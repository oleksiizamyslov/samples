using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;
using Microsoft.Extensions.Logging;

namespace Jitter
{
    public class Jitter
    {
        private const int TypeSamplesLimit = 100;

        /// <summary>
        /// Loads all assemblies references by application into memory and forces JIT compilation for
        /// all assemblies that satisfy assembliesToJitFilter filter.
        /// Tries to JIT generic methods as well, by finding types satisfying the generic constraints.
        /// Will skip jitting for methods where generic constraints cannot be satisfied.
        ///
        /// Jitting of generic methods with some complex constraints is not yet supported, such methods will be skipped.
        /// </summary>
        /// <param name="assembliesToJitFilter">Limits jitting to assemblies that satisfy this predicate</param>
        /// <param name="throwOnError">If true, exception will be thrown when jitting fails for any of the methods</param>
        /// <param name="logger">Optional logger to write jitting summary to</param>
        public static void RunJitting(Func<Assembly, bool> assembliesToJitFilter, ILogger? logger = null, bool throwOnError = true)
        {
            logger?.LogInformation($"Loading assemblies into memory...");

            var sw = Stopwatch.StartNew();
            var initialAssemblies = AppDomain.CurrentDomain.GetAssemblies();
            var set = new HashSet<Assembly>(initialAssemblies);
            var failedAsms = new HashSet<(Assembly, AssemblyName)>();
            foreach (var asm in initialAssemblies)
            {
                ForceLoadAll(asm, failedAsms, set);
            }

            var assemblies = AppDomain.CurrentDomain.GetAssemblies();
            
            logger?.LogInformation($"{assemblies.Length} assemblies loaded total.");

            var types = assemblies.Where(p => !p.FullName.Contains("CoreLib")).SelectMany(GetAllRelevantTypes).ToArray();
            var generics = GetGenericsData(types);
            var relevantAssemblies = assemblies.Where(assembliesToJitFilter).ToArray();

            logger?.LogInformation($"Jitting {relevantAssemblies.Length} assemblies...");
            var results = new List<JitResult>();
            foreach (var asm in relevantAssemblies)
            {
                var res = PreJitMethods(asm, types, generics, logger);
                results.AddRange(res.ToArray());
            }

            sw.Stop();
            FinalizeResults(sw.Elapsed, results, failedAsms, logger, throwOnError);
        }

        private static void FinalizeResults(
            TimeSpan swElapsed,
            List<JitResult> results,
            HashSet<(Assembly, AssemblyName)> failedAssemblies,
            ILogger? logger,
            bool throwOnerror)
        {
            var counts = results.GroupBy(p => p.Outcome).ToDictionary(p => p.Key, p => p.Count());
            counts.TryGetValue(JitOutcome.Fail, out var fail);
            counts.TryGetValue(JitOutcome.Success, out var success);
            counts.TryGetValue(JitOutcome.Skip, out var skip);

            if (fail > 0 || failedAssemblies.Any())
            {
                logger?.LogError($"Jitting completed in {swElapsed.TotalSeconds} seconds. {success} methods jitted successfully, {fail} failures, {skip} skipped, {failedAssemblies.Count} assemblies failed to load.");
            }
            else if (skip > 0)
            {
                logger?.LogInformation($"Jitting completed in {swElapsed.TotalSeconds} seconds! {success} methods jitted successfully, {skip} skipped");
            }
            
            var assemblyErrors = new StringBuilder();
            if (failedAssemblies.Any())
            {
                foreach (var asmName in failedAssemblies)
                {
                    var error = $"{asmName.Item2} failed to load (referenced by {asmName.Item1.FullName}).";
                    logger?.LogError(error);
                    assemblyErrors.AppendLine(error);
                }
            }

            if ((failedAssemblies.Any() || fail > 0) && throwOnerror)
            {
                var finalErrors = new StringBuilder();
                if (fail > 0)
                {
                    finalErrors.AppendLine($"JIT failed for {fail} methods, {failedAssemblies.Count} assemblies failed to load");
                }

                finalErrors.AppendLine(assemblyErrors.ToString());
                var i = 0;
                foreach (var error in results.Where(p => p.Outcome == JitOutcome.Fail))
                {
                    finalErrors.AppendLine($"{++i}. {error.MethodInfo.DeclaringType}.{error.MethodInfo.Name}: {error.Exception?.Message}");
                }
                throw new InvalidOperationException(finalErrors.ToString());
            }
        }

        // ReSharper disable once CognitiveComplexity
        private static JitResult[] PreJitMethods(
            Assembly assembly,
            Type[] allTypes,
            GenericsData genericsData,
            ILogger? logger)
        {
            List<JitResult> res = new List<JitResult>();
            Type[] types = GetAllRelevantTypes(assembly);

            foreach (Type curType in types)
            {
                MethodInfo[] methods = curType.GetMethods(
                    BindingFlags.DeclaredOnly | BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static);

                foreach (MethodInfo curMethod in methods)
                {
                    if (curMethod.IsAbstract)
                        continue;
                    if ((curMethod.Attributes & MethodAttributes.PinvokeImpl) == MethodAttributes.PinvokeImpl)
                        continue;

                    var result = JitMethod(curMethod, allTypes, genericsData);
                    res.Add(result);
                }
            }

            var errors = res.Where(p => p.Outcome == JitOutcome.Fail).ToArray();
            var i = 0;
            if (errors.Any())
            {
                var sb = new StringBuilder();
                sb.AppendLine($"JITTING FAILURES IN ASSEMBLY: {assembly.GetName().Name}");
                foreach (var outcome in errors.OrderBy(p => p.MethodInfo.DeclaringType!.Name).ThenBy(p => p.MethodInfo.Name))
                {
                    sb.AppendLine($"\t{++i}. {outcome.MethodInfo.DeclaringType}.{outcome.MethodInfo.Name}: {outcome.Exception?.Message}");
                }

                logger?.LogError(sb.ToString());
            }

            return res.ToArray();
        }

        private static JitResult JitMethod(MethodInfo method, Type[] allTypes, GenericsData genericsData)
        {
            try
            {
                if (method.ContainsGenericParameters)
                {
                    Type[]? substitutes;
                    try
                    {
                        substitutes = GetGenericArgumentSubstitutes(method, allTypes, genericsData);
                    }
                    catch
                    {
                        return new JitResult(JitOutcome.Skip, method);
                    }

                    RuntimeHelpers.PrepareMethod(method.MethodHandle, substitutes.Select(p => p.TypeHandle).ToArray());
                }
                else
                {
                    RuntimeHelpers.PrepareMethod(method.MethodHandle);
                }
            }
            catch (PlatformNotSupportedException)
            {
                // This is normal for some methods, apparently..
            }
            catch (Exception ex)
            {
                return new JitResult(JitOutcome.Fail, method, ex);
            }

            return new JitResult(JitOutcome.Success, method);
        }

        private static Type[] GetGenericArgumentSubstitutes(MethodInfo curMethod, Type[] allTypes, GenericsData genericImplementations)
        {
            var declaringType = curMethod.DeclaringType;
            var typeParameters = declaringType!.GetGenericArguments();
            var typeSubstitutes = GetSubstitutes(typeParameters, allTypes, genericImplementations);

            var methodParameters = curMethod.GetGenericArguments();
            var methodSubstitutes = GetSubstitutes(methodParameters, allTypes, genericImplementations);

            return typeSubstitutes.Concat(methodSubstitutes).ToArray();
        }

        // ReSharper disable once CognitiveComplexity
        private static Type[] GetSubstitutes(Type[] genericParams, Type[] allTypes, GenericsData genericImplementations)
        {
            var mapping = new Dictionary<Type, Type[]>();
            var paramsToProcess = new List<Type>(genericParams);
            var processedInOrder = new List<Type>();

            while (paramsToProcess.Any())
            {
                var selfReferential = false;
                var firstToProcess = paramsToProcess.FirstOrDefault(p => p.GetGenericParameterConstraints().All(x => x.GetGenericArguments().All(a =>
                {
                    if (a == p)
                    {
                        selfReferential = true;
                        return true;
                    }

                    return mapping.ContainsKey(a) || !genericParams.Contains(a);
                })));

                if (firstToProcess == null)
                {
                    throw new SkipJittingException("Unable to map substitutes.");
                }

                Type[] satisfyingTypes = GetSatisfyingTypes(firstToProcess, mapping, allTypes, genericImplementations, selfReferential)
                    .Take(TypeSamplesLimit).ToArray();
                if (satisfyingTypes.Length == 0)
                {
                    throw new SkipJittingException($"Cannot find satisfying type for generic parameter {firstToProcess.Name}.");
                }

                mapping.Add(firstToProcess, satisfyingTypes.ToArray());
                paramsToProcess.Remove(firstToProcess);
                processedInOrder.Add(firstToProcess);
            }

            var ret = FinalizeSubstitutes(genericParams, processedInOrder, mapping);
            return ret;
        }

        private static IEnumerable<Type> GetSatisfyingTypes(
            Type genericParam,
            Dictionary<Type, Type[]> mapping,
            Type[] allTypes,
            GenericsData genericsData,
            bool selfReferential)
        {
            var typeConstraints = genericParam.GetGenericParameterConstraints().Where(p => p != typeof(ValueType)).ToArray();
            var a = genericParam.GenericParameterAttributes;

            var types = GetSatisfyingTypeConstraints(typeConstraints, mapping, allTypes, genericsData, selfReferential);

            types = types.Where(p => IsSatisfyingAttributes(a, p));

            return types;
        }

        private static IEnumerable<Type> GetSatisfyingTypeConstraints(
            Type[] constraint,
            Dictionary<Type, Type[]> mapping,
            Type[] allTypes,
            GenericsData genericsData,
            bool isSelfReferential)
        {
            IEnumerable<Type> res = allTypes.Where(p => !p.IsGenericType);
            foreach (var c in constraint)
            {
                if (mapping.ContainsKey(c))
                {
                    res = res.Intersect(mapping[c]);
                }
                else
                {
                    if (c.IsGenericType && !isSelfReferential)
                    {
                        var generic = c.GetGenericTypeDefinition();
                        
                        genericsData.GenericsImplementations.TryGetValue(generic, out var implementing);
                        res = res.Intersect(implementing ?? new List<Type>());
                    }

                    var constraintTypes = GetActualConstraintTypes(c, mapping, genericsData, isSelfReferential);

                    res = res.Where(p => constraintTypes.Any(cc => cc.IsAssignableFrom(p)));
                }
            }

            return res;
        }

        private static IEnumerable<Type> GetActualConstraintTypes(
            Type constraintType,
            Dictionary<Type, Type[]> genericMapping,
            GenericsData genericsData,
            bool isSelfReferential)
        {
            if (constraintType.IsGenericType)
            {
                var @params = constraintType.GetGenericArguments();

                if (isSelfReferential)
                {
                    var genDef = constraintType.GetGenericTypeDefinition();
                    if (@params.Length == 1
                        && genericsData.SelfReferentials.ContainsKey(genDef))
                    {
                        return genericsData.SelfReferentials[genDef];
                    }

                    throw new SkipJittingException("Complex self-referential constraints not yet supported");
                }

                var substitutes = @params.Select(p => genericMapping.ContainsKey(p)
                    ? genericMapping[p]
                    : new[] { p }).ToArray();
                var @base = constraintType.GetGenericTypeDefinition();
                return CrossJoin(@base, substitutes);
            }

            return new[] { constraintType };
        }

        // ReSharper disable once CognitiveComplexity
        private static bool IsSatisfyingAttributes(GenericParameterAttributes genericParameterAttributes, Type t)
        {
            if ((genericParameterAttributes & GenericParameterAttributes.ReferenceTypeConstraint) == GenericParameterAttributes.ReferenceTypeConstraint)
            {
                if (!t.IsClass && !t.IsInterface)
                {
                    return false;
                }
            }

            if ((genericParameterAttributes & GenericParameterAttributes.NotNullableValueTypeConstraint) == GenericParameterAttributes.NotNullableValueTypeConstraint)
            {
                if (!t.IsValueType
                    || IsNullable(t))
                {
                    return false;
                }
            }

            else if ((genericParameterAttributes & GenericParameterAttributes.DefaultConstructorConstraint)
                     == GenericParameterAttributes.DefaultConstructorConstraint)
            {
                if (t.GetConstructor(Type.EmptyTypes) == null
                    && !t.IsValueType)
                {
                    return false;
                }
            }

            return true;
        }

        private static Type[] FinalizeSubstitutes(Type[] genericParams, List<Type> processedInOrder, Dictionary<Type, Type[]> mapping)
        {
            var finalizedMapping = new Dictionary<Type, Type>();

            foreach (var parameter in processedInOrder)
            {
                var substitute = mapping[parameter];
                finalizedMapping[parameter] = substitute[0];

                var constraints = parameter.GetGenericParameterConstraints();

                ApplyResolvedConstraints(constraints, substitute[0], finalizedMapping);
            }

            var selectedSubstitutes = genericParams.Select(p => finalizedMapping[p]).ToArray();
            return selectedSubstitutes;
        }

        private static void ApplyResolvedConstraints(Type[] constraints, Type substitute, Dictionary<Type, Type> finalizedMapping)
        {
            foreach (var c in constraints)
            {
                if (c.IsGenericType)
                {
                    var argumentNames = c.GetGenericArguments();
                    if (argumentNames.Length == 0)
                    {
                        continue;
                    }

                    var genericDefinition = c.GetGenericTypeDefinition();
                    Type[] resolvedArguments;
                    if (genericDefinition.IsInterface)
                    {
                        var implementation = substitute.GetInterfaces().First(p => p.IsGenericType && p.GetGenericTypeDefinition() == genericDefinition);
                        resolvedArguments = implementation.GetGenericArguments();
                    }
                    else
                    {
                        var implementation = substitute;
                        while (!implementation.IsGenericType
                               || implementation.GetGenericTypeDefinition() != genericDefinition)
                        {
                            implementation = implementation.BaseType!;
                        }

                        resolvedArguments = implementation.GetGenericArguments();
                    }

                    for (var i = 0; i < argumentNames.Length; ++i)
                    {
                        finalizedMapping[argumentNames[i]] = resolvedArguments[i];
                    }
                }
            }
        }

        // ReSharper disable once UnusedParameter.Local
        private static bool IsNullable<T>(T value)
        {
            return Nullable.GetUnderlyingType(typeof(T)) != null;
        }

        private static IEnumerable<Type> CrossJoin(Type @base, Type[][] substitutes)
        {
            var indices = substitutes.Select(_ => 0).ToArray();
            var maxIndices = substitutes.Select(p => p.Length - 1).ToArray();
            yield return @base.MakeGenericType(substitutes.Select((p, i) => p[indices[i]]).ToArray());
            while (Increment(indices, maxIndices))
            {
                yield return @base.MakeGenericType(substitutes.Select((p, i) => p[indices[i]]).ToArray());
            }
        }

        private static bool Increment(int[] indices, int[] maxIndices)
        {
            for (var i = indices.Length - 1; i >= 0; --i)
            {
                var max = maxIndices[i];
                if (indices[i] < max)
                {
                    indices[i]++;
                    for (var j = i + 1; j < indices.Length; ++j)
                    {
                        indices[j] = 0;
                    }

                    return true;
                }
            }

            return false;
        }

        private static Type[] GetAllRelevantTypes(Assembly assembly)
        {
            var types = assembly.GetTypes().ToArray();

            return types;
        }

        private static void ForceLoadAll(
            Assembly assembly,
            HashSet<(Assembly, AssemblyName)> failedLoadAssemblies,
            HashSet<Assembly> loadedAssemblies)
        {
            if (assembly.FullName.StartsWith("mscorlib,")
                || assembly.FullName.StartsWith("System,")
                || assembly.FullName.StartsWith("System.Data,"))
            {
                return;
            }

            var referencedAssemblies = assembly.GetReferencedAssemblies();

            foreach (var refAssemblyName in referencedAssemblies)
            {
                Assembly? refAssembly;
                try
                {
                    refAssembly = Assembly.Load(refAssemblyName);
                }
                catch
                {
                    failedLoadAssemblies.Add((assembly, refAssemblyName));
                    continue;
                }

                var alreadyLoaded = !loadedAssemblies.Add(refAssembly);
                if (alreadyLoaded)
                    continue;
                loadedAssemblies.Add(refAssembly);

                if (refAssembly.GlobalAssemblyCache)
                    continue;

                ForceLoadAll(refAssembly, failedLoadAssemblies, loadedAssemblies);
            }
        }

        private static GenericsData GetGenericsData(Type[] types)
        {
            var generics = new Dictionary<Type, List<Type>>();
            var selfReferentials = new Dictionary<Type, List<Type>>();

            foreach (var t in types)
            {
                var genericImplementations = GetImplementations(t).Where(p => p.IsGenericType).ToArray();

                foreach (var g in genericImplementations)
                {
                    var gen = g.GetGenericTypeDefinition();
                    if (gen == g)
                    {
                        continue;
                    }

                    if (!generics.ContainsKey(gen))
                    {
                        generics.Add(gen, new List<Type>());
                    }

                    generics[gen].Add(t);

                    if (gen.Name.Contains("IComparable"))
                    {
                        
                    }
                    
                    var @p = g.GetGenericArguments();
                    var isSelfReferential = @p.Length == 1 && p[0] == t;
                    if (isSelfReferential)
                    {
                        if (!selfReferentials.ContainsKey(gen))
                        {
                            selfReferentials.Add(gen, new List<Type>());
                        }

                        selfReferentials[gen].Add(t);
                    }
                }
            }

            return new GenericsData(generics, selfReferentials);
        }

        private static IEnumerable<Type> GetImplementations(Type type)
        {
            foreach (var i in type.GetInterfaces())
            {
                yield return i;
            }

            var currentBaseType = type;
            while (currentBaseType != null)
            {
                yield return currentBaseType;
                currentBaseType = currentBaseType.BaseType;
            }
        }

        private class SkipJittingException : Exception
        {
            public SkipJittingException(string message)
                : base(message)
            {
            }
        }

        private class JitResult
        {
            public JitResult(JitOutcome outcome, MethodInfo methodInfo, Exception? exception = null)
            {
                Outcome = outcome;
                MethodInfo = methodInfo;
                Exception = exception;
            }

            public JitOutcome Outcome { get; }
            public MethodInfo MethodInfo { get; }
            public Exception? Exception { get; }
        }

        private class GenericsData
        {
            public GenericsData(Dictionary<Type, List<Type>> genericsImplementations, Dictionary<Type, List<Type>> selfReferentials)
            {
                GenericsImplementations = genericsImplementations;
                SelfReferentials = selfReferentials;
            }

            public Dictionary<Type, List<Type>> GenericsImplementations { get; }
            public Dictionary<Type, List<Type>> SelfReferentials { get; }
        }

        private enum JitOutcome
        {
            Fail = 0,
            Skip = 1,
            Success = 2
        }
    }
}
