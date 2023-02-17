using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;
using Microsoft.Extensions.Logging;

namespace Jitting
{
    public static class Jitter
    {
        private const int TypeSamplesLimit = 100;

        /// <summary>
        /// Loads all assemblies references by application into memory and forces JIT compilation for
        /// all assemblies that satisfy assembliesToJitFilter filter.
        /// Tries to JIT generic methods as well, by finding types satisfying the generic constraints.
        /// Will skip jitting for methods where generic constraints cannot be satisfied.
        /// </summary>
        /// <param name="assembliesToJitFilter">Limits jitting to assemblies that satisfy this predicate.</param>
        /// <param name="throwOnError">If true, exception will be shown if any of the methods fail while jitting.</param>
        /// <param name="logger">Optional logger to write jitting summary to.</param>
        public static void RunJitting(Func<Assembly, bool> assembliesToJitFilter, bool throwOnError = true, ILogger? logger = null)
        {
            var assemblies = AppDomain.CurrentDomain.GetAssemblies();
            var set = new HashSet<Assembly>(assemblies);
            foreach (var a in assemblies)
            {
                ForceLoadAll(a, set);
            }

            var types = assemblies.Where(p => !p.FullName.Contains("CoreLib")).SelectMany(GetAllRelevantTypes).ToArray();
            var generics = FindGenerics(types);
            
            var relevantAssemblies = set.Where(assembliesToJitFilter).ToArray();
            logger?.LogInformation($"Jitting {relevantAssemblies.Length} assemblies...");
            var results = new List<JitResult>();
            foreach (var asm in relevantAssemblies)
            {
                var res = PreJitMethods(asm, types, generics, logger);
                results.AddRange(res.ToArray());
            }

            FinalizeResults(results, logger, throwOnError);
        }

        private static void FinalizeResults(List<JitResult> results, ILogger? logger, bool throwOnerror)
        {
            var counts = results.GroupBy(p => p.Outcome).ToDictionary(p => p.Key, p => p.Count());
            counts.TryGetValue(JitOutcome.Fail, out var fail);
            counts.TryGetValue(JitOutcome.Success, out var success);
            counts.TryGetValue(JitOutcome.Skip, out var skip);

            var logLevel = fail > 0 ? LogLevel.Error : skip > 0 ? LogLevel.Warning : LogLevel.Information;
          
            logger?.Log(logLevel, $"Jitting completed! {success} methods jitted successfully, {fail} failures, {skip} skipped");

            if (fail > 0 && throwOnerror)
            {
                throw new InvalidOperationException($"JIT failed for {fail} methods");
            }
        }

        private static JitResult[] PreJitMethods(
            Assembly assembly,
            Type[] allTypes,
            Dictionary<Type, List<Type>> genericImplementations,
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
                    if (curMethod.IsAbstract || curMethod.Name.Contains("RuntimeMethodInfo"))
                        continue;

                    var result = JitMethod(curMethod, allTypes, genericImplementations);
                    res.Add(result);
                }
            }

            var errors = res.Where(p => p.Outcome == JitOutcome.Fail).ToArray();
            var i = 0;
            if (errors.Any())
            {
                var sb = new StringBuilder();
                sb.AppendLine($"FAILURES IN ASSEMBLY: {assembly.GetName().Name}");
                foreach (var outcome in errors.OrderBy(p => p.MethodInfo.DeclaringType!.Name).ThenBy(p => p.MethodInfo.Name))
                {
                    sb.AppendLine($"\t{++i}. {outcome.MethodInfo.DeclaringType}.{outcome.MethodInfo.Name}: {outcome.Exception?.Message}");
                }

                logger?.LogError(sb.ToString());
            }

            return res.ToArray();
        }

        private static JitResult JitMethod(
            MethodInfo method,
            Type[] allTypes, Dictionary<Type, List<Type>> genericImplementations)
        {
            try
            {
                if (method.ContainsGenericParameters)
                {
                    Type[]? substitutes;
                    try
                    {
                        substitutes = GetGenericArgumentSubstitutes(method, allTypes, genericImplementations);
                    }
                    catch (SkipJittingException)
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

        private static Type[] GetGenericArgumentSubstitutes(MethodInfo curMethod, Type[] allTypes, Dictionary<Type, List<Type>> genericImplementations)
        {
            var declaringType = curMethod.DeclaringType;
            var typeParameters = declaringType!.GetGenericArguments();
            var typeSubstitutes = GetSubstitutes(typeParameters, allTypes, genericImplementations);

            var methodParameters = curMethod.GetGenericArguments();
            var methodSubstitutes = GetSubstitutes(methodParameters, allTypes, genericImplementations);

            return typeSubstitutes.Concat(methodSubstitutes).ToArray();
        }

        // ReSharper disable once CognitiveComplexity
        private static Type[] GetSubstitutes(Type[] genericParams, Type[] allTypes, Dictionary<Type, List<Type>> genericImplementations)
        {
            var mapping = new Dictionary<Type, Type[]>();
            var paramsToProcess = new List<Type>(genericParams);
            var processedInOrder = new List<Type>();

            while (paramsToProcess.Any())
            {
                var selfReferential = false;
                var firstToProcess = paramsToProcess.FirstOrDefault(p =>
                    p.GetGenericParameterConstraints().All(x =>
                        x.GetGenericArguments().All(a =>
                        {
                            if (a == p)
                            {
                                selfReferential = true;
                                return true;
                            }

                            return mapping.ContainsKey(a) || !genericParams.Contains(a);
                        })));
                if (selfReferential)
                {
                    throw new SkipJittingException("Self-referential template constraints not supported");
                }

                if (firstToProcess == null)
                {
                    throw new SkipJittingException("Unable to map substitutes.");
                }

                var satisfyingTypes = GetSatisfyingTypes(firstToProcess, mapping, allTypes, genericImplementations).Take(TypeSamplesLimit).ToArray();
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

        private static IEnumerable<Type> GetSatisfyingTypes(Type genericParam, Dictionary<Type, Type[]> mapping, Type[] allTypes, Dictionary<Type, List<Type>> genericImplementations)
        {
            var typeConstraints = genericParam.GetGenericParameterConstraints().Where(p => p != typeof(ValueType)).ToArray();
            var a = genericParam.GenericParameterAttributes;

            var types = GetSatisfyingTypeConstraints(typeConstraints, mapping, allTypes, genericImplementations);

            types = types.Where(p => IsSatisfyingAttributes(a, p));

            return types;
        }

        private static IEnumerable<Type> GetSatisfyingTypeConstraints(Type[] constraint, Dictionary<Type, Type[]> mapping, Type[] allTypes, Dictionary<Type, List<Type>> genericImplementations)
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
                    if (c.IsGenericType)
                    {
                        var generic = c.GetGenericTypeDefinition();
                        var implementing = genericImplementations[generic];
                        res = res.Intersect(implementing);
                    }
                
                    var constraintTypes = GetActualConstraintTypes(c, mapping);

                    res = res.Where(p => constraintTypes.Any(cc => cc.IsAssignableFrom(p)));
                }
            }

            return res;
        }

        private static IEnumerable<Type> GetActualConstraintTypes(Type constraintType, Dictionary<Type, Type[]> genericMapping)
        {
            if (constraintType.IsGenericType)
            {
                var @params = constraintType.GetGenericArguments();
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
                if (!t.IsValueType || IsNullable(t))
                {
                    return false;
                }
            }

            else if ((genericParameterAttributes & GenericParameterAttributes.DefaultConstructorConstraint)
                     == GenericParameterAttributes
                         .DefaultConstructorConstraint)
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
            HashSet<Assembly> loadedAssemblies)
        {
            var alreadyLoaded = !loadedAssemblies.Add(assembly);
            if (alreadyLoaded)
                return;

            var referencedAssemblies = assembly.GetReferencedAssemblies();

            foreach (var curAssemblyName in referencedAssemblies)
            {
                var nextAssembly = Assembly.Load(curAssemblyName);
                if (nextAssembly.GlobalAssemblyCache)
                    continue;

                ForceLoadAll(nextAssembly, loadedAssemblies);
            }
        }

        private static Dictionary<Type, List<Type>> FindGenerics(Type[] types)
        {
            Dictionary<Type, List<Type>> ret = new Dictionary<Type, List<Type>>();
            foreach (var t in types)
            {
                Type? b = t;
                while (b != null)
                {
                    if (b.IsGenericType)
                    {
                        var gen = b.GetGenericTypeDefinition();
                        if (!ret.ContainsKey(gen))
                        {
                            ret.Add(gen, new List<Type>());
                        }
                        ret[gen].Add(t);
                    }

                    b = b.BaseType;
                }

                var ints = t.GetInterfaces().Where(p => p.IsGenericType);
                foreach (var i in ints)
                {
                    var gen = i.GetGenericTypeDefinition();
                    if (!ret.ContainsKey(gen))
                    {
                        ret.Add(gen, new List<Type>());
                    }
                    ret[gen].Add(t);
                }
            }

            return ret;
        }

        private class SkipJittingException:Exception
        {
            public SkipJittingException(string message) : base(message)
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

        private enum JitOutcome
        {
            Fail = 0,
            Skip = 1,
            Success = 2
        }
    }
}
