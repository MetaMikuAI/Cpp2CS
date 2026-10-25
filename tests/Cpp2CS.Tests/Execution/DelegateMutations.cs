using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static partial class ExecutionCheck
{
    private static bool HasDelegateBody(MethodDefinition method) => method.Body.Instructions.Any(i => i.OpCode.Code == Code.Ldftn
        || i.OpCode.Code == Code.Callvirt && i.Operand is MethodReference { Name: "Invoke" } m && IsDelegate(m.DeclaringType));

    private static void CheckDelegateMutants(Assertions assertions, Dictionary<string, string> mutants)
    {
        if (mutants.Count == 0) return;
        var detected = mutants.Values.Count(v => v == "检出");
        var missed = mutants.Values.Count(v => v == "未检出");
        var rate = (double)detected / Math.Max(1, detected + missed);
        Console.WriteLine($"  委托方法变异：{mutants.Count} 个，检出 {detected}，未检出 {missed}，检出率 {rate:P1}");
        assertions.True(rate >= 0.95, "委托方法变异检出率至少 95%");
        assertions.True(mutants.Values.All(v => v is "检出" or "未检出"), "委托方法变异全部可比较且 IL 合法");
    }

    [MutationFamily("委托", 20)]
    private static IEnumerable<(string, Action, Action)> DelegateFamily(MutationSite site) => DelegateMutations(site.Method);

    private static IEnumerable<(string, Action, Action)> DelegateMutations(MethodDefinition method)
    {
        var il = method.Body.GetILProcessor();
        foreach (var instruction in method.Body.Instructions.ToArray())
        {
            var code = instruction.OpCode;
            var operand = instruction.Operand;
            if (code.Code == Code.Ldftn && operand is MethodReference target)
            {
                var definition = target.Resolve();
                var other = definition.DeclaringType.Methods.FirstOrDefault(m => m != definition && !m.IsConstructor && !m.HasGenericParameters
                    && m.IsStatic == definition.IsStatic && m.ReturnType.FullName == definition.ReturnType.FullName
                    && m.Parameters.Select(p => p.ParameterType.FullName).SequenceEqual(definition.Parameters.Select(p => p.ParameterType.FullName)));
                if (other is not null)
                {
                    var replacement = new MethodReference(other.Name, target.ReturnType, target.DeclaringType) { HasThis = target.HasThis };
                    foreach (var parameter in target.Parameters) replacement.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
                    yield return ($"委托换目标方法 {target.Name} → {other.Name}", () => instruction.Operand = replacement, () => instruction.Operand = operand);
                }
                if (target.HasThis)
                {
                    var extras = new[] { il.Create(OpCodes.Ldnull), il.Create(OpCodes.Ldftn, target) };
                    yield return ($"委托换绑定对象 {target.Name} → null",
                        () => Replace(OpCodes.Pop, null, extras), () => Restore(extras));
                }
            }
            if (code.Code != Code.Callvirt || operand is not MethodReference invoke || invoke.Name != "Invoke"
                || !IsDelegate(invoke.DeclaringType)) continue;
            // void 的删调用由通用变异覆盖；这里补齐有返回值的 Invoke。
            if (invoke.ReturnType.MetadataType != MetadataType.Void && Default(Concrete(invoke.ReturnType, invoke)) is { } zero)
            {
                var extras = Enumerable.Range(0, invoke.Parameters.Count).Select(_ => il.Create(OpCodes.Pop)).Concat(zero).ToArray();
                yield return ($"委托删 Invoke 调用 {invoke.FullName}", () => Replace(OpCodes.Pop, null, extras), () => Restore(extras));
            }
            if (invoke.Parameters.Count >= 2 && Concrete(invoke.Parameters[^1].ParameterType, invoke).FullName == Concrete(invoke.Parameters[^2].ParameterType, invoke).FullName)
            {
                var last = new VariableDefinition(Concrete(invoke.Parameters[^1].ParameterType, invoke));
                var previous = new VariableDefinition(Concrete(invoke.Parameters[^2].ParameterType, invoke));
                var extras = new[] { il.Create(OpCodes.Stloc, previous), il.Create(OpCodes.Ldloc, last), il.Create(OpCodes.Ldloc, previous), il.Create(code, invoke) };
                yield return ($"委托交换 Invoke 最后两个实参 {invoke.FullName}",
                    () => { method.Body.Variables.Add(last); method.Body.Variables.Add(previous); Replace(OpCodes.Stloc, last, extras); },
                    () => { Restore(extras); method.Body.Variables.Remove(previous); method.Body.Variables.Remove(last); });
            }
            void Replace(OpCode first, object? value, Instruction[] extras)
            {
                instruction.OpCode = first; instruction.Operand = value;
                var cursor = instruction;
                foreach (var extra in extras) { il.InsertAfter(cursor, extra); cursor = extra; }
            }
            void Restore(Instruction[] extras)
            {
                foreach (var extra in extras) il.Remove(extra);
                instruction.OpCode = code; instruction.Operand = operand;
            }
        }
    }

    private static TypeReference Concrete(TypeReference type, MethodReference method) => type switch
    {
        GenericParameter { Type: GenericParameterType.Type } p when method.DeclaringType is GenericInstanceType instance => instance.GenericArguments[p.Position],
        _ => type,
    };

    private static bool IsDelegate(TypeReference type)
    {
        for (var current = type.Resolve(); current is not null; current = current.BaseType?.Resolve())
            if (current.FullName == "System.MulticastDelegate") return true;
        return false;
    }

    private static Instruction[]? Default(TypeReference type) => type.MetadataType switch
    {
        MetadataType.Boolean or MetadataType.Char or MetadataType.SByte or MetadataType.Byte or MetadataType.Int16 or MetadataType.UInt16 or MetadataType.Int32 or MetadataType.UInt32 => [Instruction.Create(OpCodes.Ldc_I4_0)],
        MetadataType.Int64 or MetadataType.UInt64 => [Instruction.Create(OpCodes.Ldc_I8, 0L)],
        MetadataType.Single => [Instruction.Create(OpCodes.Ldc_R4, 0f)],
        MetadataType.Double => [Instruction.Create(OpCodes.Ldc_R8, 0d)],
        _ when !type.IsValueType => [Instruction.Create(OpCodes.Ldnull)],
        _ => null,
    };
}
