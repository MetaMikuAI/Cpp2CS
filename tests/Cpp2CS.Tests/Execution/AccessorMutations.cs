using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static partial class ExecutionCheck
{
    private static void CheckAccessorMutants(Assertions a, Dictionary<string, string> mutants)
    {
        if (mutants.Count == 0) return;
        foreach (var kind in new[] { "F9 换访问器", "F9 删认回调用" })
        {
            var group = mutants.Where(p => p.Key.Contains(kind, StringComparison.Ordinal)).ToArray();
            var detected = group.Count(p => p.Value == "检出");
            Console.WriteLine($"  {kind}：{group.Length} 个，检出 {detected}，检出率 {(double)detected / Math.Max(1, group.Length):P1}");
            a.True(group.Length > 0 && (double)detected / group.Length >= 0.95, $"{kind} 检出率至少 95%（不可比较与非法 IL 也计失败）");
        }
    }

    [MutationFamily("访问器认回", 40)]
    private static IEnumerable<(string, Action, Action)> AccessorFamily(MutationSite site) => AccessorMutations(site.Method, site.Interpreter);

    private static IEnumerable<(string, Action, Action)> AccessorMutations(MethodDefinition method, CilInterpreter interpreter)
    {
        var il = method.Body.GetILProcessor();
        foreach (var instruction in method.Body.Instructions.Where(interpreter.IsAccessorCall).ToArray())
        {
            var code = instruction.OpCode;
            var target = (MethodReference)instruction.Operand;
            // 替换目标只能来自本次认回得到的透明集合，不能为测试临时扩大集合或改成普通调用桩。
            var other = interpreter.TransparentAccessors.Values.FirstOrDefault(m => m.FullName != target.FullName
                && m.DeclaringType.FullName == target.DeclaringType.FullName && m.HasThis == target.HasThis
                && m.ReturnType.FullName == target.ReturnType.FullName
                && m.Parameters.Select(p => p.ParameterType.FullName).SequenceEqual(target.Parameters.Select(p => p.ParameterType.FullName)));
            if (other is not null)
            {
                var replacement = new MethodReference(other.Name, target.ReturnType, target.DeclaringType) { HasThis = target.HasThis };
                foreach (var parameter in target.Parameters) replacement.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
                yield return ($"F9 换访问器 #{method.Body.Instructions.IndexOf(instruction)} {target.Name} → {other.Name}",
                    () => instruction.Operand = replacement, () => instruction.Operand = target);
            }
            var returnType = target.ReturnType.Resolve() is { IsEnum: true } enumeration
                ? enumeration.Fields.Single(f => f.Name == "value__").FieldType : target.ReturnType;
            var zero = returnType.MetadataType == MetadataType.Void ? [] : Default(returnType);
            if (zero is null) continue;
            var pops = target.Parameters.Count + (target.HasThis ? 1 : 0);
            var extras = Enumerable.Range(0, Math.Max(0, pops - 1)).Select(_ => il.Create(OpCodes.Pop)).Concat(zero).ToArray();
            yield return ($"F9 删认回调用 #{method.Body.Instructions.IndexOf(instruction)} {target.Name}",
                () =>
                {
                    instruction.OpCode = pops > 0 ? OpCodes.Pop : OpCodes.Nop;
                    instruction.Operand = null;
                    var cursor = instruction;
                    foreach (var extra in extras) { il.InsertAfter(cursor, extra); cursor = extra; }
                },
                () =>
                {
                    foreach (var extra in extras) il.Remove(extra);
                    instruction.OpCode = code;
                    instruction.Operand = target;
                });
        }
    }
}
