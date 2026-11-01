using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Calls;

/// <summary>
/// 分派解析：虚调用按接收者的静态类型与虚表槽号确定声明方法，接口调用按接口与槽号，委托调用取 Invoke。
/// 解析结果记在调用上（<see cref="Call.Resolved"/>），之后的内存效果与下降按该方法的机器签名进行。
/// 在内存提升之前运行，使用未提升内存的符号值。
/// </summary>
internal static class DispatchResolution
{
    public static int Run(MachineFunction function, ValueModel values, TypeOracle oracle)
    {
        var resolved = 0;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: { } op, Resolved: null } call) continue;
                MethodRef? method = op switch
                {
                    { Kind: OpKind.CallDelegate, Operand: MethodRef invoke } => invoke,
                    { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> { Item1: DefinitionRef itf } pair } => Slot(itf, pair.Item2, interfaceOnly: true),
                    { Kind: OpKind.CallVirtual, Operand: int slot } when Receiver(call, values) is { } receiver && oracle.TypeOf(receiver) is DefinitionRef owner => Slot(owner, slot, interfaceOnly: false),
                    _ => null,
                };
                if (method is null) continue;
                block.Statements[i] = call with { Resolved = method };
                resolved++;
            }
        return resolved;
    }

    private static Sym? Receiver(Call call, ValueModel values)
    {
        var position = Array.IndexOf(call.Sources, Storage.Gpr(0));
        return position < 0 ? null : values.Operands(call)[1 + position];
    }

    /// <summary>类型（沿基类链）中占据虚表槽 slot 的虚方法，类型实参代入声明类型。</summary>
    private static MethodRef? Slot(DefinitionRef type, int slot, bool interfaceOnly)
    {
        for (TypeRef? current = type; current is DefinitionRef d; current = interfaceOnly ? null : d.Definition.BaseType?.Substitute(d.Arguments, []))
            if (d.Definition.Methods.FirstOrDefault(m => m.IsVirtual && m.Slot == slot && m.GenericParameters.Count == 0) is { } method)
                return new MethodRef(method, d.Arguments, []);
        return null;
    }
}
