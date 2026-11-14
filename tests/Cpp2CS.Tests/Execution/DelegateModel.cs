using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>按委托签名合成单播输入。</summary>
[ShapeModel("委托", Basis = "ECMA-335 第 II 部分 14.6 节的委托语义")]
internal static class DelegateModel
{
    public static MethodRef? Invoke(TypeRef type)
    {
        if (type is not DefinitionRef d) return null;
        for (TypeRef? current = d; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, []))
            if (c.Definition.FullName == "System.MulticastDelegate")
                return d.Definition.Methods.SingleOrDefault(m => m.Name == "Invoke" && !m.IsStatic) is { } method ? new(method, d.Arguments, []) : null;
        return null;
    }

    public static bool IsInvoke(MethodRef method) => method.Method.Name == "Invoke" && Invoke(method.DeclaringType)?.Equals(method) == true;
    public static string Signature(MethodRef method) => string.Join("|", method.Method.Parameters.Select(p => p.Type.Substitute(method.TypeArguments, method.MethodArguments)).Prepend(method.Method.ReturnType.Substitute(method.TypeArguments, method.MethodArguments)));
    public static void Event(Side side, ulong receiver, IEnumerable<ulong> arguments)
    {
        side.Event($"delegate 0x{receiver:x}({string.Join(", ", arguments.Select(a => $"0x{a:x}"))})", TraceEventKind.Call);
        side.PlannedCall();
    }
}

internal sealed record DelegateInput(ulong Receiver, ulong Trap, MethodRef Invoke, MethodRef Method, ulong Target);

internal sealed partial class World
{
    private readonly Dictionary<ulong, DelegateInput> delegateTraps = [];
    private readonly Dictionary<ulong, DelegateInput> delegateInputs = [];
    public DelegateInput? DelegateAtTrap(ulong trap) => delegateTraps.GetValueOrDefault(trap);
    public DelegateInput? DelegateAt(ulong receiver) => delegateInputs.GetValueOrDefault(receiver);

    private ulong DelegateInstance(DefinitionRef type, MethodRef invoke, string key, int depth)
    {
        var layout = Layouts.Of(type) ?? throw new Unsupported($"委托 {type} 没有布局");
        var address = Reserve(layout.InstanceSize, 8);
        Put64(address, Klass(type));
        // 输入回调是不展开的运行时边界：用具体 Invoke 描述签名，闭合实例字段指向同一合成对象。
        // 不要求程序中恰好存在同签名的用户回调，否则未调用的委托字段也会使整个输入图不可合成。
        var method = invoke;
        var target = address;
        var trap = CodeBase + 0x80000 + (ulong)delegateTraps.Count * 4;
        if (trap >= CodeBase + CodeSize) throw new Unsupported("委托陷阱区已满");
        var binding = new DelegateInput(address, trap, invoke, method, target);
        delegateTraps.Add(trap, binding);
        delegateInputs.Add(address, binding);
        return address;
    }
}

internal sealed partial class CilInterpreter
{
    private StackValue? InvokeDelegate(CilSide side, MethodRef invoke, StackValue[] values)
    {
        if (side.World.DelegateAt(values[0].Bits) is null) throw new Unsupported("委托调用接收者不是合成的单播输入");
        var ordinal = side.NextCall();
        side.Callees.Add(invoke);
        var types = ManagedValues.ArgumentTypes(invoke);
        DelegateModel.Event(side, values[0].Bits, index.ManagedValues.ObservableArguments(side, invoke, types,
            types.Select((type, i) => ToBytes(type, values[i])).ToArray()).Skip(1));
        var returnType = invoke.Method.ReturnType.Substitute(invoke.TypeArguments, invoke.MethodArguments);
        return !ManagedTypes.IsVoid(returnType) ? FromBytes(returnType, side.World.ReturnBytes(ordinal, returnType)) : null;
    }
}
