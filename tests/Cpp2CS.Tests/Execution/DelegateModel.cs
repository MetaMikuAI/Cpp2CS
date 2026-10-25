using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

/// <summary>按 libil2cpp 的委托布局合成单播输入。</summary>
[ShapeModel("委托", Basis = "libil2cpp 委托对象的运行时结构与 Invoke 分派（运行时源码）；ECMA-335 第 II 部分 14.6 节的委托语义；delegate-constructors 入口检查")]
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
        side.Event($"delegate 0x{receiver:x}({string.Join(", ", arguments.Select(a => $"0x{a:x}"))})");
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
        Put64(address + 0x10, Index.CodeAddress(method));
        Put64(address + 0x18, trap);
        Put64(address + 0x20, target);
        Put64(address + 0x28, MethodInfo(method));
        Put64(address + 0x40, method.Method.IsStatic ? address : target);
        // +0x78 的多播列表保持 null。陷阱替代适配器/目标执行，保留其 ABI 和接收者身份。
        return address;
    }
}

internal sealed partial class NativeMachine
{
    private MethodRef? DelegateConstructorInstance(MethodRef callee, ulong receiver)
    {
        if (callee.Method.Name != ".ctor" || DelegateModel.Invoke(callee.DeclaringType) is null) return null;
        // delegate-constructors 检查构造入口是否读取隐藏 MethodInfo。
        // ctor 的具体类型由真实接收者 klass 决定；第三实参的目标 MethodInfo 仍按原值比较，不能省略。
        // 复现：Cpp2CS.Tests delegate-constructors <binary> <metadata> <output.tsv>。
        if (side.TypeOf(receiver) is not DefinitionRef type || type.Definition != callee.Method.Owner)
            throw new Unsupported($"委托构造 {callee} 的接收者类型与构造入口不一致");
        return callee with { TypeArguments = type.Arguments };
    }

    private void CallDelegate(DelegateInput binding)
    {
        var world = side.World;
        var signature = world.Index.StructAbi.Signature(binding.Invoke);
        if (signature.Parameters.Any(a => a.Indirect || a.StackOffset is not null)
            || signature.MethodInfo.StackOffset is not null || signature.Return is { } r && (r.Indirect || r.StackOffset is not null || r.Pieces.Length != 1))
            throw new Unsupported("委托间接/栈上传参或聚合返回尚未建模");
        if (uc.Reg(Unicorn.X(0)) != (binding.Method.Method.IsStatic ? binding.Receiver : binding.Target)
            || StructAbi.Bits(ReadLocation(signature.MethodInfo)) != world.MethodInfo(binding.Method))
            throw new InvalidOperationException("委托陷阱收到的 method_code/method 与合成输入不一致");
        var ordinal = side.NextCall();
        // Invoke 仍是单播边界；聚合实参按 AAPCS64 独立位置读取，按 ECMA 值字段记录，不能把填充当整数比较。
        var parameterTypes = StructAbi.ArgumentTypes(binding.Invoke).Skip(1).ToArray();
        DelegateModel.Event(side, binding.Receiver, signature.Parameters.SelectMany((a, i) =>
            world.Index.StructAbi.ObservableArgument(side, parameterTypes[i], ReadLocation(a))));
        if (signature.Return is { } result)
        {
            var returnType = binding.Invoke.Method.ReturnType.Substitute(binding.Invoke.TypeArguments, binding.Invoke.MethodArguments);
            var value = world.ReturnValue(ordinal, returnType);
            var register = result.Pieces[0].Register;
            uc.SetReg(register.Bank == Cpp2CS.Ir.Bank.Gpr ? Unicorn.X(register.Index) : Unicorn.D(register.Index), value);
        }
        Back();
    }
}

internal sealed partial class CilInterpreter
{
    private StackValue? InvokeDelegate(CilSide side, MethodRef invoke, StackValue[] values)
    {
        var signature = index.StructAbi.Signature(invoke);
        if (signature.Parameters.Any(a => a.Indirect || a.StackOffset is not null)
            || signature.Return is { } r && (r.Indirect || r.StackOffset is not null || r.Pieces.Length != 1))
            throw new Unsupported("委托间接/栈上传参或聚合返回尚未建模");
        if (side.World.DelegateAt(values[0].Bits) is null) throw new Unsupported("委托调用接收者不是合成的单播输入");
        var ordinal = side.NextCall();
        side.Callees.Add(invoke);
        var parameterTypes = StructAbi.ArgumentTypes(invoke).Skip(1).ToArray();
        DelegateModel.Event(side, values[0].Bits, parameterTypes.SelectMany((type, i) =>
            index.StructAbi.ObservableArgument(side, type, ToBytes(type, values[i + 1]))));
        var returnType = invoke.Method.ReturnType.Substitute(invoke.TypeArguments, invoke.MethodArguments);
        return signature.Return is not null ? Load(returnType, side.World.ReturnValue(ordinal, returnType)) : null;
    }
}
