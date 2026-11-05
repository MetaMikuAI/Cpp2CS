using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Calls;

/// <summary>
/// 分派解析：虚调用按接收者的静态类型与虚表槽号确定声明方法，接口调用按接口与槽号，委托调用取 Invoke。
/// 解析结果记在调用上（<see cref="Call.Resolved"/>），之后的内存效果与下降按该方法的机器签名进行。
/// 内存提升前后均可查询；新增目标后由调用方按新签名重做内存提升。
/// </summary>
internal static class DispatchResolution
{
    public static int Run(MachineFunction function, ValueModel values, TypeOracle oracle)
    {
        var targets = Find(function, values, oracle);
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call call && targets.TryGetValue(call.Site, out var method))
                    block.Statements[i] = call with { Resolved = method };
        return targets.Count;
    }

    /// <summary>只读发现调用目标；事实与图改写分开，供内存与分派共同求解。</summary>
    public static IReadOnlyDictionary<CallSite, MethodRef> Find(MachineFunction function, ValueModel values, TypeOracle oracle)
    {
        var targets = new Dictionary<CallSite, MethodRef>();
        foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Resolved is null))
        {
            MethodRef? method = call.Op switch
            {
                null when call.Kind is CallKind.Indirect or CallKind.TailIndirect => MethodPointer(values.Operands(call)[0]) ?? SplitDispatch(call, values, oracle),
                { Kind: OpKind.CallMethodPointer } => MethodPointer(values.Operands(call)[0]),
                { Kind: OpKind.CallDelegate, Operand: MethodRef invoke } => invoke,
                { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> { Item1: DefinitionRef itf } pair } => Slot(itf, pair.Item2, interfaceOnly: true),
                { Kind: OpKind.CallVirtual, Operand: int slot } when Receiver(call, values) is { } receiver => VirtualSlot(oracle.TypeOf(receiver), slot, oracle.Types, oracle.Substitute),
                _ => null,
            };
            if (method is not null) targets.Add(call.Site, method);
        }
        return targets;
    }

    /// <summary>符号求值已确定 MethodInfo 时，偏移零的 methodPointer 读取指向该方法。</summary>
    private static MethodRef? MethodPointer(Sym value) => SymTable.Resolve(value) switch
    {
        EntitySym { Symbol: { Kind: SymbolKind.Method, Value: MethodRef method } } => method,
        ReadSym { Width: 64, Address: EntitySym { Symbol: { Kind: SymbolKind.Method, Value: MethodRef method } } } => method,
        _ => null,
    };

    /// <summary>
    /// L2 按模板识别虚调用和接口调用时目标还是合流值；路径拆分之后目标成为单一读取，这里按同样的形态解析：
    /// 接口查找结果的方法指针，泛型虚方法解析结果的虚方法指针，或接收者类指针上虚表槽的方法指针。
    /// </summary>
    private static MethodRef? SplitDispatch(Call call, ValueModel values, TypeOracle oracle)
    {
        if (SymTable.Resolve(values.Operands(call)[0]) is not ReadSym { Width: 64 } target) return null;
        if (SymTable.Resolve(target.Address) is ResultSym { Site: Call { Op: { Kind: OpKind.InterfaceInvokeData, Operand: ValueTuple<object?, int> { Item1: DefinitionRef itf } lookup } } })
            return Slot(itf, lookup.Item2, interfaceOnly: true);
        if (oracle.Decompose(target.Address) is (ResultSym { Site: Call { Op: { Kind: OpKind.ResolveGenericVirtual, Operand: MethodRef generic } } }, RuntimeLayout.MethodVirtualPointer, null, _))
            return generic;
        return oracle.Decompose(target.Address) is (_, var offset, null, _) && offset >= RuntimeLayout.ClassVtable
            && (offset - RuntimeLayout.ClassVtable) % RuntimeLayout.VirtualInvokeDataSize == 0 && Receiver(call, values) is { } receiver
            ? oracle.VirtualMethod(target, receiver) : null;
    }

    private static Sym? Receiver(Call call, ValueModel values)
    {
        var position = Array.IndexOf(call.Sources, Storage.Gpr(0));
        return position < 0 ? null : values.Operands(call)[1 + position];
    }

    /// <summary>类型（沿基类链）中占据虚表槽 slot 的虚方法，类型实参代入声明类型。</summary>
    internal static MethodRef? VirtualSlot(TypeRef? type, int slot, ManagedTypes types, Func<TypeRef, TypeRef>? substitute = null)
    {
        if (type is GenericParameterRef { IsReference: true } parameter)
            type = parameter.ReferenceBase is { } constraint ? substitute?.Invoke(constraint) ?? constraint : types.Object;
        if (type is ArrayRef) type = types.CorlibDefinition("System.Array") is { } array ? new DefinitionRef(array, []) : null;
        // 接口自身的槽号只供 interface offset 分派；对象虚表上的槽属于 Object。
        if (type is DefinitionRef { Definition.IsInterface: true }) type = types.Object;
        return type is DefinitionRef owner ? Slot(owner, slot, interfaceOnly: false) : null;
    }

    /// <summary>类型（沿基类链）中占据虚表槽 slot 的虚方法，类型实参代入声明类型。</summary>
    internal static MethodRef? Slot(DefinitionRef type, int slot, bool interfaceOnly)
    {
        for (TypeRef? current = type; current is DefinitionRef d; current = interfaceOnly ? null : d.Definition.BaseType?.Substitute(d.Arguments, []))
            if (d.Definition.Methods.FirstOrDefault(m => m.IsVirtual && m.Slot == slot && m.GenericParameters.Count == 0) is { } method)
                return new MethodRef(method, d.Arguments, []);
        return null;
    }
}
