using System.Collections.Immutable;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Spec.Runtime;

/// <summary>内联体中的外部调用。符号指定重载；异常沿调用点传播，结果只在正常返回时可用。</summary>
public sealed record RuntimeInlineCall(string Symbol, ImmutableArray<Term> Operands, ImmutableArray<int> ResultWidths) : IFlowOccurrence
{
    // 本组内联体只有接口查找的慢路径，正常返回时不写托管内存。
    public bool DefinesMemory => false;
    public void WriteContent(DigestWriter writer) => writer.Write(Symbol);
}

/// <summary>ArgumentOrder 按图的形参次序给出它们在源码签名中的位置。</summary>
public sealed record RuntimeInlineBody(RuntimeFunction Function, string Source, ImmutableArray<int> ArgumentOrder,
    RuntimeTypeCondition? TargetType, FlowGraph<RuntimeInlineCall> Graph);

public static class RuntimeInlineBodies
{
    public const string InterfaceSlowPath = "_ZN6il2cpp2vm12ClassInlines40GetInterfaceInvokeDataFromVTableSlowPathEP12Il2CppObjectPK11Il2CppClasst";

    public static ImmutableArray<RuntimeInlineBody> ForLayout(RuntimeLayout layout)
    {
        var lookup = InterfaceLookup(layout);
        return [
            new(RuntimeFunction.InterfaceInvokeData, "vm/ClassInlines.h: ClassInlines::GetInterfaceInvokeDataFromVTable(Il2CppObject*, const Il2CppClass*, Il2CppMethodSlot)",
                [0, 1, 2], null, lookup),
            new(RuntimeFunction.InterfaceInvokeData, "codegen/il2cpp-codegen-il2cpp.h: il2cpp_codegen_get_interface_invoke_data(Il2CppMethodSlot, RuntimeObject*, const RuntimeClass*)",
                [1, 2, 0], null, lookup),
            new(RuntimeFunction.IsInstance, RuntimeEquations.SealedSource, [0, 1], RuntimeTypeCondition.SealedOrdinaryClass, TypeTest(layout, true)),
            new(RuntimeFunction.IsInstance, RuntimeEquations.ClassSource, [0, 1], RuntimeTypeCondition.OrdinaryClass, TypeTest(layout, false)),
        ];
    }

    // T0、TH、TB、TF、TS 取自对象重载。索引为 uint16_t，槽号为 il2cpp-config.h 定义的 Il2CppMethodSlot（uint16_t）。
    private static FlowGraph<RuntimeInlineCall> InterfaceLookup(RuntimeLayout layout)
    {
        var p = new TermPool();
        var graph = new FlowBuilder<RuntimeInlineCall>(p);
        var data = new RuntimeDataTerms(p, layout);
        int ptr = layout.PointerBits, countBits = layout.ClassInterfaceCountBits;
        const int slotBits = 16;
        var obj = graph.EntryParameter(new(SlotKind.Managed, 0), ptr);
        var itf = graph.EntryParameter(new(SlotKind.Managed, 1), ptr);
        var slot = graph.EntryParameter(new(SlotKind.Managed, 2), slotBits);
        graph.SetReturnWidths(ptr);
        var head = graph.Block(ptr, ptr, slotBits, countBits);
        var body = graph.Block(ptr, ptr, slotBits, countBits);
        var found = graph.Block(ptr, ptr, slotBits);
        var slow = graph.Block(ptr, ptr, slotBits);

        graph.Terminate(graph.Entry, Terminator.Single(Exit.To(head, obj, itf, slot, p.Zero(countBits))));
        var h = graph.Parameters(head);
        var count = data.Field(data.ClassOf(h[0]), layout.ClassInterfaceCountOffset, countBits);
        graph.Terminate(head, Terminator.Branch(p.Ult(h[3], count), Exit.To(body, h.AsSpan()), Exit.To(slow, h[0], h[1], h[2])));

        var b = graph.Parameters(body);
        var klass = data.ClassOf(b[0]);
        var pair = data.InterfacePair(klass, b[3]);
        var matches = p.Eq(data.Field(pair, layout.InterfaceTypeOffset, ptr), b[1]);
        var next = p.Add(b[3], p.Constant(1, countBits));
        graph.Terminate(body, Terminator.Branch(matches, Exit.To(found, klass, pair, b[2]), Exit.To(head, b[0], b[1], b[2], next)));

        var f = graph.Parameters(found);
        graph.Terminate(found, Terminator.Single(Exit.Return(data.VTableEntry(f[0], f[1], f[2]))));
        var result = graph.Append(slow, new(InterfaceSlowPath, graph.Parameters(slow), [ptr]));
        graph.Terminate(slow, Terminator.Single(Exit.Return(result[0])));
        return graph.Build();
    }

    private static FlowGraph<RuntimeInlineCall> TypeTest(RuntimeLayout layout, bool sealedClass)
    {
        var p = new TermPool();
        var graph = new FlowBuilder<RuntimeInlineCall>(p);
        var data = new RuntimeDataTerms(p, layout);
        int ptr = layout.PointerBits;
        var obj = graph.EntryParameter(new(SlotKind.Managed, 0), ptr);
        var target = graph.EntryParameter(new(SlotKind.Managed, 1), ptr);
        graph.SetReturnWidths(ptr);
        var nonNull = graph.Block(ptr, ptr);
        var nil = p.Zero(ptr);
        graph.Terminate(graph.Entry, Terminator.Branch(p.Eq(obj, nil), Exit.Return(nil), Exit.To(nonNull, obj, target)));
        var args = graph.Parameters(nonNull);
        var klass = data.ClassOf(args[0]);
        if (sealedClass)
        {
            graph.Terminate(nonNull, Terminator.Branch(p.Eq(klass, args[1]), Exit.Return(args[0]), Exit.Return(nil)));
        }
        else
        {
            var ancestor = graph.Block(ptr, ptr, ptr, layout.ClassTypeHierarchyDepthBits);
            var depth = data.Depth(args[1]);
            graph.Terminate(nonNull, Terminator.Branch(p.Uge(data.Depth(klass), depth), Exit.To(ancestor, args[0], args[1], klass, depth), Exit.Return(nil)));
            var a = graph.Parameters(ancestor);
            graph.Terminate(ancestor, Terminator.Branch(p.Eq(data.Ancestor(a[2], a[3]), a[1]), Exit.Return(a[0]), Exit.Return(nil)));
        }
        return graph.Build();
    }
}
