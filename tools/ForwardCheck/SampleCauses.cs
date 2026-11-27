using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.Runtime;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>在已完成下降的只读视图上解释诊断。基址、位宽或来源没有依据时保留“其他”。</summary>
internal sealed class SampleCauses
{
    private readonly FactView view;
    private EffectGraph Graph => view.Effects;
    private MethodSnapshot Snapshot => Graph.Snapshot;
    private RuntimeLayout Layout => view.Layout;
    private readonly Dictionary<Term, TypeShape> types = [];
    private readonly Dictionary<Term, string> reads = [];
    private readonly HashSet<Term> metadataSlots = [];
    private Dictionary<Term, HashSet<string>>? uses;
    private const string Header = "对象头 klass";
    private const string Cctor = "类结构 cctor_finished";

    public SampleCauses(FactView view)
    {
        this.view = view;
        foreach (var arg in Graph.Arguments) types[arg.Value] = arg.Type;
        foreach (int index in Graph.Order)
        {
            var block = new BlockId(index);
            for (int i = 0; i < Snapshot.OccurrenceCount(block); i++)
            {
                var id = new OccurrenceId(block, i);
                var effect = Graph.Effect(id);
                if (effect?.Callee?.Return is { } returned && effect.Result is { } result) types[result] = returned;
                if (effect is { Kind: NativeEffectKind.NewObject, Class.Kind: TermKind.Entity, Value: { } obj })
                    types[obj] = new(StackKind.Object, Layout.PointerBits, false, effect.Class.Entity);
                if (Snapshot[id] is not ReadOccurrence read) continue;
                var value = Snapshot.Results(id)[0];
                var address = Graph.Resolve(read.Location);
                if (address.IsConstant && Graph.Resolve(value).Kind == TermKind.Entity) metadataSlots.Add(address);
                reads[value] = ReadKind(address, read.Width, value);
            }
        }
    }

    public void Record(Hole hole, SampleCauseCounts counts)
    {
        var effect = hole.Effect is { IsEdge: false } reference ? Graph.Effect(reference.Occurrence) : null;
        string layer = Recover.Reason(hole.Layer.ToString(), hole.Obligation);
        string key;
        IEnumerable<string>? usage = null;
        ulong address = hole.Effect is { } site ? site.IsEdge ? Snapshot.Terminator(site.Block).Address : Snapshot[site.Occurrence].Address : 0;
        if (hole.Layer == HoleLayer.Discovery && effect is { Kind: NativeEffectKind.Read, Value: { } read } && hole.Reason == "没有声明触及这个效果")
        {
            key = "读取 · " + reads[read];
            uses ??= ReadUses();
            usage = uses.TryGetValue(read, out var found) ? found : ["未见直接用途"];
        }
        else if (effect is { Kind: NativeEffectKind.Unnamed } && IsUnnamedCall(effect) && Snapshot[effect.Occurrence] is CallOccurrence call)
            key = "未命名调用 · " + Target(call);
        else if (hole.What.StartsWith('B') && hole.What.IndexOf(' ') is int end && end > 1 &&
            int.TryParse(hole.What.AsSpan(1, end - 1), out int index) && (uint)index < Snapshot.BlockCount &&
            (hole.Layer == HoleLayer.Skeleton || hole.Layer == HoleLayer.Value && hole.What.EndsWith(" 的分支条件", StringComparison.Ordinal)))
        {
            var block = new BlockId(index);
            var term = Snapshot.Terminator(block);
            address = term.Address;
            if (hole.Layer == HoleLayer.Value) key = "分支 · " + Condition(block);
            else
            {
                var lastCall = Snapshot.Blocks[index].Occurrences.OfType<CallOccurrence>().LastOrDefault();
                string kind = term.Kind == TerminatorKind.Single ? term.Exits[0].Kind switch
                {
                    ExitKind.NoReturn => "不返回的调用", ExitKind.Trap => "陷阱", var exit => exit.ToString(),
                } : term.Kind.ToString();
                key = "骨架 · " + kind + " · " + (lastCall == null ? "块内无前置调用" : Target(lastCall));
            }
        }
        else key = SampleCauseCounts.Pattern(layer, hole.What, hole.Reason);
        counts.Add(key, hole.What + "：" + hole.Reason, address, hole.Derived, usage);
    }

    private static bool IsUnnamedCall(NativeEffect e) => e.Detail.StartsWith("未命名的调用：", StringComparison.Ordinal)
        || e.Detail.StartsWith("调用的目标没有命名：", StringComparison.Ordinal);

    private string Target(CallOccurrence call) => call.Target is null ? $"原语 {call.Primitive}"
        : Graph.Resolve(call.Target) is { IsConstant: true } value ? $"0x{value.Value:x}" : "间接目标未定";

    private static (Term Root, long Offset) BaseOffset(Term address) =>
        address is { Op: Op.Add, Operands: [var root, { IsConstant: true } offset] }
            ? (root, unchecked((long)(ulong)offset.Value)) : (address, 0L);

    private bool Class(Term root) => root.Kind == TermKind.Entity && root.Entity.Kind == EntityKind.Type ||
        root.Kind == TermKind.Attribute && root.Attribute.Value is (int)RuntimeFunction.ClassOf or (int)RuntimeFunction.ElementClass ||
        reads.GetValueOrDefault(root) is Header or "类结构 element_class" or "类结构 castClass" or "继承链表项";

    private string ClassField(long offset, int width)
    {
        if (offset == Layout.ClassInitializedOffset && width == Layout.ClassInitializedBits) return Cctor;
        if (offset == Layout.ClassInitializedFlagsOffset && width == 8) return "类结构 initialized 标志";
        if (offset == Layout.ClassSizeFlagsOffset && width == 8) return "类结构 size 标志";
        if (offset == Layout.ClassInterfaceCountOffset && width == Layout.ClassInterfaceCountBits) return "类结构 interface_offsets_count";
        if (offset == Layout.ClassTypeHierarchyDepthOffset && width == Layout.ClassTypeHierarchyDepthBits) return "类结构 typeHierarchyDepth";
        if (width == Layout.PointerBits)
        {
            if (offset == Layout.ClassStaticFieldsOffset) return "类结构 static_fields";
            if (offset == Layout.ClassInterfaceOffsetsOffset) return "类结构 interfaceOffsets";
            if (offset == Layout.ClassElementOffset) return "类结构 element_class";
            if (offset == Layout.ClassCastOffset) return "类结构 castClass";
            if (offset == Layout.ClassTypeHierarchyOffset) return "类结构 typeHierarchy";
            if (offset >= Layout.ClassVTableOffset)
            {
                long part = (offset - Layout.ClassVTableOffset) % Layout.VirtualInvokeDataBytes;
                if (part == Layout.VirtualMethodPointerOffset) return "类结构 vtable.methodPtr";
                if (part == Layout.VirtualMethodInfoOffset) return "类结构 vtable.method";
            }
        }
        return "类结构其他字段";
    }

    private string ReadKind(Term address, int width, Term value)
    {
        if (metadataSlots.Contains(address)) return "元数据槽";
        var (root, offset) = BaseOffset(address);
        if (Class(root)) return ClassField(offset, width);
        if (root.Kind == TermKind.EntryParameter && root.Slot.Kind == SlotKind.StackPointer) return "栈上的值";
        if (root.Kind == TermKind.EntryParameter && root.Slot.Kind == SlotKind.ThreadPointer) return "原生线程指针相对读取";
        if (root.Kind == TermKind.Result && Snapshot[root.Occurrence] is StackAllocateOccurrence) return "栈上的值";
        if (root.Kind == TermKind.Result && Snapshot[root.Occurrence] is CallOccurrence called &&
            called.ResultSlots[root.ResultIndex] == new Slot(SlotKind.Integer, 0) && Graph.Effect(root.Occurrence) is { } producer &&
            producer.Detail is "未命名的调用：_Z37il2cpp_codegen_get_thread_static_dataP11Il2CppClass" or
                "未命名的调用：_Z51il2cpp_codegen_get_thread_static_field_data_pointerP9FieldInfo" or
                "未命名的调用：_ZN6il2cpp2vm6Thread19GetThreadStaticDataEi")
            return "线程静态";
        if (reads.GetValueOrDefault(root) == "类结构 static_fields") return "静态区字段";
        if (types.TryGetValue(root, out var type) && type.Kind is StackKind.Object or StackKind.ByRef)
        {
            if (type.Kind == StackKind.Object && offset == Layout.ObjectClassOffset && width == Layout.PointerBits) return Header;
            if (view.Metadata.ElementOf(type.Entity) is { } element && type.Kind == StackKind.Object)
            {
                if (offset == Layout.ArrayLengthOffset && (width == Layout.ArrayLengthBits || width == Layout.ArrayLengthStorageBits)) return "数组长度";
                if (offset >= Layout.ArrayDataOffset && element.StorageBits == width && (offset - Layout.ArrayDataOffset) % Math.Max(1, width / 8) == 0)
                { types[value] = element; return "数组元素"; }
            }
            long header = type.Kind == StackKind.ByRef ? Layout.ObjectHeaderBytes : 0;
            if (offset >= 0 && offset <= int.MaxValue - header && view.Metadata.FieldAt(type.Entity, (int)(offset + header)) is { } member &&
                member.Type.StorageBits == width)
            {
                types[value] = member.Type;
                return type.Kind == StackKind.ByRef ? "实例字段（值类型，经地址）" : "实例字段（引用类型接收者）";
            }
        }
        // 数组或虚表的动态下标只在基址身份、数据起点和步长同时符合布局时命名。
        if (root is { Op: Op.Add, Operands: [var a, var b] })
        {
            foreach (var (baseTerm, index) in new[] { (a, b), (b, a) })
            {
                var (baseRoot, extra) = BaseOffset(baseTerm);
                long displacement = unchecked(offset + extra);
                if (Class(baseRoot) && displacement >= Layout.ClassVTableOffset && Multiple(index, Layout.VirtualInvokeDataBytes))
                    return ClassField(displacement, width);
                if (reads.GetValueOrDefault(baseRoot) == "类结构 typeHierarchy" && width == Layout.PointerBits &&
                    displacement % (width / 8) == 0 && Multiple(index, width / 8)) return "继承链表项";
                if (types.TryGetValue(baseRoot, out var array) && array.Kind == StackKind.Object &&
                    view.Metadata.ElementOf(array.Entity) is { } elem && elem.StorageBits == width && displacement == Layout.ArrayDataOffset &&
                    Multiple(index, Math.Max(1, width / 8))) { types[value] = elem; return "数组元素"; }
            }
        }
        if (root.Kind == TermKind.BlockParameter) return "其他（合流基址未定）";
        if (root.Kind == TermKind.Result)
        {
            if (Snapshot[root.Occurrence] is ReadOccurrence) return "其他（前一次读取的指针未定位）";
            if (Graph.Effect(root.Occurrence) is { } call && IsUnnamedCall(call)) return "其他（未命名调用给出的基址）";
        }
        return "其他";
    }

    private static bool Multiple(Term index, int bytes) => bytes == 1 ||
        index is { Op: Op.Mul, Operands: [_, { IsConstant: true } stride] } && stride.Value == (uint)bytes ||
        index is { Kind: TermKind.Concat, Operands: [{ IsConstant: true } low, ..] } && low.Value == 0 && low.Width < 32 && (1L << low.Width) % bytes == 0;

    private string Condition(BlockId block)
    {
        if (Graph.Condition(block) is not { } condition) return "其他";
        var sources = new HashSet<string>();
        bool comparison = false, typeData = false;
        foreach (var term in Terms(condition))
        {
            comparison |= term.Op is Op.Eq or Op.Slt or Op.Ult;
            if (FloatingComparison(term)) sources.Add("浮点比较");
            if (term.Kind == TermKind.Attribute && term.Attribute.Value == (int)RuntimeFunction.IsInstance) typeData = comparison = true;
            if (term.Kind != TermKind.Result) continue;
            string? read = reads.GetValueOrDefault(term);
            typeData |= read is Header or "类结构 element_class" or "类结构 castClass" or "类结构 typeHierarchyDepth" or "继承链表项";
            if (read == Cctor) sources.Add("类初始化标志 cctor_finished");
            if (Graph.Effect(term.Occurrence) is { Kind: NativeEffectKind.Unnamed } e && IsUnnamedCall(e)) sources.Add("未命名调用的结果");
            if (term.Width == 8 && Graph.RuntimeStateAddress(term) is { IsConstant: true } address && GuardArm(block, address) is { } guard)
                sources.Add(guard);
        }
        if (comparison && typeData) sources.Add("对象头或类结构的类型比较");
        return sources.Count switch { 0 => "其他", 1 => sources.Single(), _ => string.Join("＋", sources.Order(StringComparer.Ordinal)) };
    }

    // 同址字节在守卫臂的调用后置一；调用的首实参是图中读成实体的元数据槽时才能确定初始化对象。
    private string? GuardArm(BlockId block, Term address)
    {
        foreach (var exit in Snapshot.Terminator(block).Exits)
        {
            if (exit.Kind != ExitKind.Target) continue;
            bool callSeen = false, slotSeen = false;
            foreach (var op in Snapshot.Blocks[exit.Target.Index].Occurrences)
            {
                if (op is CallOccurrence call)
                {
                    callSeen = true;
                    int at = call.ArgumentSlots.IndexOf(new(SlotKind.Integer, 0));
                    if (at >= 0) slotSeen |= metadataSlots.Contains(Graph.Resolve(call.Arguments[at]));
                }
                if (callSeen && op is WriteOccurrence write && Graph.Resolve(write.Location) == address &&
                    Graph.Resolve(write.Value) is { IsConstant: true, Width: 8 } stored && stored.Value == 1)
                    return slotSeen ? "元数据初始化标志" : "映像字节守卫（元数据用途待证）";
            }
        }
        return null;
    }

    private static bool FloatingComparison(Term t) => t.Op is Op.FEq or Op.FLt or Op.FLe or Op.FUnordered;

    private static IEnumerable<Term> Terms(Term root)
    {
        var seen = new HashSet<Term>();
        var pending = new Stack<Term>();
        pending.Push(root);
        while (pending.TryPop(out var term))
        {
            if (!seen.Add(term)) continue;
            yield return term;
            foreach (var child in term.Operands) pending.Push(child);
        }
    }

    private Dictionary<Term, HashSet<string>> ReadUses()
    {
        var result = new Dictionary<Term, HashSet<string>>();
        void Mark(Term? term, string use)
        {
            if (term == null) return;
            foreach (var part in Terms(Graph.Resolve(term)))
            {
                if (reads.ContainsKey(part))
                {
                    if (!result.TryGetValue(part, out var tags)) result.Add(part, tags = []);
                    tags.Add(use);
                }
                if (use != "比较操作数" && (part.Op is Op.Eq or Op.Slt or Op.Ult || FloatingComparison(part)))
                    foreach (var operand in part.Operands) Mark(operand, "比较操作数");
            }
        }
        foreach (int index in Graph.Order)
        {
            var b = new BlockId(index);
            for (int i = 0; i < Snapshot.OccurrenceCount(b); i++)
            {
                var id = new OccurrenceId(b, i);
                switch (Snapshot[id])
                {
                    case ReadOccurrence r: Mark(r.Location, "读取地址"); break;
                    case WriteOccurrence w: Mark(w.Location, "写入地址"); Mark(w.Value, "被写入的值"); break;
                    case CallOccurrence c:
                        Mark(c.Target, "间接调用目标");
                        if (Graph.Effect(id) is { Kind: NativeEffectKind.Call } call)
                            foreach (var arg in call.Arguments) Mark(arg, "托管调用实参");
                        else foreach (var arg in c.Arguments) Mark(arg, "调用现场候选实参槽");
                        break;
                    case StackAllocateOccurrence s: Mark(s.Size, "栈分配大小"); break;
                }
            }
            Mark(Graph.Condition(b), "分支或跳转表条件");
            Mark(Graph.Returned(b), "返回值");
        }
        return result;
    }
}
