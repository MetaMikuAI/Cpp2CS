using Cpp2CS.Ir;
namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 被比较的方法体编成的微操作：每条语句按 CIL 的求值次序拆成取值、读取、写入与事件，隐式抛出和事件都落在操作之间，
/// 共同执行可以在任何一处分叉或对齐。临时量只在一条语句内存活。
/// </summary>
internal abstract record MicroOp(int Statement);

/// <summary>位置的求值结果：根、根的操作数（临时量）与字段路径。Local 为局部变量（值在环境中或可取址的单元）。</summary>
internal sealed record Place(RootKind Root, int Base, int Index, int[]? Indices, IReadOnlyList<FieldRef> Path, LocalValue? Local, TypeRef Type);

internal sealed record PureOp(int Statement, int Target, ManagedValue Node, int[] Operands) : MicroOp(Statement);
internal sealed record LocalOp(int Statement, int Target, LocalValue Local) : MicroOp(Statement);
internal sealed record LoadOp(int Statement, int Target, Place Place, ManagedValue Node) : MicroOp(Statement);
/// <summary>结构体右值的字段投影。</summary>
internal sealed record ProjectOp(int Statement, int Target, int Source, FieldRef Field, ManagedValue Node) : MicroOp(Statement);
internal sealed record AddressOp(int Statement, int Target, Place Place, ManagedValue Node) : MicroOp(Statement);
/// <summary>表达式中的事件：静态调用值、newobj、newarr、box、委托。</summary>
internal sealed record ValueEventOp(int Statement, int Target, ManagedValue Node, int[] Operands) : MicroOp(Statement);
/// <summary>可能抛出的转换：castclass、unbox.any、unbox。</summary>
internal sealed record CheckedOp(int Statement, int Target, ManagedValue Node, int Operand) : MicroOp(Statement);
internal sealed record StoreOp(int Statement, Place Place, int Value) : MicroOp(Statement);
internal sealed record AssignOp(int Statement, LocalValue Target, int Value) : MicroOp(Statement);
internal sealed record CallOp(int Statement, ManagedCall Call, int Receiver, int[] Arguments) : MicroOp(Statement);
internal sealed record CheckOp(int Statement, int Condition, MethodRef Exception) : MicroOp(Statement);
internal sealed record BranchOp(int Statement, int Condition, int Taken, int Fallthrough) : MicroOp(Statement);
internal sealed record SwitchOp(int Statement, int Index, int[] Cases) : MicroOp(Statement);
internal sealed record JumpOp(int Statement, int Unit) : MicroOp(Statement);
internal sealed record CopyOp(int Statement, LocalValue[] Targets, int[] Values) : MicroOp(Statement);
internal sealed record GotoOp(int Statement, ulong Block) : MicroOp(Statement);
internal sealed record ReturnOp(int Statement, int Value) : MicroOp(Statement);
internal sealed record ThrowOp(int Statement, int Value) : MicroOp(Statement);
internal sealed record UnsupportedOp(int Statement, string Reason) : MicroOp(Statement);

/// <summary>代码单元：一个块，或一条出边（边上的并行复制加跳转）。Block 是块本身或边的目标，Source 是代码所在的块。</summary>
internal sealed record CodeUnit(int Index, ulong Block, bool Edge, MicroOp[] Ops)
{
    public ulong Source { get; init; } = Block;
}

internal sealed class Program
{
    public required ManagedBody Body { get; init; }
    public required IReadOnlyList<CodeUnit> Units { get; init; }
    public required IReadOnlyDictionary<ulong, int> BlockUnits { get; init; }

    /// <summary>块中第 index 条语句产生的事件数（调用、分配、装箱、委托）。</summary>
    public int EventsAt(ulong block, int index) => Units[BlockUnits[block]].Ops.Count(o => o.Statement == index && o is CallOp or ValueEventOp);

    /// <summary>方法体中可能产生事件的微指令数：无环方法体每条路径上的事件数不超过它。</summary>
    public int EventBound => Units.Sum(u => u.Ops.Count(o => o is CallOp or ValueEventOp));
    public required IReadOnlyDictionary<ulong, ManagedBlock> Blocks { get; init; }
    /// <summary>取过地址的局部：值放在单元里，按位置读写。</summary>
    /// <summary>以存储单元建模的局部：取址的局部与结构体局部。</summary>
    public required IReadOnlySet<Variable> Cells { get; init; }
    /// <summary>取过地址的局部：可能经地址被调用改写，不能按定义推断它的值。</summary>
    public required IReadOnlySet<Variable> AddressTaken { get; init; }
    public required int Temps { get; init; }
    public MethodRef Method => Body.Method;
    public ulong Entry => Body.Blocks[0].Address;

    private Dictionary<ulong, HashSet<Variable>>? liveIn;
    private Dictionary<Variable, LocalValue>? locals;

    /// <summary>方法体中出现的局部（取其类型）。</summary>
    public LocalValue? LocalOf(Variable variable)
    {
        locals ??= Body.Blocks.SelectMany(b => b.Statements)
            .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)).Concat(ManagedValues.Edges(s).SelectMany(e => e.Copies).Select(c => (ManagedValue)c.Target))
                .Concat(s is ManagedCall { Result: { } r } ? [r] : []))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().DistinctBy(l => l.Variable).ToDictionary(l => l.Variable);
        return locals.GetValueOrDefault(variable);
    }
    private Dictionary<ulong, ulong[]>? predecessors;

    /// <summary>块所在的最内层 try 区域；不在 try 中为 null。</summary>
    public ManagedRegion? HandlerOf(ulong block) =>
        Body.Regions.Where(r => r.Try.Contains(block)).OrderBy(r => r.Try.Count).FirstOrDefault();

    public IReadOnlyList<ulong> Predecessors(ulong block)
    {
        predecessors ??= Body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => (From: b.Address, e.Target)))
            .Distinct().GroupBy(p => p.Target).ToDictionary(g => g.Key, g => g.Select(p => p.From).ToArray());
        return predecessors.GetValueOrDefault(block) ?? [];
    }

    /// <summary>语句读到的局部（含边上复制的源值；赋值目标不算）。</summary>
    public static IEnumerable<Variable> Uses(ManagedStatement statement) =>
        (statement is ManagedAssignment a ? [a.Value] : ManagedValues.Of(statement)).Concat(ManagedValues.CopiedValues(statement))
            .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable);

    public static IEnumerable<Variable> Definitions(ManagedStatement statement) => statement switch
    {
        ManagedAssignment a => [a.Target.Variable],
        ManagedCall { Result: { } result } => [result.Variable],
        _ => [],
    };

    /// <summary>块入口处活跃的局部（取址的局部视为一直活跃）。</summary>
    public IReadOnlySet<Variable> LiveIn(ulong block)
    {
        if (liveIn is null) ComputeLiveness();
        return liveIn!.GetValueOrDefault(block) ?? [];
    }

    /// <summary>块中第 index 条语句之前活跃的局部。</summary>
    public HashSet<Variable> LiveBefore(ulong block, int index)
    {
        if (liveIn is null) ComputeLiveness();
        var statements = Blocks[block].Statements;
        var live = LiveOut(block);
        for (var i = statements.Count - 1; i >= index; i--) Transfer(statements[i], live);
        return live;
    }

    /// <summary>第 index 条语句之后活跃的局部，不计这条语句自己（含它的边上复制）读到的局部。</summary>
    public HashSet<Variable> LiveThrough(ulong block, int index)
    {
        if (liveIn is null) ComputeLiveness();
        var statements = Blocks[block].Statements;
        if (index < statements.Count - 1) return LiveBefore(block, index + 1);
        var live = new HashSet<Variable>(Cells);
        foreach (var edge in ManagedValues.Edges(statements[index]))
        {
            var target = new HashSet<Variable>(liveIn!.GetValueOrDefault(edge.Target) ?? []);
            foreach (var copy in edge.Copies) target.Remove(copy.Target.Variable);
            live.UnionWith(target);
        }
        if (HandlerOf(block) is { } region) live.UnionWith(liveIn!.GetValueOrDefault(region.HandlerEntry) ?? []);
        return live;
    }

    private HashSet<Variable> LiveOut(ulong block)
    {
        var live = new HashSet<Variable>(Cells);
        var last = Blocks[block].Statements.LastOrDefault();
        if (last is null) return live;
        foreach (var edge in ManagedValues.Edges(last))
        {
            var target = new HashSet<Variable>(liveIn!.GetValueOrDefault(edge.Target) ?? []);
            foreach (var copy in edge.Copies) target.Remove(copy.Target.Variable);
            foreach (var copy in edge.Copies) target.UnionWith(ManagedValues.Walk(copy.Value).OfType<LocalValue>().Select(l => l.Variable));
            live.UnionWith(target);
        }
        // 抛出可到达处理块：处理块入口活跃的局部在整个 try 中活跃。
        if (HandlerOf(block) is { } region) live.UnionWith(liveIn!.GetValueOrDefault(region.HandlerEntry) ?? []);
        return live;
    }

    private static void Transfer(ManagedStatement statement, HashSet<Variable> live)
    {
        foreach (var defined in Definitions(statement)) live.Remove(defined);
        live.UnionWith(Uses(statement));
    }

    private void ComputeLiveness()
    {
        liveIn = Body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<Variable>());
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var block in Body.Blocks.AsEnumerable().Reverse())
            {
                var live = LiveOut(block.Address);
                for (var i = block.Statements.Count - 1; i >= 0; i--) Transfer(block.Statements[i], live);
                if (!live.SetEquals(liveIn[block.Address])) { liveIn[block.Address] = live; changed = true; }
            }
        }
    }

    // ---- 编译 ----

    public static Program Compile(ManagedBody body, ManagedTypes types)
    {
        var values = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))
            .Concat(ManagedValues.Edges(s).SelectMany(e => e.Copies.Select(c => (ManagedValue)c.Target)))
            .Concat(s is ManagedCall { Result: { } result } ? [result] : [])).SelectMany(ManagedValues.Walk).ToArray();
        var addressTaken = values.OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        // 结构体局部也是存储单元：内联的实例方法经 ref this 访问它，两侧须是同一种位置。
        var cells = values.OfType<LocalValue>().Where(l => types.Kind(l.Type) == TypeKind.Struct).Select(l => l.Variable).Concat(addressTaken).ToHashSet();
        var compiler = new Compiler(types, cells);
        var blockUnits = new Dictionary<ulong, int>();
        foreach (var block in body.Blocks) blockUnits[block.Address] = compiler.Reserve(block.Address, false);
        foreach (var block in body.Blocks) compiler.CompileBlock(block, blockUnits[block.Address]);
        return new Program
        {
            Body = body,
            Units = compiler.Units,
            BlockUnits = blockUnits,
            Blocks = body.Blocks.ToDictionary(b => b.Address),
            Cells = cells,
            AddressTaken = addressTaken,
            Temps = compiler.MaxTemps,
        };
    }

    private sealed class Compiler(ManagedTypes types, HashSet<Variable> cells)
    {
        public readonly List<CodeUnit> Units = [];
        private readonly List<(ulong Block, bool Edge)> reserved = [];
        public int MaxTemps;
        private List<MicroOp> ops = [];
        private int temps;
        private int statement;

        public int Reserve(ulong block, bool edge)
        {
            reserved.Add((block, edge));
            Units.Add(null!);
            return Units.Count - 1;
        }

        private int Temp() { var t = temps++; MaxTemps = Math.Max(MaxTemps, temps); return t; }

        public void CompileBlock(ManagedBlock block, int unit)
        {
            ops = [];
            source = block.Address;
            for (statement = 0; statement < block.Statements.Count; statement++)
            {
                temps = 0;
                Statement(block.Statements[statement]);
            }
            if (block.Statements.Count == 0 || ManagedValues.Edges(block.Statements[^1]).Count == 0 && block.Statements[^1] is not
                (ManagedReturn or ManagedThrow or ManagedRethrow or ManagedEndFault or ManagedHole { Terminal: true }))
                ops.Add(new UnsupportedOp(block.Statements.Count, "块没有终结语句"));
            Units[unit] = new CodeUnit(unit, block.Address, false, ops.ToArray());
        }

        private ulong source;

        private int EdgeUnit(ManagedEdge edge)
        {
            var saved = (ops, temps);
            var unit = Reserve(edge.Target, true);
            ops = [];
            temps = 0;
            if (edge.Copies.Count > 0)
            {
                var values = edge.Copies.Select(c => Value(c.Value)).ToArray();
                ops.Add(new CopyOp(statement, edge.Copies.Select(c => c.Target).ToArray(), values));
            }
            ops.Add(new GotoOp(statement, edge.Target));
            Units[unit] = new CodeUnit(unit, edge.Target, true, ops.ToArray()) { Source = source };
            (ops, temps) = saved;
            return unit;
        }

        private void Statement(ManagedStatement s)
        {
            switch (s)
            {
                case ManagedAssignment a:
                    ops.Add(new AssignOp(statement, a.Target, Value(a.Value)));
                    break;
                case ManagedStore store:
                    {
                        if (Locate(store.Target) is not { } place) { ops.Add(new UnsupportedOp(statement, $"写入目标不是位置：{store.Target}")); break; }
                        ops.Add(new StoreOp(statement, place, Value(store.Value)));
                        break;
                    }
                case ManagedCall call:
                    {
                        var receiver = call.Invocation.Receiver is { } r ? Value(r) : -1;
                        var arguments = call.Invocation.Arguments.Select(Value).ToArray();
                        ops.Add(new CallOp(statement, call, receiver, arguments));
                        break;
                    }
                case ManagedReturn r:
                    ops.Add(new ReturnOp(statement, r.Value is { } v ? Value(v) : -1));
                    break;
                case ManagedThrow t:
                    ops.Add(new ThrowOp(statement, Value(t.Exception)));
                    break;
                case ManagedCheck c:
                    ops.Add(new CheckOp(statement, Value(c.Condition), c.Exception));
                    break;
                case ManagedJump j:
                    ops.Add(new JumpOp(statement, EdgeUnit(j.Edge)));
                    break;
                case ManagedBranch b:
                    {
                        var condition = Value(b.Condition);
                        ops.Add(new BranchOp(statement, condition, EdgeUnit(b.Taken), EdgeUnit(b.Fallthrough)));
                        break;
                    }
                case ManagedSwitch w:
                    {
                        var index = Value(w.Index);
                        ops.Add(new SwitchOp(statement, index, w.Cases.Select(EdgeUnit).ToArray()));
                        break;
                    }
                case ManagedHole hole:
                    ops.Add(new UnsupportedOp(statement, $"未恢复的语句：{hole.Reason}"));
                    break;
                default:
                    ops.Add(new UnsupportedOp(statement, $"不支持的语句：{s.GetType().Name}"));
                    break;
            }
        }

        private bool IsStruct(TypeRef type) => types.Kind(type) == TypeKind.Struct;

        /// <summary>值作为位置求值：字段链、静态字段、数组元素、经引用、局部变量。右值的字段不是位置，返回 null。</summary>
        private Place? Locate(ManagedValue value)
        {
            switch (value)
            {
                case FieldValue field:
                    {
                        var receiver = field.Receiver;
                        if (receiver.Type is ByRefRef or PointerRef)
                            return new Place(RootKind.Reference, Value(receiver), -1, null, [field.Field], null, field.Type);
                        if (ManagedTypes.IsReferenceType(receiver.Type) || types.Kind(receiver.Type) == TypeKind.Reference)
                            return new Place(RootKind.Field, Value(receiver), -1, null, [field.Field], null, field.Type);
                        if (receiver is FieldValue or StaticFieldValue or ArrayElementValue or MultiArrayElementValue or IndirectValue or LocalValue
                            && Locate(receiver) is { } inner)
                            return inner with { Path = [.. inner.Path, field.Field], Type = field.Type };
                        return null;
                    }
                case StaticFieldValue field:
                    return new Place(RootKind.Static, -1, -1, null, [field.Field], null, field.Type);
                case ArrayElementValue element:
                    {
                        var array = Value(element.Array);
                        return new Place(RootKind.Element, array, Value(element.Index), null, [], null, element.Type);
                    }
                case MultiArrayElementValue element:
                    {
                        var array = Value(element.Array);
                        return new Place(RootKind.MultiElement, array, -1, element.Indices.Select(Value).ToArray(), [], null, element.Type);
                    }
                case IndirectValue indirect:
                    return new Place(RootKind.Reference, Value(indirect.Address), -1, null, [], null, indirect.Type);
                case LocalValue local:
                    return new Place(RootKind.Cell, -1, -1, null, [], local, local.Type);
                default:
                    return null;
            }
        }

        private int Value(ManagedValue value)
        {
            switch (value)
            {
                case LocalValue local when !cells.Contains(local.Variable):
                    {
                        var t = Temp();
                        ops.Add(new LocalOp(statement, t, local));
                        return t;
                    }
                case LocalValue or FieldValue or StaticFieldValue or ArrayElementValue or MultiArrayElementValue or IndirectValue:
                    {
                        if (Locate(value) is { } place)
                        {
                            var t = Temp();
                            ops.Add(new LoadOp(statement, t, place, value));
                            return t;
                        }
                        // 结构体右值的字段。
                        var field = (FieldValue)value;
                        var source = Value(field.Receiver);
                        var target = Temp();
                        ops.Add(new ProjectOp(statement, target, source, field.Field, value));
                        return target;
                    }
                case AddressValue address:
                    {
                        if (Locate(address.Target) is not { } place) { ops.Add(new UnsupportedOp(statement, $"取址的不是位置：{address.Target}")); return Temp(); }
                        var t = Temp();
                        ops.Add(new AddressOp(statement, t, place, value));
                        return t;
                    }
                case ArrayLengthValue length:
                    {
                        var array = Value(length.Array);
                        var t = Temp();
                        ops.Add(new LoadOp(statement, t, new Place(RootKind.Length, array, -1, null, [], null, length.Type), value));
                        return t;
                    }
                case StringLengthValue length:
                    {
                        var text = Value(length.String);
                        var t = Temp();
                        ops.Add(new LoadOp(statement, t, new Place(RootKind.StringLength, text, -1, null, [], null, length.Type), value));
                        return t;
                    }
                case ArrayBoundValue bound:
                    {
                        var array = Value(bound.Array);
                        var t = Temp();
                        ops.Add(new LoadOp(statement, t, new Place(RootKind.Bound, array, bound.Dimension * 2 + (bound.Lower ? 1 : 0), null, [], null, bound.Type), value));
                        return t;
                    }
                case StaticCallValue or NewObjectValue or NewArrayValue or NewMultiArrayValue or BoxValue or DelegateValue:
                    {
                        var operands = ManagedValues.Children(value).Select(Value).ToArray();
                        var t = Temp();
                        ops.Add(new ValueEventOp(statement, t, value, operands));
                        return t;
                    }
                case CheckedCastValue or UnboxValue or UnboxAddressValue:
                    {
                        var operand = Value(ManagedValues.Children(value).Single());
                        var t = Temp();
                        ops.Add(new CheckedOp(statement, t, value, operand));
                        return t;
                    }
                case HoleValue hole:
                    ops.Add(new UnsupportedOp(statement, $"未恢复的值：{hole.Reason}"));
                    return Temp();
                case AsyncResultValue:
                    ops.Add(new UnsupportedOp(statement, "async 结果"));
                    return Temp();
                default:
                    {
                        var operands = ManagedValues.Children(value).Select(Value).ToArray();
                        var t = Temp();
                        ops.Add(new PureOp(statement, t, value, operands));
                        return t;
                    }
            }
        }
    }
}
