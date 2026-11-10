using Cpp2CS.Ir;
using System.Collections.Immutable;
using System.Reflection;

namespace Cpp2CS.Recovery.Inlining;

internal enum EventKind { Call, Construct, NewArray, NewMultiArray, Box, Delegate, ClassInit, Allocate }

/// <summary>
/// 一次事件：种类、身份（方法、类型）、接收者与实参。调用、构造与类初始化执行别的代码，是堆的屏障；
/// 分配（数组、装箱、委托与合成的对象分配）不执行用户代码，只产生新对象。
/// </summary>
internal sealed record EventInfo(EventKind Kind, object Identity, Term? Receiver, Term[] Arguments, bool Virtual)
{
    public TypeRef? Constraint { get; init; }
    /// <summary>调用或构造是从内联代码证明出的（原生代码里是被调方法的方法体，不是调用指令）。</summary>
    public bool Inlined { get; init; }
    /// <summary>结果的类型；无结果为 null。</summary>
    public TypeRef? ResultType { get; init; }
    public bool Barrier => Kind is EventKind.Call or EventKind.Construct or EventKind.ClassInit;
    public bool Allocates => Kind is EventKind.Construct or EventKind.NewArray or EventKind.NewMultiArray or EventKind.Box or EventKind.Delegate or EventKind.Allocate;
    public IEnumerable<Term> Operands => Receiver is null ? Arguments : Arguments.Prepend(Receiver);
}

/// <summary>抛出：隐式异常与 ManagedCheck 按异常类型的全名，显式 throw 按异常对象。</summary>
internal sealed record ThrowInfo(string? ExceptionType, Term? Exception);

internal enum StopKind { Event, Fork, Return, Throw, Soft, Fail }

internal sealed record Stop(StopKind Kind)
{
    public EventInfo? Event { get; init; }
    /// <summary>分叉的各个选择（互斥且覆盖全部情形）。</summary>
    public Term[]? Alternatives { get; init; }
    public Term? Value { get; init; }
    public ThrowInfo? Thrown { get; init; }
    public ulong Block { get; init; }
    public string? Reason { get; init; }
}

/// <summary>调用方语句开始执行时的状态，用于选择出口与改写续接语句。</summary>
internal sealed class TracePoint(ulong block, int statement, ImmutableDictionary<Variable, Term> env, ImmutableList<(Term Location, Term Value)> writes,
    int version, int serial, ImmutableHashSet<Term> exposed, ImmutableHashSet<Term> fresh)
{
    public ulong Block => block;
    public int Statement => statement;
    public ImmutableDictionary<Variable, Term> Env => env;
    public ImmutableList<(Term Location, Term Value)> Writes => writes;
    public int Version => version;
    /// <summary>此前完成的事件数。</summary>
    public int Events => serial;
    public ImmutableHashSet<Term> Exposed => exposed;
    public ImmutableHashSet<Term> Fresh => fresh;
    /// <summary>这条语句中已求值的子值。</summary>
    public Dictionary<ManagedValue, Term> Nodes { get; } = new(ReferenceEqualityComparer.Instance);
    /// <summary>这条语句中发生过的待证访问。</summary>
    public bool Pending { get; set; }
}

internal sealed class Frame
{
    public required Program Program { get; init; }
    public required int Id { get; init; }
    public int Unit { get; set; }
    public int Op { get; set; }
    public ImmutableDictionary<Variable, Term> Env { get; set; } = ImmutableDictionary<Variable, Term>.Empty;
    /// <summary>实参：下标 0 为 this（静态方法时不用），i + 1 为第 i 个形参。</summary>
    public required Term[] Arguments { get; init; }
    public required Term[] Temps { get; set; }
    /// <summary>模板帧：局部未赋值即读取是错误，取址局部初值为零。调用方的底层帧取入口值。</summary>
    public bool Fresh { get; init; }
    /// <summary>构造的帧：引用类型为新对象；值类型为存放新值的单元。</summary>
    public Term? Constructed { get; init; }
    public TypeRef? ConstructedType { get; init; }

    public Frame Clone() => new()
    {
        Program = Program, Id = Id, Unit = Unit, Op = Op, Env = Env, Arguments = Arguments, Temps = (Term[])Temps.Clone(),
        Fresh = Fresh, Constructed = Constructed, ConstructedType = ConstructedType,
    };
}

/// <summary>
/// 一侧的符号状态：帧栈、自上一个屏障以来的写入表与堆版本、取过地址并已交出的单元、尚未逃逸的新对象、已初始化的类型。
/// 写入不是事件，只在事件与结局处比较；读取沿写入表倒查，遇到可能重叠而不能判定相同的写入时这条路径不可判定。
/// </summary>
internal sealed class SideState
{
    public required List<Frame> Frames { get; set; }
    public int Version { get; set; }
    public ImmutableList<(Term Location, Term Value)> Writes { get; set; } = [];
    public ImmutableHashSet<Term> Exposed { get; set; } = ImmutableHashSet.Create<Term>(ReferenceEqualityComparer.Instance);
    public ImmutableHashSet<Term> Fresh { get; set; } = ImmutableHashSet.Create<Term>(ReferenceEqualityComparer.Instance);
    public ImmutableHashSet<TypeDef> Initialized { get; set; } = ImmutableHashSet<TypeDef>.Empty;
    public Stop? Stop { get; set; }
    public int Steps { get; set; }
    /// <summary>调用方的入口值（底层帧未赋值的局部）。</summary>
    public Func<LocalValue, Term>? Entry { get; init; }
    /// <summary>复核：进入两侧相同的块时停下比较。</summary>
    public IReadOnlySet<ulong>? Unchanged { get; init; }
    public ulong? Resumed { get; set; }
    /// <summary>记录底层帧的语句轨迹（发现区域时的调用方）。</summary>
    public bool Tracing { get; init; }
    public ImmutableList<TracePoint> Trace { get; set; } = [];
    private (int Unit, int Statement) last = (-1, -1);
    /// <summary>底层帧中以待证访问为准的语句：(块, 语句)。</summary>
    public Func<ulong, int, bool>? PendingAt { get; init; }
    /// <summary>引用类型的构造：分配完成后压入构造函数的帧。</summary>
    public (Program Template, EventInfo Event)? PendingConstruct { get; set; }
    /// <summary>合成的分配（待证构造的对象）写入的局部。</summary>
    public LocalValue? AllocationTarget { get; set; }
    /// <summary>已完成的事件数。</summary>
    public int Events { get; set; }
    /// <summary>callvirt 进入模板前对接收者的判空。</summary>
    public Term? EntryCheck { get; set; }
    /// <summary>发现区域时模板一侧的异常上下文：调用点的处理块与活跃局部。</summary>
    public (ulong? Handler, IReadOnlyDictionary<Variable, Term> Live)? OuterContext { get; init; }

    public Frame Top => Frames[^1];

    public SideState Clone() => new()
    {
        Frames = Frames.Select(f => f.Clone()).ToList(), Version = Version, Writes = Writes, Exposed = Exposed, Fresh = Fresh,
        Initialized = Initialized, Stop = Stop, Steps = Steps, Entry = Entry, Unchanged = Unchanged, Resumed = Resumed,
        Tracing = Tracing, Trace = Trace, last = last, PendingAt = PendingAt, PendingConstruct = PendingConstruct,
        AllocationTarget = AllocationTarget, OuterContext = OuterContext, Events = Events, EntryCheck = EntryCheck,
    };

    internal void NoteStatement(Program program, Frame frame, MicroOp op)
    {
        if (!Tracing || Frames.Count != 1) return;
        var unit = program.Units[frame.Unit];
        if (unit.Edge || (frame.Unit, op.Statement) == last) return;
        last = (frame.Unit, op.Statement);
        var point = new TracePoint(unit.Block, op.Statement, frame.Env, Writes, Version, Events, Exposed, Fresh)
        {
            Pending = PendingAt?.Invoke(unit.Block, op.Statement) ?? false,
        };
        Trace = Trace.Add(point);
    }

    public TracePoint? Current => Tracing && Trace.Count > 0 ? Trace[^1] : null;
}

/// <summary>结构体的标量叶子：路径、类型、宽度、是否 0/1。没有布局的结构体整体作一片叶子。</summary>
internal sealed record Leaf(FieldPath Path, TypeRef Type, int Width, bool Bit);

/// <summary>一次尝试（发现与各次复核）共用的步数计量：每条路径各有步数上限，路径数也有上限，两者之积仍可能过大。</summary>
internal sealed class Meter(long limit)
{
    public long Used { get; private set; }
    public bool Spend() => ++Used > limit;
}

/// <summary>
/// 解释器：把一侧推进到下一个观察点（事件、不可判定的分支或隐式抛出、结局、复核的同步点）。
/// 读写、赋值、跳转与可判定的分支都是内部步骤。
/// </summary>
internal sealed class Interpreter(ManagedTypes types, Solver solver, InlineEvidence evidence)
{
    public TermTable Terms => solver.Terms;
    public Solver Solver => solver;
    public ManagedTypes Types => types;
    public InlineEvidence Evidence => evidence;
    private readonly Dictionary<TypeRef, Leaf[]> leaves = [];
    public int StepBudget { get; set; } = 6000;
    public Meter? Meter { get; init; }
    private int nextFrame = 1;
    public int NewFrameId() => nextFrame++;

    public Leaf[] Leaves(TypeRef type)
    {
        if (leaves.TryGetValue(type, out var known)) return known;
        Leaf[] result;
        if (type is DefinitionRef structure && types.Kind(structure) == TypeKind.Struct && types.Projections(structure).ToArray() is { Length: > 0 } projections)
            result = projections.Select(p => new Leaf(Terms.Path(p.Path), p.Type, types.ValueWidth(p.Type), IsBool(p.Type))).ToArray();
        else result = [new Leaf(FieldPath.Empty, type, types.ValueWidth(type), IsBool(type))];
        return leaves[type] = result;
    }

    public bool IsStruct(TypeRef type) => types.Kind(type) == TypeKind.Struct;
    public static bool IsBool(TypeRef type) => ManagedTypes.PrimitiveName(type) == "Boolean";

    /// <summary>结构体值的叶子元组，或标量。</summary>
    public Term Shape(TypeRef type, Func<Leaf, Term> leaf)
    {
        if (!IsStruct(type) || type is not DefinitionRef structure) return leaf(Leaves(type)[0]);
        return Terms.Tuple(structure, Leaves(type).Select(leaf).ToArray());
    }

    public Term Zero(TypeRef type) => Shape(type, l => Terms.Constant(0, l.Width));

    public Term Atom(AtomKind kind, object key, TypeRef type) => Shape(type, l =>
    {
        var atom = Terms.Atom(kind, l.Path.Count == 0 ? key : new TermTable.LeafKey(key, l.Path.Id), l.Width, l.Bit);
        atom.Hint ??= kind is AtomKind.Entry or AtomKind.Argument or AtomKind.Formal ? l.Type : null;
        return atom;
    });

    /// <summary>元组中某个字段（可能仍是结构体）。</summary>
    public Term? Project(Term value, IReadOnlyList<FieldRef> path, TypeRef type)
    {
        if (path.Count == 0) return value;
        if (value.Kind != TermKind.Tuple) return null;
        var structure = (DefinitionRef)value.Key!;
        var all = Leaves(structure);
        var prefix = Terms.Path(path);
        var picked = new List<Term>();
        for (var i = 0; i < all.Length; i++)
            if (StartsWith(all[i].Path, prefix)) picked.Add(value.Args[i]);
        if (picked.Count == 0) return null;
        if (!IsStruct(type)) return picked.Count == 1 ? picked[0] : null;
        return picked.Count == Leaves(type).Length ? Terms.Tuple((DefinitionRef)type, picked) : null;
    }

    /// <summary>元组中替换某个字段。</summary>
    public Term? Update(Term whole, IReadOnlyList<FieldRef> path, Term part)
    {
        if (path.Count == 0) return part;
        if (whole.Kind != TermKind.Tuple) return null;
        var structure = (DefinitionRef)whole.Key!;
        var all = Leaves(structure);
        var prefix = Terms.Path(path);
        var args = (Term[])whole.Args.Clone();
        var j = 0;
        for (var i = 0; i < all.Length; i++)
            if (StartsWith(all[i].Path, prefix))
            {
                var value = part.Kind == TermKind.Tuple ? (j < part.Args.Length ? part.Args[j] : null) : j == 0 ? part : null;
                if (value is null) return null;
                args[i] = value;
                j++;
            }
        if (j == 0 || part.Kind == TermKind.Tuple && j != part.Args.Length) return null;
        // 赋给视图的值拆到主叶子上（同时赋了相应主叶子的除外，主叶子为准）；视图分量由 Tuple 重新拼成。
        if (Terms.Overlays?.Invoke(structure) is { } overlay)
        {
            var assigned = Enumerable.Range(0, all.Length).Where(i => StartsWith(all[i].Path, prefix)).ToHashSet();
            foreach (var v in assigned.Where(i => overlay.View[i]).ToArray())
            {
                if (Enumerable.Range(0, all.Length).Where(p => !overlay.View[p] && overlay.Intersects(p, v)).All(assigned.Contains)) continue;
                var before = args;
                if (overlay.Split(Terms, v, args[v], p => before[p]) is not { } parts) return null;
                args = (Term[])args.Clone();
                foreach (var (p, value) in parts) args[p] = value;
            }
        }
        return Terms.Tuple(structure, args);
    }

    public static bool StartsWith(FieldPath path, FieldPath prefix)
    {
        if (path.Count < prefix.Count) return false;
        for (var i = 0; i < prefix.Count; i++)
            if (!path.Fields[i].Equals(prefix.Fields[i])) return false;
        return true;
    }

    public static bool PreciseInit(TypeDef type) => (type.Attributes & TypeAttributes.BeforeFieldInit) == 0 && type.Methods.Any(m => m.Name == ".cctor");

    // ---- 堆 ----

    /// <summary>位置是否在私有存储中：未交出的单元、未逃逸的新对象。私有存储不被屏障改变，事件也看不到。</summary>
    public bool Private(SideState side, Term location) => location.Root switch
    {
        RootKind.Cell => !side.Exposed.Contains(CellOf(location)),
        RootKind.Field or RootKind.Element or RootKind.MultiElement or RootKind.Length => side.Fresh.Contains(location.Args[0]),
        _ => false,
    };

    public Term CellOf(Term location) => Terms.CellRoot(location.Aux, TermTable.CellVariable(location), FieldPath.Empty);

    /// <summary>位置是显式布局结构体的视图叶子时：结构体所在的位置、划分、叶子序号与全部叶子。</summary>
    private (Term Root, Overlay Overlay, int View, Leaf[] Leaves)? ViewOf(Term location)
    {
        var path = TermTable.PathOf(location);
        for (var k = 0; k < path.Count; k++)
        {
            var field = path.Fields[k];
            if (!Explicit(field) || field.DeclaringType is not DefinitionRef owner) continue;
            if (Terms.Overlays?.Invoke(owner) is not { } overlay) return null;
            var all = Leaves(owner);
            var sub = Terms.Path(path.Fields.Skip(k).ToArray());
            var index = Array.FindIndex(all, l => ReferenceEquals(l.Path, sub));
            if (index < 0 || !overlay.View[index] || Terms.Truncate(location, k) is not { } root) return null;
            return (root, overlay, index, all);
        }
        return null;
    }

    /// <summary>字段路径是否可能重叠；在显式布局的结构体处分开时按字节范围判定。</summary>
    private bool FieldsOverlap(FieldPath x, FieldPath y)
    {
        if (!Effects.MemoryFootprint.Overlap(x.Fields, y.Fields)) return false;
        var d = 0;
        while (d < x.Count && d < y.Count && x.Fields[d].Equals(y.Fields[d])) d++;
        if (d >= x.Count || d >= y.Count) return true;
        var (a, b) = (x.Fields[d], y.Fields[d]);
        if (a.Field.Owner != b.Field.Owner || !Explicit(a) || a.DeclaringType is not DefinitionRef owner) return true;
        return Range(owner, x.Fields.Skip(d).ToArray()) is not var (sa, ea) || Range(owner, y.Fields.Skip(d).ToArray()) is not var (sb, eb) || sa < eb && sb < ea;
    }

    /// <summary>结构体内一段字段路径占的字节范围（路径下全部叶子的范围）。</summary>
    private (int Start, int End)? Range(DefinitionRef owner, IReadOnlyList<FieldRef> path)
    {
        var inside = types.Leaves(owner).Where(l => l.Path.Count >= path.Count && l.Path.Take(path.Count).SequenceEqual(path)).ToArray();
        if (inside.Length == 0 || inside.Any(l => types.Size(l.Type) <= 0)) return null;
        return (inside.Min(l => l.Offset), inside.Max(l => l.Offset + types.Size(l.Type)));
    }

    /// <summary>两位置可能共享存储（必然相同的已先判定）。</summary>
    public bool MayOverlap(SideState side, Term x, Term y)
    {
        if (TermTable.Immutable(x) || TermTable.Immutable(y))
            return x.Root == y.Root && x.Aux == y.Aux && !Distinct(side, x.Args[0], y.Args[0]);
        var px = TermTable.PathOf(x);
        var py = TermTable.PathOf(y);
        // 两个标量叶子：最内层字段不同则不是同一存储（显式布局除外）。
        if (px.Count > 0 && py.Count > 0 && !HeapAliasShare(px.Fields[^1], py.Fields[^1]) && !Explicit(px.Fields[^1]) && !Explicit(py.Fields[^1]))
            return false;
        if (x.Root == RootKind.Reference || y.Root == RootKind.Reference)
        {
            var other = x.Root == RootKind.Reference ? y : x;
            if (other.Root != RootKind.Reference && Private(side, other)) return false;
            if (x.Root == RootKind.Reference && y.Root == RootKind.Reference && ReferenceEquals(x.Args[0], y.Args[0]))
                return FieldsOverlap(px, py);
            return true;
        }
        if (x.Root != y.Root) return false;
        switch (x.Root)
        {
            case RootKind.Cell:
                return x.Aux == y.Aux && TermTable.CellVariable(x).Equals(TermTable.CellVariable(y)) && FieldsOverlap(px, py);
            case RootKind.Static:
                return FieldsOverlap(px, py);
            case RootKind.Field:
                return FieldsOverlap(px, py) && !Distinct(side, x.Args[0], y.Args[0]);
            case RootKind.Element:
                if (Distinct(side, x.Args[0], y.Args[0])) return false;
                if (ReferenceEquals(x.Args[0], y.Args[0]) && x.Args[1].IsConstant && y.Args[1].IsConstant && x.Args[1].Bits != y.Args[1].Bits) return false;
                return FieldsOverlap(px, py);
            case RootKind.MultiElement:
                return !Distinct(side, x.Args[0], y.Args[0]) && FieldsOverlap(px, py);
            default:
                return true;
        }
    }

    private static bool HeapAliasShare(FieldRef a, FieldRef b) => Effects.HeapAlias.MayShare(a, b);
    private static bool Explicit(FieldRef field) => (field.Field.Owner.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout;

    /// <summary>两个对象项必然不同：两次分配，或一侧是未逃逸的新对象。</summary>
    public bool Distinct(SideState side, Term a, Term b) => !ReferenceEquals(a, b)
        && (solver.Allocations.Contains(a) && solver.Allocations.Contains(b) || side.Fresh.Contains(a) || side.Fresh.Contains(b));

    /// <summary>
    /// 读取标量。写入表从新到旧找：同一位置取其值；可能重叠的写入若只差对象（同一字段路径），Φ 判定两对象相等时取其值、
    /// 判定不等时跳过；其他情况内容不可判定（null）。
    /// 按对象是否相等分情况（分叉，或读经写的条件项）在语义上成立，但循环中每次迭代都会产生新的条件，路径或项指数增长，因此不做。
    /// </summary>
    public Term? ReadScalar(SideState side, Term location, Leaf leaf, bool freshFrame, ImmutableList<Term>? phi = null)
    {
        // 不可变的位置（长度、边界）：写入表里只有分配时的定义；未定义时读取项本身就是它的值。
        if (TermTable.Immutable(location))
        {
            foreach (var (written, value) in side.Writes)
                if (ReferenceEquals(written, location)) return value;
            return Terms.Read(0, location, leaf.Width, leaf.Bit);
        }
        // 显式布局的视图：由主叶子拼成。
        if (ViewOf(location) is var (root, overlay, view, all))
        {
            var parts = new Term[all.Length];
            for (var p = 0; p < all.Length; p++)
                if (!overlay.View[p] && overlay.Intersects(p, view))
                {
                    if (ReadScalar(side, Terms.Append(root, all[p].Path), all[p], freshFrame, phi) is not { } part) return null;
                    parts[p] = part;
                }
            return overlay.Compose(Terms, view, p => parts[p]);
        }
        for (var i = side.Writes.Count - 1; i >= 0; i--)
        {
            var (written, value) = side.Writes[i];
            if (ReferenceEquals(written, location)) return value;
            if (!MayOverlap(side, written, location)) continue;
            if (phi is null || SameObject(written, location) is not { } same) return null;
            var decided = solver.Decide(phi, same);
            if (decided == true) return value;
            if (decided is null) return null;
        }
        if (location.Root is RootKind.Field or RootKind.Element or RootKind.MultiElement && side.Fresh.Contains(location.Args[0]))
            return Terms.Constant(0, leaf.Width);
        if (location.Root == RootKind.Cell && freshFrame && location.Aux != 0) return Terms.Constant(0, leaf.Width);
        var version = location.Root == RootKind.Cell && !side.Exposed.Contains(CellOf(location)) ? 0 : side.Version;
        var read = Terms.Read(version, location, leaf.Width, leaf.Bit);
        read.Hint ??= leaf.Type;
        return read;
    }

    /// <summary>两个字段位置路径相同、只差对象时，“同一位置”的条件是两个对象相等。</summary>
    private Term? SameObject(Term x, Term y) =>
        x.Root == RootKind.Field && y.Root == RootKind.Field && ReferenceEquals(x.Key, y.Key) && !ReferenceEquals(x.Args[0], y.Args[0])
            ? Terms.Compare(Cond.Eq, x.Args[0], y.Args[0]) : null;

    public Term? ReadValue(SideState side, Term location, TypeRef type, bool freshFrame, ImmutableList<Term>? phi = null)
    {
        var failed = false;
        var value = Shape(type, l =>
        {
            var leafLocation = l.Path.Count == 0 ? location : Terms.Append(location, l.Path);
            var read = ReadScalar(side, leafLocation, l, freshFrame, phi);
            if (read is null) failed = true;
            return read ?? Terms.Constant(0, l.Width);
        });
        return failed ? null : value;
    }

    public void Write(SideState side, Term location, Term value, TypeRef type)
    {
        if (value.Kind == TermKind.Tuple && IsStruct(type))
        {
            var all = Leaves(type);
            if (all.Length == value.Args.Length)
            {
                for (var i = 0; i < all.Length; i++)
                    if (!Terms.IsView((DefinitionRef)type, i))
                        WriteScalar(side, all[i].Path.Count == 0 ? location : Terms.Append(location, all[i].Path), Fit(value.Args[i], all[i].Width));
                return;
            }
        }
        WriteScalar(side, location, value.Kind == TermKind.Tuple ? value : Fit(value, types.ValueWidth(type)));
    }

    /// <summary>值按类型的存储宽度保存（局部、返回值）：0/1 值存入 bool 时扩宽，与入口值、读取和调用结果同宽。</summary>
    public Term Stored(Term value, TypeRef type) => value.Kind == TermKind.Tuple ? value : Fit(value, types.ValueWidth(type));

    /// <summary>0/1 值存入更宽的存储（bool 字段）时扩成存储宽度，与经形参或读取得到的项同宽。</summary>
    private Term Fit(Term value, int width) => value.Bit && width > value.Width ? Terms.Widen(value, width) : value;

    private void WriteScalar(SideState side, Term location, Term value)
    {
        // 显式布局的视图：写到主叶子上。部分相交的主叶子原来的内容不可判定时，按视图位置写入（之后读取重叠的叶子不可判定）。
        if (ViewOf(location) is var (root, overlay, view, all)
            && overlay.Split(Terms, view, value, p => ReadScalar(side, Terms.Append(root, all[p].Path), all[p], false)) is { } parts)
        {
            foreach (var (p, part) in parts) WriteScalar(side, Terms.Append(root, all[p].Path), part);
            return;
        }
        // 覆盖同一位置的旧写入不再需要。
        var writes = side.Writes.RemoveAll(w => ReferenceEquals(w.Location, location));
        side.Writes = writes.Add((location, value));
        if (!Private(side, location)) Escape(side, value);
    }

    /// <summary>值进入公共存储或事件：其中的新对象逃逸，单元地址交出。</summary>
    public void Escape(SideState side, Term value)
    {
        foreach (var t in TermTable.Walk(value))
        {
            if (side.Fresh.Contains(t)) side.Fresh = side.Fresh.Remove(t);
            if (t.Kind == TermKind.Address && t.Location.Root == RootKind.Cell) side.Exposed = side.Exposed.Add(CellOf(t.Location));
        }
    }

    /// <summary>屏障：开始新的堆版本；不可变位置与私有存储的写入保留。</summary>
    public void Barrier(SideState side)
    {
        side.Version++;
        side.Writes = side.Writes.RemoveAll(w => !TermTable.Immutable(w.Location) && !Private(side, w.Location));
    }

    // ---- 推进 ----

    private Term Temp(Frame frame, int index) => frame.Temps[index] ?? throw new InvalidOperationException("临时量未定义");

    /// <summary>实参按形参的存储宽度：比较得到的 0/1 值传给 bool 形参时扩成 bool 的宽度，与形参的项同宽。</summary>
    private Term Argument(Term value, MethodRef method, int index)
    {
        if (!value.Bit || index >= method.Method.Parameters.Count) return value;
        var width = types.ValueWidth(method.Concrete(method.Method.Parameters[index].Type));
        return width > value.Width ? Terms.Widen(value, width) : value;
    }

    private Stop Fail(string reason) => new(StopKind.Fail) { Reason = reason };

    /// <summary>可能抛出：判定为真时抛出，判定不出时分叉（先走不抛出的一侧）。返回 null 表示继续。</summary>
    private Stop? Check(ImmutableList<Term> phi, Term condition, string exception)
    {
        var decided = solver.Decide(phi, condition);
        if (decided == false) return null;
        if (decided == true) return new Stop(StopKind.Throw) { Thrown = new ThrowInfo(exception, null) };
        var c = Terms.ToBit(condition);
        return new Stop(StopKind.Fork) { Alternatives = [Terms.Not(c), c] };
    }

    private Term NullTest(Term value) => Terms.Compare(Cond.Eq, value, Terms.Constant(0, value.Width));

    private const string NullReference = "System.NullReferenceException";
    private const string IndexOutOfRange = "System.IndexOutOfRangeException";
    private const string InvalidCast = "System.InvalidCastException";

    /// <summary>
    /// 位置项与它的隐式检查。位置取 Φ 下的规范形（<see cref="Solver.Fold"/>）：这条路径上已知相等的下标、对象写成同一个项，
    /// 写入表按规范形判定“必然相同”。
    /// </summary>
    private (Term? Location, Stop? Stop) Locate(SideState side, Frame frame, Place place, ImmutableList<Term> phi)
    {
        var (location, stop) = Address(side, frame, place, phi);
        return (location is null ? null : solver.Fold(phi, location), stop);
    }

    private (Term? Location, Stop? Stop) Address(SideState side, Frame frame, Place place, ImmutableList<Term> phi)
    {
        switch (place.Root)
        {
            case RootKind.Field:
                {
                    var obj = Temp(frame, place.Base);
                    if (Check(phi, NullTest(obj), NullReference) is { } stop) return (null, stop);
                    return (Terms.FieldRoot(obj, Terms.Path(place.Path)), null);
                }
            case RootKind.Static:
                {
                    var owner = ((DefinitionRef)place.Path[0].DeclaringType).Definition;
                    if (PreciseInit(owner) && !side.Initialized.Contains(owner))
                        return (null, new Stop(StopKind.Event) { Event = new EventInfo(EventKind.ClassInit, owner, null, [], false) });
                    return (Terms.StaticRoot(Terms.Path(place.Path)), null);
                }
            case RootKind.Element:
                {
                    var array = Temp(frame, place.Base);
                    if (Check(phi, NullTest(array), NullReference) is { } stop) return (null, stop);
                    var index = Temp(frame, place.Index);
                    var length = ReadScalar(side, Terms.LengthRoot(array), new Leaf(FieldPath.Empty, types.Int32, 32, false), false)!;
                    var narrow = index.IsOp(OpCode.Convert) && index.Conv is ConvKind.ZeroExtend or ConvKind.SignExtend && index.Args[0].Width == 32 ? index.Args[0] : index;
                    var inRange = narrow.Width == 32 ? Terms.Compare(Cond.Ult, narrow, length)
                        : Terms.Compare(Cond.Ult, narrow, Terms.Convert(ConvKind.ZeroExtend, length, narrow.Width));
                    if (Check(phi, Terms.Not(inRange), IndexOutOfRange) is { } bounds) return (null, bounds);
                    return (Terms.ElementRoot(array, index, Terms.Path(place.Path)), null);
                }
            case RootKind.MultiElement:
                {
                    var array = Temp(frame, place.Base);
                    if (Check(phi, NullTest(array), NullReference) is { } stop) return (null, stop);
                    var indices = place.Indices!.Select(i => Temp(frame, i)).ToArray();
                    var outside = Terms.Operation(OpCode.OutOfRange, 0, 1, null, [array, .. indices]);
                    if (Check(phi, outside, IndexOutOfRange) is { } bounds) return (null, bounds);
                    return (Terms.MultiElementRoot(array, indices, Terms.Path(place.Path)), null);
                }
            case RootKind.Reference:
                return (Terms.ReferenceRoot(Temp(frame, place.Base), Terms.Path(place.Path)), null);
            case RootKind.Cell:
                return (Terms.CellRoot(frame.Id, place.Local!.Variable, Terms.Path(place.Path)), null);
            case RootKind.Length:
            case RootKind.StringLength:
            case RootKind.Bound:
                {
                    var obj = Temp(frame, place.Base);
                    if (Check(phi, NullTest(obj), NullReference) is { } stop) return (null, stop);
                    return (place.Root switch
                    {
                        RootKind.Length => Terms.LengthRoot(obj),
                        RootKind.StringLength => Terms.StringLengthRoot(obj),
                        _ => Terms.BoundRoot(obj, place.Index / 2, place.Index % 2 == 1),
                    }, null);
                }
            default:
                return (null, Fail($"位置 {place.Root}"));
        }
    }

    /// <summary>局部变量的值：环境、可取址的单元或入口值。</summary>
    private Term? LocalTerm(SideState side, Frame frame, LocalValue local)
    {
        if (frame.Program.Cells.Contains(local.Variable))
            return ReadValue(side, Terms.CellRoot(frame.Id, local.Variable, FieldPath.Empty), local.Type, frame.Fresh);
        if (frame.Env.TryGetValue(local.Variable, out var value)) return value;
        if (frame.Fresh || side.Entry is null || frame != side.Frames[0]) return null;
        value = side.Entry(local);
        frame.Env = frame.Env.SetItem(local.Variable, value);
        return value;
    }

    private void AssignLocal(SideState side, Frame frame, LocalValue local, Term value)
    {
        if (frame.Program.Cells.Contains(local.Variable)) Write(side, Terms.CellRoot(frame.Id, local.Variable, FieldPath.Empty), value, local.Type);
        else frame.Env = frame.Env.SetItem(local.Variable, Stored(value, local.Type));
    }

    /// <summary>推进到下一个观察点。已停在观察点时不动。</summary>
    public Stop Advance(SideState side, ImmutableList<Term> phi)
    {
        if (side.Stop is { } stopped) return stopped;
        return side.Stop = Run(side, phi);
    }

    private Stop Run(SideState side, ImmutableList<Term> phi)
    {
        if (side.EntryCheck is { } checkedReceiver)
        {
            if (Check(phi, NullTest(checkedReceiver), NullReference) is { } entryStop) return entryStop;
            side.EntryCheck = null;
        }
        while (true)
        {
            if (++side.Steps > StepBudget) return Fail("步数超过预算");
            if (Meter?.Spend() == true) return Fail("尝试的总步数超过预算");
            var frame = side.Top;
            var program = frame.Program;
            var unit = program.Units[frame.Unit];
            if (frame.Op >= unit.Ops.Length) return Fail("块没有终结");
            var op = unit.Ops[frame.Op];
            side.NoteStatement(program, frame, op);
            var trace = side.Frames.Count == 1 ? side.Current : null;
            switch (op)
            {
                case LocalOp local:
                    {
                        if (LocalTerm(side, frame, local.Local) is not { } value)
                            return Fail(frame.Program.Cells.Contains(local.Local.Variable) ? "局部单元的读取不可判定" : $"局部 {local.Local.Variable} 未定义");
                        frame.Temps[local.Target] = value;
                        trace?.Nodes.TryAdd(local.Local, value);
                        break;
                    }
                case PureOp pure:
                    {
                        var operands = pure.Operands.Select(t => Temp(frame, t)).ToArray();
                        if (pure.Node is BinaryValue { Op: BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem } division)
                        {
                            if (Check(phi, NullTest(operands[1]), "System.DivideByZeroException") is { } zero) return zero;
                            if (division.Op is BinOp.SDiv or BinOp.SRem && !(operands[1].IsConstant && operands[1].Bits != TermTable.Mask(operands[1].Width)))
                            {
                                var overflow = Terms.Operation(OpCode.DivOverflow, 0, 1, null, operands[0], operands[1]);
                                if (Check(phi, overflow, "System.OverflowException") is { } over) return over;
                            }
                        }
                        if (Pure(side, frame, pure.Node, operands) is not { } value) return Fail($"不能解释的值 {pure.Node.GetType().Name}");
                        if (value.Hint is null && frame == side.Frames[0] && side.Entry is not null) value.Hint = pure.Node.Type;
                        frame.Temps[pure.Target] = value;
                        trace?.Nodes.TryAdd(pure.Node, value);
                        break;
                    }
                case LoadOp load:
                    {
                        var (location, stop) = Locate(side, frame, load.Place, phi);
                        if (stop is not null) return stop;
                        Term? value;
                        if (load.Place.Root == RootKind.Cell && !program.Cells.Contains(load.Place.Local!.Variable))
                        {
                            if (LocalTerm(side, frame, load.Place.Local) is not { } whole) return Fail($"局部 {load.Place.Local.Variable} 未定义");
                            value = Project(whole, load.Place.Path, load.Place.Type);
                            if (value is null) return Fail("结构体局部的字段不能投影");
                        }
                        else if ((value = ReadValue(side, location!, load.Place.Type, frame.Fresh, phi)) is null)
                            return Fail($"读取 {location} 的别名不可判定");
                        frame.Temps[load.Target] = value;
                        if (trace is not null)
                        {
                            trace.Nodes.TryAdd(load.Node, value);
                            if (load.Node is FieldValue { Pending: not null } or StaticFieldValue { Pending: not null }) trace.Pending = true;
                        }
                        break;
                    }
                case ProjectOp project:
                    {
                        var source = Temp(frame, project.Source);
                        if (Project(source, [project.Field], project.Node.Type) is not { } value) return Fail("结构体值的字段不能投影");
                        frame.Temps[project.Target] = value;
                        trace?.Nodes.TryAdd(project.Node, value);
                        break;
                    }
                case AddressOp address:
                    {
                        var (location, stop) = Locate(side, frame, address.Place, phi);
                        if (stop is not null) return stop;
                        var value = Terms.Address(location!);
                        frame.Temps[address.Target] = value;
                        trace?.Nodes.TryAdd(address.Node, value);
                        break;
                    }
                case CheckedOp check:
                    {
                        var operand = Temp(frame, check.Operand);
                        Term value;
                        switch (check.Node)
                        {
                            case CheckedCastValue cast:
                                {
                                    var fails = Terms.Operation(OpCode.CastFails, 0, 1, cast.Target, operand);
                                    if (!(operand.IsConstant && operand.Bits == 0) && Check(phi, fails, InvalidCast) is { } stop) return stop;
                                    value = operand;
                                    break;
                                }
                            case UnboxValue unbox when ManagedTypes.IsReferenceType(unbox.Target):
                                {
                                    var fails = Terms.Operation(OpCode.CastFails, 0, 1, unbox.Target, operand);
                                    if (!(operand.IsConstant && operand.Bits == 0) && Check(phi, fails, InvalidCast) is { } stop) return stop;
                                    value = operand;
                                    break;
                                }
                            case UnboxValue unbox:
                                {
                                    if (Check(phi, NullTest(operand), NullReference) is { } stop) return stop;
                                    var fails = Terms.Operation(OpCode.UnboxFails, 0, 1, unbox.Target, operand);
                                    if (Check(phi, fails, InvalidCast) is { } wrong) return wrong;
                                    var content = Terms.ReferenceRoot(Terms.Operation(OpCode.UnboxAddress, 0, 64, unbox.Target, operand), FieldPath.Empty);
                                    if (ReadValue(side, content, unbox.Target, false) is not { } read) return Fail("装箱内容的读取不可判定");
                                    value = read;
                                    break;
                                }
                            case UnboxAddressValue unbox:
                                {
                                    if (Check(phi, NullTest(operand), NullReference) is { } stop) return stop;
                                    var fails = Terms.Operation(OpCode.UnboxFails, 0, 1, unbox.Target, operand);
                                    if (Check(phi, fails, InvalidCast) is { } wrong) return wrong;
                                    value = Terms.Operation(OpCode.UnboxAddress, 0, 64, unbox.Target, operand);
                                    break;
                                }
                            default:
                                return Fail("未知的检查转换");
                        }
                        frame.Temps[check.Target] = value;
                        trace?.Nodes.TryAdd(check.Node, value);
                        break;
                    }
                case ValueEventOp evt:
                    return new Stop(StopKind.Event) { Event = ValueEvent(frame, evt) };
                case CallOp call:
                    {
                        var invocation = call.Call.Invocation;
                        var receiver = call.Receiver >= 0 ? Temp(frame, call.Receiver) : null;
                        if (receiver is not null && invocation.Virtual && Check(phi, NullTest(receiver), NullReference) is { } stop) return stop;
                        return new Stop(StopKind.Event)
                        {
                            Event = new EventInfo(EventKind.Call, invocation.Method, receiver,
                                call.Arguments.Select((t, i) => Argument(Temp(frame, t), invocation.Method, i)).ToArray(), invocation.Virtual)
                            {
                                Constraint = invocation.Constraint,
                                ResultType = call.Call.Result?.Type,
                                Inlined = call.Call.Inlined,
                            },
                        };
                    }
                case StoreOp store:
                    {
                        var (location, stop) = Locate(side, frame, store.Place, phi);
                        if (stop is not null) return stop;
                        var value = Temp(frame, store.Value);
                        // 引用类型数组元素的存储检查（数组协变）；元素类型是 sealed 类时数组的运行时类型只能正好是它的数组，存入不会失败。
                        if (store.Place.Root == RootKind.Element && ManagedTypes.IsReferenceType(store.Place.Type) && !(value.IsConstant && value.Bits == 0)
                            && !(store.Place.Type is DefinitionRef { Definition.Attributes: var attributes } && (attributes & System.Reflection.TypeAttributes.Sealed) != 0))
                        {
                            var mismatch = Terms.Operation(OpCode.CastFails, 1, 1, "array-store", location!.Args[0], value);
                            if (Check(phi, mismatch, "System.ArrayTypeMismatchException") is { } wrong) return wrong;
                        }
                        if (store.Place.Root == RootKind.Cell && !program.Cells.Contains(store.Place.Local!.Variable))
                        {
                            var local = store.Place.Local;
                            if (LocalTerm(side, frame, local) is not { } whole) return Fail($"局部 {local.Variable} 未定义");
                            if (Update(whole, store.Place.Path, value) is not { } updated) return Fail("结构体局部的字段不能更新");
                            frame.Env = frame.Env.SetItem(local.Variable, updated);
                        }
                        else Write(side, location!, value, store.Place.Type);
                        if (trace is not null && program.Blocks[program.Units[frame.Unit].Block].Statements[store.Statement] is ManagedStore { Target: FieldValue { Pending: not null } or StaticFieldValue { Pending: not null } })
                            trace.Pending = true;
                        break;
                    }
                case AssignOp assign:
                    AssignLocal(side, frame, assign.Target, Temp(frame, assign.Value));
                    break;
                case CheckOp check:
                    {
                        var exception = check.Exception.Method.Owner.FullName;
                        if (Check(phi, Temp(frame, check.Condition), exception) is { } stop) return stop;
                        break;
                    }
                case BranchOp branch:
                    {
                        var condition = Temp(frame, branch.Condition);
                        var decided = solver.Decide(phi, condition);
                        if (decided is null)
                        {
                            var c = Terms.ToBit(condition);
                            return new Stop(StopKind.Fork) { Alternatives = [c, Terms.Not(c)] };
                        }
                        frame.Unit = decided.Value ? branch.Taken : branch.Fallthrough;
                        frame.Op = 0;
                        continue;
                    }
                case SwitchOp table:
                    {
                        var index = Temp(frame, table.Index);
                        var chosen = -1;
                        var open = new List<Term>();
                        for (var k = 0; k < table.Cases.Length; k++)
                        {
                            var test = Terms.Compare(Cond.Eq, index, Terms.Constant((ulong)k, index.Width));
                            var decided = solver.Decide(phi, test);
                            if (decided == true) { chosen = k; break; }
                            if (decided is null) open.Add(test);
                        }
                        if (chosen < 0 && open.Count == 0) return Fail("跳转表下标越界");
                        if (chosen < 0) return new Stop(StopKind.Fork) { Alternatives = open.ToArray() };
                        frame.Unit = table.Cases[chosen];
                        frame.Op = 0;
                        continue;
                    }
                case JumpOp jump:
                    frame.Unit = jump.Unit;
                    frame.Op = 0;
                    continue;
                case CopyOp copy:
                    {
                        var values = copy.Values.Select(t => Temp(frame, t)).ToArray();
                        for (var i = 0; i < copy.Targets.Length; i++) AssignLocal(side, frame, copy.Targets[i], values[i]);
                        break;
                    }
                case GotoOp jump:
                    {
                        frame.Unit = program.BlockUnits[jump.Block];
                        frame.Op = 0;
                        if (side.Frames.Count == 1 && side.Unchanged is { } unchanged && unchanged.Contains(jump.Block) && side.Resumed != jump.Block)
                            return new Stop(StopKind.Soft) { Block = jump.Block };
                        side.Resumed = null;
                        continue;
                    }
                case ReturnOp ret:
                    {
                        var value = ret.Value >= 0 ? Temp(frame, ret.Value) : null;
                        if (value is not null && frame.ConstructedType is null) value = Stored(value, frame.Program.Method.Concrete(frame.Program.Method.Method.ReturnType));
                        if (side.Frames.Count == 1) return new Stop(StopKind.Return) { Value = value };
                        if (frame.ConstructedType is { } constructed)
                            value = ManagedTypes.IsReferenceType(constructed) ? frame.Constructed
                                : ReadValue(side, frame.Constructed!.Location, constructed, true);
                        if (value is null && frame.ConstructedType is not null) return Fail("构造的值不可判定");
                        side.Frames.RemoveAt(side.Frames.Count - 1);
                        Finish(side, side.Top, value);
                        continue;
                    }
                case ThrowOp thrown:
                    {
                        var exception = Temp(frame, thrown.Value);
                        return new Stop(StopKind.Throw) { Thrown = new ThrowInfo(null, exception) };
                    }
                case UnsupportedOp unsupported:
                    return Fail(unsupported.Reason);
                default:
                    return Fail($"未知操作 {op.GetType().Name}");
            }
            frame.Op++;
        }
    }

    /// <summary>解释纯值。</summary>
    private Term? Pure(SideState side, Frame frame, ManagedValue node, Term[] o)
    {
        switch (node)
        {
            case ConstantValue constant:
                return IsStruct(constant.Type) ? Zero(constant.Type) : Terms.Constant(constant.Bits, constant.Width);
            case ArgumentValue argument:
                return frame.Arguments[argument.Index + 1];
            case StringValue text:
                return Terms.Atom(AtomKind.Text, text.Text, 64);
            case TypeHandleValue or SizeOfValue or FieldHandleValue or MethodHandleValue:
                return Terms.Atom(AtomKind.Token, node, node.Width);
            case BinaryValue binary:
                return Terms.Binary(binary.Op, o[0], o[1], binary.Width);
            case UnaryValue unary:
                return Terms.Unary(unary.Op, o[0], unary.Width);
            case ConversionValue conversion:
                return Terms.Convert(conversion.Kind, o[0], conversion.Width);
            case ComparisonValue comparison:
                return Terms.Compare(comparison.Condition, o[0], o[1]);
            case ChoiceValue choice:
                {
                    if (o[1].Kind == TermKind.Tuple && o[2].Kind == TermKind.Tuple && o[1].Args.Length == o[2].Args.Length)
                        return Terms.Tuple((DefinitionRef)o[1].Key!, o[1].Args.Zip(o[2].Args, (a, b) => Terms.Choice(o[0], a, b, a.Width)).ToArray());
                    return Terms.Choice(o[0], o[1], o[2], choice.Width);
                }
            case BooleanValue boolean:
                return boolean.IsAnd ? Terms.And(o[0], o[1]) : Terms.Or(o[0], o[1]);
            case NegatedValue:
                return Terms.Not(o[0]);
            case IsInstValue isinst:
                return o[0].IsConstant && o[0].Bits == 0 ? o[0] : Terms.Operation(OpCode.IsInst, 0, 64, isinst.Target, o[0]);
            case PinnedArrayValue:
                return Terms.Operation(OpCode.Pin, 0, 64, null, o[0]);
            case PointerOffsetValue:
                return Terms.Binary(BinOp.Add, o[0], o[1].Width == 64 ? o[1] : Terms.Convert(ConvKind.SignExtend, o[1], 64), 64);
            case ComposedValue composed:
                {
                    // 没有叶子的组成值是类型的零值（default(T)，T 可以是类型形参）。
                    if (composed.Leaves.Count == 0) return Zero(composed.StructType);
                    if (composed.StructType is not DefinitionRef structure) return null;
                    var value = Zero(structure);
                    for (var i = 0; i < composed.Leaves.Count; i++)
                        if (Update(value, composed.Leaves[i].Path, o[i]) is { } updated) value = updated;
                        else return null;
                    return value;
                }
            default:
                return null;
        }
    }

    private EventInfo ValueEvent(Frame frame, ValueEventOp op)
    {
        var o = op.Operands.Select(t => Temp(frame, t)).ToArray();
        return op.Node switch
        {
            StaticCallValue call => new EventInfo(EventKind.Call, call.Method, null, [], false) { ResultType = call.Type, Inlined = call.Inlined },
            NewObjectValue created => new EventInfo(EventKind.Construct, created.Constructor, null, o, false) { ResultType = created.Type, Inlined = created.Transparent },
            NewArrayValue array => new EventInfo(EventKind.NewArray, array.ArrayType, null, o, false) { ResultType = array.Type },
            NewMultiArrayValue array => new EventInfo(EventKind.NewMultiArray, array.ArrayType, null, o, false) { ResultType = array.Type },
            BoxValue box => new EventInfo(EventKind.Box, box.Boxed, null, o, false) { ResultType = box.Type },
            DelegateValue d => new EventInfo(EventKind.Delegate, (d.DelegateType, d.Method, d.Binding), null, o, false) { ResultType = d.Type },
            _ => throw new InvalidOperationException(op.Node.ToString()),
        };
    }

    /// <summary>事件的结果项（结构体按叶子）。</summary>
    public Term? Result(EventInfo evt, int serial)
    {
        if (evt.ResultType is not { } type || ManagedTypes.IsVoid(type)) return null;
        return Shape(type, l => Terms.Atom(AtomKind.Result, l.Path.Count == 0 ? serial : (serial, l.Path.Id), l.Width, l.Bit));
    }

    /// <summary>
    /// 两侧对应的事件完成：操作数中的新对象逃逸、单元交出，屏障开始新的堆版本，分配的新对象登记，结果写入。
    /// </summary>
    public void Complete(SideState side, EventInfo evt, Term? result)
    {
        foreach (var operand in evt.Operands) Escape(side, operand);
        if (evt.Barrier) Barrier(side);
        side.Events++;
        if (evt.Kind == EventKind.ClassInit) side.Initialized = side.Initialized.Add((TypeDef)evt.Identity);
        if (evt.Allocates && result is not null)
        {
            solver.Allocations.Add(result);
            side.Fresh = side.Fresh.Add(result);
            if (evt.Kind == EventKind.NewArray)
                side.Writes = side.Writes.Add((Terms.LengthRoot(result), Terms.Convert(ConvKind.Truncate, evt.Arguments[0], 32)));
        }
        side.Stop = null;
        if (evt.Kind == EventKind.ClassInit) return;
        if (evt.Kind == EventKind.Allocate)
        {
            if (side.PendingConstruct is { } pending)
            {
                side.PendingConstruct = null;
                Unfold(side, pending.Template, pending.Event, result);
            }
            else if (side.AllocationTarget is { } target)
            {
                side.AllocationTarget = null;
                AssignLocal(side, side.Frames[0], target, result!);
            }
            return;
        }
        Finish(side, side.Top, result);
    }

    /// <summary>展开构造：引用类型先停在分配事件上，分配完成后压入构造函数的帧；值类型直接压帧。</summary>
    public void BeginConstruct(SideState side, Program template, EventInfo evt)
    {
        var type = template.Method.DeclaringType;
        if (!ManagedTypes.IsReferenceType(type))
        {
            Unfold(side, template, evt, null);
            return;
        }
        side.PendingConstruct = (template, evt);
        side.Stop = new Stop(StopKind.Event) { Event = new EventInfo(EventKind.Allocate, type, null, [], false) { ResultType = type } };
    }

    /// <summary>帧停在事件（调用或值事件）上，以结果完成它并前进。</summary>
    public void Finish(SideState side, Frame frame, Term? result)
    {
        var op = frame.Program.Units[frame.Unit].Ops[frame.Op];
        switch (op)
        {
            case CallOp call when call.Call.Result is { } target && result is not null:
                AssignLocal(side, frame, target, result);
                break;
            case ValueEventOp value:
                frame.Temps[value.Target] = result ?? Terms.Constant(0, 64);
                if (side.Frames.Count == 1) side.Current?.Nodes.TryAdd(value.Node, frame.Temps[value.Target]);
                break;
        }
        frame.Op++;
    }

    /// <summary>
    /// 以模板展开停着的调用：压入被调方法的帧。构造先分配（引用类型）或建立存放新值的单元（值类型）。
    /// </summary>
    public void Unfold(SideState side, Program template, EventInfo evt, Term? allocated)
    {
        var method = template.Method;
        var definition = method.Method;
        var id = NewFrameId();
        Term? receiver = evt.Receiver;
        Term? constructed = null;
        TypeRef? constructedType = null;
        if (evt.Kind == EventKind.Construct)
        {
            constructedType = method.DeclaringType;
            if (ManagedTypes.IsReferenceType(constructedType)) receiver = constructed = allocated;
            else
            {
                var cell = Terms.CellRoot(id, new Variable(Storage.Temp(int.MaxValue), 1), FieldPath.Empty);
                constructed = Terms.Address(cell);
                receiver = constructed;
            }
        }
        var arguments = new Term[definition.Parameters.Count + 1];
        arguments[0] = receiver ?? Terms.Zero64;
        for (var i = 0; i < definition.Parameters.Count && i < evt.Arguments.Length; i++) arguments[i + 1] = evt.Arguments[i];
        side.Frames.Add(new Frame
        {
            Program = template, Id = id, Unit = template.BlockUnits[template.Entry], Op = 0,
            Arguments = arguments, Temps = new Term[Math.Max(1, template.Temps)], Fresh = true,
            Constructed = constructed, ConstructedType = constructedType,
        });
        side.Stop = null;
        if (constructedType is not null && !ManagedTypes.IsReferenceType(constructedType))
            Write(side, constructed!.Location, Zero(constructedType), constructedType);
        // 进入精确初始化类型的静态方法先触发类初始化（实例构造与值类型方法的触发不建模）。
        if (definition.IsStatic && PreciseInit(definition.Owner) && !side.Initialized.Contains(definition.Owner))
            side.Stop = new Stop(StopKind.Event) { Event = new EventInfo(EventKind.ClassInit, definition.Owner, null, [], false) };
    }
}
