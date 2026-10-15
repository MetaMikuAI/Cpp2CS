using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Runtime;

/// <summary>副本匹配结果。Distance 为归一化语句序列的编辑距离，0 表示逐条相同。</summary>
public sealed record CopyMatch(IReadOnlyList<ulong> Originals, int Distance)
{
    public bool Exact => Distance == 0;
}

/// <summary>
/// 托管方法的脱离副本：C++ 编译器没有内联的托管方法在其他编译单元留下的拷贝，不在方法指针表中。
/// 逐条比较归一化的语句：常量寄存器值按顺序代入（adrp+add/ldr 折成完整地址，写常量的赋值不单独比较）；
/// 分支目标按在函数内的名次比较；零填充区（.bss，如每份拷贝自己的 s_Il2CppMethodInitialized 标志）
/// 地址按出现顺序一一对应；其余常量（GOT 槽、被调函数、字面量）必须相同。
/// 顺序代入跨越了分支，但比较双方结构相同，所以这种不精确在两侧一致。
/// 候选限定为外部引用（被调函数、按常量地址读写的全局位置）集合相同、大小相差不超过 32 字节的托管方法；
/// 逐条相同为精确匹配，否则取编辑距离最小者（启发式：同一源码在不同编译单元的指令选择与寄存器分配可能不同，
/// 例如布尔标志用 cbnz 或 tbnz #0 判断、GOT 值留在被调用者保存寄存器或重新读取）。
/// 引用了全局数据（元数据用量槽等，方法特有）时允许距离到语句数的 1/3，否则只到 1/32。
/// </summary>
public sealed class ManagedCopies(IMachine machine, FunctionTable functions, ProgramModel model)
{
    private const int MaxStatements = 4096;
    private const ulong SizeWindow = 32;
    private const int MaxDistance = 64;
    private const ulong RelativeTag = 1UL << 62;
    private const ulong WildcardTag = 1UL << 61;

    internal sealed record Shape(string[] Statements, string References, bool ReferencesData);

    private (ulong Size, ulong Address)[]? bySize;
    private readonly Dictionary<ulong, Shape?> shapes = new();
    private readonly Dictionary<ulong, CopyMatch?> matches = new();

    /// <summary>与 target 匹配的托管方法（可能多个：代码相同的不同方法）；不是副本或无法比较时返回 null。</summary>
    public CopyMatch? Match(ulong target)
    {
        if (matches.TryGetValue(target, out var cached)) return cached;
        CopyMatch? result = null;
        if (!model.Code.ContainsKey(target) && functions.At(target) is { } range && range.Start == target && ShapeOf(range) is { } shape)
        {
            // 没有方法特有的数据引用时几乎只靠语句比较：短函数只接受精确匹配，一两条之差足以把桩函数配成空方法
            var limit = Math.Min(MaxDistance, shape.Statements.Length / (shape.ReferencesData ? 3 : 32));
            var best = limit + 1;
            var originals = new List<ulong>();
            foreach (var candidate in Candidates(range.End - range.Start))
            {
                if (ShapeOf(functions.At(candidate)!) is not { } other || other.References != shape.References) continue;
                var distance = EditDistance(shape.Statements, other.Statements, Math.Min(limit, best));
                if (distance > best || distance > limit) continue;
                if (distance < best)
                {
                    best = distance;
                    originals.Clear();
                }
                originals.Add(candidate);
            }
            if (originals.Count > 0) result = new CopyMatch(originals, best);
        }
        return matches[target] = result;
    }

    private IEnumerable<ulong> Candidates(ulong size)
    {
        bySize ??= model.Code.Keys
            .Where(a => functions.At(a) is { } r && r.Start == a)
            .Select(a => (functions.At(a)!.End - a, a))
            .Order()
            .ToArray();
        var low = size > SizeWindow ? size - SizeWindow : 0;
        var index = Array.BinarySearch(bySize, (low, 0UL));
        if (index < 0) index = ~index;
        for (; index < bySize.Length && bySize[index].Size <= size + SizeWindow; index++) yield return bySize[index].Address;
    }

    internal Shape? ShapeOf(ulong start) => functions.At(start) is { } range && range.Start == start ? ShapeOf(range) : null;

    /// <summary>归一化的语句序列与外部引用；无法读取或超长时返回 null。寄存器跳转按原文比较（跳转表地址随副本变化，只会漏配不会错配）。</summary>
    private Shape? ShapeOf(FunctionRange range)
    {
        if (shapes.TryGetValue(range.Start, out var cached)) return cached;
        Shape? shape = null;
        if (Evaluate(range) is { } evaluated)
        {
            var labels = evaluated
                .SelectMany(s => s switch { Jump j => [j.Target], Branch b => new[] { b.Target, b.Fallthrough }, _ => [] })
                .Where(t => t >= range.Start && t < range.End)
                .Distinct().Order()
                .Select((t, i) => (t, i)).ToDictionary(p => p.t, p => p.i);
            var wildcards = new Dictionary<ulong, ulong>();
            var calls = new SortedSet<ulong>();
            var data = new SortedSet<ulong>();
            var statements = new string[evaluated.Count];
            for (var i = 0; i < evaluated.Count; i++)
            {
                CollectReferences(evaluated[i], range, calls, data);
                var normalized = ExprMap.MapOperands(evaluated[i], e => ExprMap.Map(e, x => x is Const { Width: 64 } c ? new Const(Key(c.Value, range, wildcards), 64) : null));
                statements[i] = normalized switch
                {
                    Jump jump => $"goto {Label(jump.Target, labels)}",
                    Branch branch => $"if {branch.Condition} goto {Label(branch.Target, labels)} else {Label(branch.Fallthrough, labels)}",
                    _ => normalized.ToString(),
                };
            }
            shape = new Shape(statements, string.Join(",", calls.Select(r => r.ToString("x"))) + ";" + string.Join(",", data.Select(r => r.ToString("x"))), data.Count > 0);
        }
        shapes[range.Start] = shape;
        return shape;
    }

    /// <summary>按顺序提升并代入常量寄存器值；写常量到寄存器的赋值不保留。</summary>
    private List<Stmt>? Evaluate(FunctionRange range)
    {
        var constants = new Dictionary<Storage, Const>();
        Expr Eval(Expr e) => Fold.Simplify(ExprMap.Map(e, x => x is Read read && constants.TryGetValue(read.Storage, out var c)
            ? Fold.Convert(ConvKind.Truncate, c, read.Width)
            : null));
        var output = new List<Stmt>();
        var statements = new List<Stmt>();
        for (var address = range.Start; address < range.End;)
        {
            statements.Clear();
            var size = machine.Lift(address, statements);
            if (size == 0 || output.Count > MaxStatements) return null;
            foreach (var stmt in statements)
            {
                if (stmt is Assign { Target.Bank: not Bank.Flags } constant && Eval(constant.Value) is Const c)
                {
                    constants[constant.Target] = new Const(c.Value, constant.Target.Width);
                    continue;
                }
                output.Add(ExprMap.MapOperands(stmt, Eval));
                switch (stmt)
                {
                    case Assign assign:
                        constants.Remove(assign.Target);
                        break;
                    case Call:
                        foreach (var storage in machine.Convention.Clobbered) constants.Remove(storage);
                        break;
                    case Opaque:
                        constants.Clear();
                        break;
                }
            }
            address += (ulong)size;
        }
        return output;
    }

    /// <summary>外部引用：直接调用目标与按常量地址读写的全局位置（不含函数自身与零填充区）。</summary>
    private void CollectReferences(Stmt stmt, FunctionRange range, SortedSet<ulong> calls, SortedSet<ulong> data)
    {
        bool External(ulong value) => (value < range.Start || value >= range.End) && machine.Image.Resolve(value).Kind != AddressKind.ZeroFill;
        if (stmt is Call { Target: Const target } && External(target.Value)) calls.Add(target.Value);
        if (stmt is Jump jump && External(jump.Target)) calls.Add(jump.Target);
        if (stmt is Store { Target: Const store } && External(store.Value)) data.Add(store.Value);
        foreach (var e in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk))
            if (e is Load { Address: Const load } && External(load.Value)) data.Add(load.Value);
    }

    private ulong Key(ulong value, FunctionRange range, Dictionary<ulong, ulong> wildcards)
    {
        if (value >= range.Start && value < range.End) return RelativeTag | (value - range.Start);
        if (machine.Image.Resolve(value).Kind == AddressKind.ZeroFill)
        {
            if (!wildcards.TryGetValue(value, out var id)) wildcards[value] = id = (ulong)wildcards.Count;
            return WildcardTag | id;
        }
        return value;
    }

    private static string Label(ulong target, Dictionary<ulong, int> labels) => labels.TryGetValue(target, out var label) ? $"L{label}" : $"0x{target:x}";

    /// <summary>限宽 limit 的编辑距离；超过 limit 时返回 limit + 1。</summary>
    internal static int EditDistance(string[] a, string[] b, int limit)
    {
        if (Math.Abs(a.Length - b.Length) > limit) return limit + 1;
        const int Infinity = int.MaxValue / 2;
        var width = 2 * limit + 1;
        var previous = new int[width];
        var current = new int[width];
        // 第 i 行的第 k 格对应 j = i - limit + k
        for (var k = 0; k < width; k++)
        {
            var j = k - limit;
            previous[k] = j >= 0 && j <= b.Length ? j : Infinity;
        }
        for (var i = 1; i <= a.Length; i++)
        {
            var rowMin = Infinity;
            for (var k = 0; k < width; k++)
            {
                var j = i - limit + k;
                if (j < 0 || j > b.Length)
                {
                    current[k] = Infinity;
                    continue;
                }
                // 删除 a[i-1]：(i-1, j) 在上一行后一格
                var value = k + 1 < width ? previous[k + 1] + 1 : Infinity;
                if (j == 0) value = Math.Min(value, i);
                else
                {
                    // 替换或相同：(i-1, j-1) 在上一行同一格；插入 b[j-1]：(i, j-1) 在本行前一格
                    value = Math.Min(value, previous[k] + (a[i - 1] == b[j - 1] ? 0 : 1));
                    if (k > 0) value = Math.Min(value, current[k - 1] + 1);
                }
                current[k] = value;
                rowMin = Math.Min(rowMin, value);
            }
            if (rowMin > limit) return limit + 1;
            (previous, current) = (current, previous);
        }
        return Math.Min(previous[b.Length - a.Length + limit], limit + 1);
    }
}
