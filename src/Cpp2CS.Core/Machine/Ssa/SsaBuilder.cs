using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Ssa;

using Storage = Cpp2CS.Ir.Storage;

/// <summary>调用与返回的数据流约定：调用读取哪些存储、把结果写到哪里、破坏哪些存储。</summary>
public interface ICallModel
{
    IReadOnlyList<Storage> Reads(Call call);
    IReadOnlyList<Storage> Results(Call call);
    IReadOnlyList<Storage> Clobbers(Call call);
}

/// <summary>不知道被调用者签名时的保守约定：读全部参数寄存器，写全部结果寄存器。</summary>
public sealed class ConservativeCallModel(CallingConvention convention) : ICallModel
{
    private readonly Storage[] reads = [.. convention.IntegerArguments, .. convention.IndirectResult is { } x8 ? [x8] : Array.Empty<Storage>(), .. convention.FloatArguments];
    private readonly Storage[] results = [.. convention.IntegerResults, .. convention.FloatResults];

    public IReadOnlyList<Storage> Reads(Call call) => reads;
    public IReadOnlyList<Storage> Results(Call call) => call.Kind is CallKind.Tail or CallKind.TailIndirect ? [] : results;
    public IReadOnlyList<Storage> Clobbers(Call call) => convention.Clobbered;
}

/// <summary>
/// 构建剪枝 SSA（Cytron 等，按活跃性剪枝）。只处理 include 选中的存储单元，其余语句原样保留，
/// 因此同一构建器先用于寄存器，栈槽提升之后再用于栈槽。
/// 约定：版本 0 为入口值；版本 -1 为调用破坏后的未定义值，使用处直接成为 Unknown；
/// 入口 SP 读作 FrameAddress(0)。
/// </summary>
public sealed class SsaBuilder
{
    private readonly MachineFunction function;
    private readonly Func<Storage, bool> include;
    private readonly ICallModel calls;
    private readonly Storage stackPointer;
    private readonly Dominators dominators;
    private readonly Dictionary<Storage, int> index = new();
    private readonly List<Storage> storages = [];
    private readonly Dictionary<Storage, int> counters = new();

    private SsaBuilder(MachineFunction function, Dominators dominators, Func<Storage, bool> include, ICallModel calls, Storage stackPointer)
    {
        this.function = function;
        this.dominators = dominators;
        this.include = include;
        this.calls = calls;
        this.stackPointer = stackPointer;
    }

    /// <summary>
    /// 先把调用的参数/结果按 calls 填好（尚未填写过的调用）、返回语句按 returnValue 填好，再构建 SSA。
    /// </summary>
    public static void Build(MachineFunction function, Dominators dominators, Func<Storage, bool> include, ICallModel calls, Storage stackPointer)
    {
        if (function.Blocks[0].Predecessors.Count > 0) throw new InvalidOperationException("入口块有前驱，SSA 需要独立的起始块");
        new SsaBuilder(function, dominators, include, calls, stackPointer).Run();
    }

    /// <summary>按调用模型填写调用读取的参数与结果存储，按签名填写返回值。只处理尚未填写的调用。</summary>
    public static void PrepareCalls(MachineFunction function, ICallModel calls, Expr? returnValue)
    {
        foreach (var block in function.Blocks)
        {
            for (var i = 0; i < block.Statements.Count; i++)
            {
                block.Statements[i] = block.Statements[i] switch
                {
                    Call { Arguments.Length: 0, Results.Length: 0 } call => call with
                    {
                        Arguments = calls.Reads(call).Select(s => (Expr)new Read(s, s.Width)).ToArray(),
                        Sources = calls.Reads(call).ToArray(),
                        Results = calls.Results(call).ToArray(),
                    },
                    Return { Value: null, Pieces.Length: 0, Buffer: null } ret when returnValue is not null => ret with { Value = returnValue },
                    var other => other,
                };
            }
        }
    }

    private int Id(Storage storage)
    {
        if (!index.TryGetValue(storage, out var id))
        {
            id = storages.Count;
            index[storage] = id;
            storages.Add(storage);
        }
        return id;
    }

    private IEnumerable<Storage> Reads(Stmt stmt) =>
        ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Read>().Select(r => r.Storage).Where(include);

    private IEnumerable<Storage> Writes(Stmt stmt) => stmt switch
    {
        Assign assign when include(assign.Target) => [assign.Target],
        Call call => call.Results.Concat(calls.Clobbers(call)).Where(include),
        _ => [],
    };

    private void Run()
    {
        var blocks = function.Blocks;
        var count = blocks.Count;
        foreach (var block in blocks)
            foreach (var stmt in block.Statements)
            {
                foreach (var s in Reads(stmt)) Id(s);
                foreach (var s in Writes(stmt)) Id(s);
            }
        var words = (storages.Count + 63) / 64;
        if (words == 0) return;

        // 活跃性：向上暴露的使用与定义
        var used = new ulong[count][];
        var killed = new ulong[count][];
        var defBlocks = new List<int>[storages.Count];
        for (var s = 0; s < storages.Count; s++) defBlocks[s] = [];
        for (var b = 0; b < count; b++)
        {
            used[b] = new ulong[words];
            killed[b] = new ulong[words];
            foreach (var stmt in blocks[b].Statements)
            {
                foreach (var s in Reads(stmt))
                {
                    var id = index[s];
                    if (!Has(killed[b], id)) Set(used[b], id);
                }
                foreach (var s in Writes(stmt))
                {
                    var id = index[s];
                    Set(killed[b], id);
                    if (defBlocks[id].Count == 0 || defBlocks[id][^1] != b) defBlocks[id].Add(b);
                }
            }
        }
        var liveIn = new ulong[count][];
        for (var b = 0; b < count; b++) liveIn[b] = (ulong[])used[b].Clone();
        var changed = true;
        var scratch = new ulong[words];
        while (changed)
        {
            changed = false;
            for (var b = count - 1; b >= 0; b--)
            {
                Array.Clear(scratch);
                foreach (var successor in blocks[b].Successors)
                    for (var w = 0; w < words; w++) scratch[w] |= liveIn[successor.Index][w];
                for (var w = 0; w < words; w++)
                {
                    var value = used[b][w] | (scratch[w] & ~killed[b][w]);
                    if (value != liveIn[b][w])
                    {
                        liveIn[b][w] = value;
                        changed = true;
                    }
                }
            }
        }

        // φ 放置：迭代支配边界，且变量在该块入口活跃
        var phis = new List<(int Storage, Phi Phi)>[count];
        for (var b = 0; b < count; b++) phis[b] = [];
        var placed = new int[count];
        var queued = new int[count];
        var work = new Stack<int>();
        for (var s = 0; s < storages.Count; s++)
        {
            var stamp = s + 1;
            foreach (var b in defBlocks[s])
            {
                queued[b] = stamp;
                work.Push(b);
            }
            while (work.Count > 0)
            {
                var b = work.Pop();
                foreach (var y in dominators.Frontier[b])
                {
                    if (placed[y] == stamp) continue;
                    placed[y] = stamp;
                    if (Has(liveIn[y], s))
                    {
                        var storage = storages[s];
                        phis[y].Add((s, new Phi(blocks[y].Start, new Variable(storage, 0), new Variable[blocks[y].Predecessors.Count])));
                    }
                    if (queued[y] != stamp)
                    {
                        queued[y] = stamp;
                        work.Push(y);
                    }
                }
            }
        }

        Rename(phis);
    }

    private static bool Has(ulong[] set, int id) => (set[id >> 6] & (1UL << (id & 63))) != 0;
    private static void Set(ulong[] set, int id) => set[id >> 6] |= 1UL << (id & 63);

    private int Fresh(Storage storage)
    {
        var next = counters.GetValueOrDefault(storage) + 1;
        counters[storage] = next;
        return next;
    }

    private void Rename(List<(int Storage, Phi Phi)>[] phis)
    {
        var blocks = function.Blocks;
        var stacks = new List<int>[storages.Count];
        for (var s = 0; s < storages.Count; s++) stacks[s] = [0];
        var pushed = new List<int>[blocks.Count];
        int Top(Storage s) => stacks[index[s]][^1];

        Expr Rewrite(Expr expr) => ExprMap.Map(expr, e =>
        {
            if (e is not Read read || !include(read.Storage)) return null;
            var version = Top(read.Storage);
            if (version < 0) return new Unknown($"{read.Storage} 被调用破坏", read.Width);
            if (version == 0 && read.Storage == stackPointer) return Fold.Convert(ConvKind.Truncate, new FrameAddress(0), read.Width);
            return new Use(new Variable(read.Storage, version), read.Width);
        });

        var walk = new Stack<(int Block, bool Exit)>();
        walk.Push((0, false));
        while (walk.Count > 0)
        {
            var (b, exit) = walk.Pop();
            if (exit)
            {
                foreach (var s in pushed[b]) stacks[s].RemoveAt(stacks[s].Count - 1);
                continue;
            }
            var block = blocks[b];
            var mine = pushed[b] = [];
            void Push(int s, int version)
            {
                stacks[s].Add(version);
                mine.Add(s);
            }

            var output = new List<Stmt>(block.Statements.Count + phis[b].Count);
            for (var k = 0; k < phis[b].Count; k++)
            {
                var (s, phi) = phis[b][k];
                var version = Fresh(storages[s]);
                Push(s, version);
                phis[b][k] = (s, phi with { Target = new Variable(storages[s], version) });
                output.Add(phis[b][k].Phi);
            }

            HashSet<Storage>? exceptional = null;
            foreach (var stmt in block.Statements)
            {
                var rewritten = ExprMap.MapOperands(stmt, Rewrite);
                switch (rewritten)
                {
                    case Assign assign when include(assign.Target):
                        {
                            var target = assign.Target;
                            var value = assign.Value;
                            if (target.Bank is Bank.Gpr or Bank.Vec or Bank.Temp or Bank.Stack && value.Width < target.Width)
                                value = Fold.Convert(ConvKind.ZeroExtend, value, target.Width);
                            var version = Fresh(target);
                            Push(index[target], version);
                            output.Add(new Define(assign.Address, new Variable(target, version), value));
                            break;
                        }
                    case Call call:
                        {
                            var results = call.Results.Where(include).ToHashSet();
                            exceptional = [.. results, .. calls.Clobbers(call).Where(include)];
                            foreach (var s in calls.Clobbers(call))
                                if (include(s) && !results.Contains(s)) Push(index[s], -1);
                            if (!call.Results.Any(include))
                            {
                                output.Add(call);
                                break;
                            }
                            var defines = call.Defines.Length == call.Results.Length ? (Variable[])call.Defines.Clone() : new Variable[call.Results.Length];
                            for (var r = 0; r < call.Results.Length; r++)
                            {
                                var s = call.Results[r];
                                if (!include(s)) continue;
                                var version = Fresh(s);
                                Push(index[s], version);
                                defines[r] = new Variable(s, version);
                            }
                            output.Add(call with { Defines = defines });
                            break;
                        }
                    default:
                        output.Add(rewritten);
                        break;
                }
            }
            block.Statements = output;

            foreach (var successor in block.Successors.Distinct())
            {
                // 异常边：调用结果与被破坏的寄存器在落地块入口未定义
                var viaHandler = successor == block.Handler;
                for (var j = 0; j < successor.Predecessors.Count; j++)
                {
                    if (successor.Predecessors[j] != block) continue;
                    foreach (var (s, phi) in phis[successor.Index])
                        phi.Sources[j] = viaHandler && exceptional is not null && exceptional.Contains(storages[s])
                            ? new Variable(storages[s], -1)
                            : new Variable(storages[s], stacks[s][^1]);
                }
            }

            walk.Push((b, true));
            var children = dominators.Children[b];
            for (var c = children.Count - 1; c >= 0; c--) walk.Push((children[c], false));
        }
    }
}
