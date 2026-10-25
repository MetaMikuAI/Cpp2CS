using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>异常区域的语句片段。位置是原始块及半开语句区间，避免给拆块伪造机器地址。</summary>
public sealed class ExceptionFragment(int id, Block block, int first, int limit)
{
    public int Id { get; } = id;
    public Block Block { get; } = block;
    public int First { get; } = first;
    public int Limit { get; } = limit;
    public IEnumerable<Stmt> Statements => Block.Statements.Skip(First).Take(Limit - First);
    public List<ExceptionFragment> Normal { get; } = [];
    public ExceptionFragment? Exceptional { get; internal set; }
    public ulong? NativeExceptionSite { get; internal set; }
    public ulong? MissingLandingPad { get; internal set; }
    public ulong[] NativeLandingPath { get; internal set; } = [];
    public override string ToString() => $"0x{Block.Start:x}[{First},{Limit})";
}

/// <summary>
/// 独立视图，不改写生产 SSA。每次调用前后拆分，因而 BeginCatch 前、EndCatch 后一定有边界；
/// phi 仍保留原块的逐前驱来源，2b 写出时必须据此做边赋值，不能把拆块当作重新生成 SSA。
/// </summary>
public sealed class ExceptionStatementGraph
{
    public ExceptionFragment[] Fragments { get; }
    public ExceptionFragment Entry { get; }
    public IReadOnlyDictionary<Block, ExceptionFragment> First { get; }
    public ExceptionStatementGraph(MachineFunction function, Func<ulong, ulong?>? branchTarget = null)
    {
        var all = new List<ExceptionFragment>();
        var first = new Dictionary<Block, ExceptionFragment>();
        var last = new Dictionary<Block, ExceptionFragment>();
        foreach (var block in function.Blocks)
        {
            var cuts = new SortedSet<int> { 0, block.Statements.Count };
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call) { cuts.Add(i); cuts.Add(i + 1); }
            ExceptionFragment? previous = null;
            var offsets = cuts.ToArray();
            if (offsets.Length == 1) offsets = [0, 0];
            for (var i = 1; i < offsets.Length; i++)
            {
                var fragment = new ExceptionFragment(all.Count, block, offsets[i - 1], offsets[i]);
                all.Add(fragment); first.TryAdd(block, fragment); previous?.Normal.Add(fragment); previous = fragment;
            }
            last[block] = previous!;
        }
        foreach (var block in function.Blocks)
        {
            last[block].Normal.AddRange(block.NormalSuccessors.Select(b => first[b]));
            if (block.Handler is not { } pad) continue;
            // CFG 的异常边属于末次调用；同块其他归一操作不能无依据继承这条边。
            var call = block.Statements.OfType<Call>().LastOrDefault();
            if (call is null) continue;
            var owner = all.Single(f => f.Block == block && f.Statements.Contains(call));
            owner.Exceptional = first[pad];
        }
        // Call.Address 在 InterfaceInvokeData 等归一后仍是真实调用点；条件抛出单独保留原始 site。
        // 这里恢复异常转移的来源证据，原生产 CFG/phi 不动；2b 必须按此 native site 恢复异常边值。
        var byAddress = first.GroupBy(p => p.Key.Start).ToDictionary(g => g.Key, g => g.First().Value);
        foreach (var fragment in all)
            if (fragment.Statements.OfType<Call>().SingleOrDefault() is { } call)
            {
                var site = call.NativeExceptionSite ?? call.Address;
                fragment.NativeExceptionSite = site;
                var region = function.Range.ExceptionRegions.SingleOrDefault(r => r.Start <= site && site < r.End);
                if (region is { LandingPad: not 0 })
                {
                    var landing = region.LandingPad;
                    var seen = new HashSet<ulong> { landing }; var path = new List<ulong> { landing };
                    while (!byAddress.ContainsKey(landing) && branchTarget?.Invoke(landing) is { } target && seen.Add(target))
                    { landing = target; path.Add(landing); }
                    fragment.NativeLandingPath = path.ToArray();
                    if (byAddress.TryGetValue(landing, out var pad)) fragment.Exceptional = pad;
                    else if (fragment.Exceptional is null || call.NativeExceptionSite is not null || call.Address < fragment.Block.Start || call.Address >= fragment.Block.End)
                        fragment.MissingLandingPad = region.LandingPad;
                }
            }
        Fragments = all.ToArray(); First = first; Entry = first[function.EntryBlock];
    }
}
