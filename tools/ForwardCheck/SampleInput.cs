using System.Globalization;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Target;
using M = Cpp2CS.Model;

namespace Cpp2CS.Tools.ForwardCheck;

internal sealed class SampleInput
{
    private readonly ModelMetadata metadata;
    private readonly EntityFacts entities;
    private readonly BridgeFacts facts;
    private readonly Il2CppInput input;
    private readonly Dictionary<long, ManagedBody> complete = [];
    private readonly Arm64Target target;
    private readonly (long Key, ulong Address)[] population;

    public SampleInput(string binary, string path, string? symbols)
    {
        input = Il2CppInput.Load(binary, path);
        var file = File.ReadAllBytes(binary);
        metadata = ModelInput.Facts(input, file);
        entities = new(metadata);
        facts = new(input, metadata, symbols, file);
        var rows = new List<(long, ulong)>();
        for (int i = 0; i < input.Code.Methods.Count; i++)
            if (input.Code.Methods[i].Entry is ulong rva) rows.Add((i, rva));
        for (int i = 0; i < input.Code.MethodInstances.Count; i++)
            if (input.Code.MethodInstances[i].Entry is ulong rva)
                rows.Add((metadata.Keys.MethodKey(input.Model.MethodInstances[i])!.Value, rva));
        // 同一托管实体有多行登记时只抽一次。若入口不唯一，不能随意挑一个作其实现。
        var methods = rows.Distinct().OrderBy(r => r.Item1).ToArray();
        if (methods.DistinctBy(r => r.Item1).Count() != methods.Length)
            throw new InvalidDataException("同一托管方法实体登记了多个原生入口");
        target = new(input.Elf, file, methods.Select(m => m.Item2));
        population = methods.Select(m => (m.Item1, checked(m.Item2 + input.Elf.ImageBase))).ToArray();
    }

    private string Name(long key)
    {
        var model = metadata.Model;
        string Definition(int i)
        {
            var d = model.Types[i];
            return d.DeclaringType is int parent ? Definition(parent) + "+" + d.Name :
                d.Namespace.Length == 0 ? d.Name : d.Namespace + "." + d.Name;
        }
        string Arguments(IReadOnlyList<M.TypeReference> args) => args.Count == 0 ? "" : "<" + string.Join(",", args.Select(Type)) + ">";
        string Type(M.TypeReference t) => t switch
        {
            M.NamedType n => Definition(n.Definition) + Arguments(n.Arguments),
            M.VariableType v => (v.Method ? "!!" : "!") + v.Position,
            M.PointerType p => Type(p.Element) + "*",
            M.ReferenceType r => Type(r.Element) + "&",
            M.ArrayType a => Type(a.Element) + (a.Vector ? "[]" : a.Rank == 1 ? "[*]" : "[" + new string(',', a.Rank - 1) + "]"),
            _ => throw new InvalidDataException($"未知类型 {t}"),
        };
        var m = metadata.Keys.DescribeMethod(new(EntityKind.Method, key))!;
        var def = model.Methods[m.Definition];
        return Definition(def.Owner) + Arguments(m.TypeArguments) + "::" + def.Name + Arguments(m.MethodArguments);
    }

    public Sample.Plan Draw(int count, int seed, string? show)
    {
        // 总体按元数据实体序排列；.NET 10 的有种子 Random 与机器字长、区域和哈希顺序无关。
        var order = population.ToArray();
        var random = new Random(seed);
        int main = Math.Min(count, order.Length);
        int audit = Math.Min(20, order.Length - main);
        var items = new List<Sample.Item>();
        for (int i = 0; i < main + audit; i++)
        {
            int j = random.Next(i, order.Length);
            (order[i], order[j]) = (order[j], order[i]);
            var (key, address) = order[i];
            items.Add(new(key, address, Name(key)));
        }
        var shown = new HashSet<long>();
        if (show != null)
        {
            bool address = ulong.TryParse(show.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? show[2..] : show,
                NumberStyles.AllowHexSpecifier, CultureInfo.InvariantCulture, out ulong wanted);
            address = address && population.Any(m => m.Address == wanted);
            var sampled = items.Select(m => m.Key).ToHashSet();
            foreach (var (key, entry) in population)
            {
                if (address && entry != wanted) continue;
                string name = Name(key);
                if (!address && name != show)
                {
                    int definition = metadata.Keys.DescribeMethod(new(EntityKind.Method, key))!.Definition;
                    if (metadata.Model.Methods[definition].Name != show) continue;
                }
                shown.Add(key);
                if (!sampled.Contains(key)) items.Add(new(key, entry, name));
            }
        }
        return new(population.Length, target.Entries.Count, main, audit, items.ToArray(), shown.ToArray());
    }

    public void Recover(Sample.Item item, Sample.Result result, Action<string> progress)
    {
        var lift = target.Lift(item.Address);
        if (lift.Snapshot is not { } snapshot) { result.Hole("前端", lift.Reason ?? "未产出快照"); return; }
        progress("提升");
        var entity = new EntityRef(EntityKind.Method, item.Key);
        MethodShape host;
        try { host = metadata.Method(entity); }
        catch (ExpansionException e) { result.Hole("事实层", e.Message); return; }
        var graph = new EffectGraph(snapshot, host, facts);
        if (graph.Failure is { } missing) { result.Hole("事实层", missing); return; }

        // 占用的计量单位是效果图中的出现和条件抛出边。不可观察的 None 不进入分母。
        var effects = graph.Effects.Where(e => e.Kind != NativeEffectKind.None).Select(e => EffectRef.Of(e.Occurrence))
            .Concat(graph.Checks.Select(c => EffectRef.Of(c.Edge))).ToHashSet();
        progress($"效果 {effects.Count}");
        var lifts = new Dictionary<ulong, MethodSnapshot?> { [item.Address] = snapshot };
        MethodSnapshot? Snapshot(ulong entry)
        {
            if (!lifts.TryGetValue(entry, out var s)) lifts[entry] = s = target.Lift(entry).Snapshot;
            return s;
        }
        var view = new FactView(graph, entities, facts.Layout);
        var context = new RecoveryContext(snapshot, host, host.IsTypeInitializer ? host.DeclaringType : null, facts, entities, Snapshot);
        var (_, explanation) = ForwardCheck.Recover.ProveAndSelect(view, context, ForwardCheck.Recover.Propose(view));
        var covered = explanation.Selected.SelectMany(c => c.Claim.Occupied).Distinct().Count(effects.Contains);
        progress($"选中 {covered}");
        var body = Lowering.Lower(explanation);
        if (!body.Complete)
        {
            foreach (var h in body.Holes.Where(h => !h.Derived))
                result.Hole(ForwardCheck.Recover.Reason(h.Layer.ToString(), h.Obligation), $"{h.What}：{h.Reason}");
            result.First ??= body.Holes[0].What + "：" + body.Holes[0].Reason;
            return;
        }

        progress("完整");
        complete[item.Key] = body;
    }

    public Sample.Generation Generate(Sample.Item[] items, long[] main, string? directory)
    {
        // 工作进程超时后只重建已经完成恢复的方法。写出仍须经过原来的下降入口。
        foreach (var item in items)
            if (!complete.ContainsKey(item.Key)) Recover(item, new(), _ => { });
        var selected = items.Select(i => complete[i.Key]).ToArray();
        using var set = new AssemblySet();
        set.Generate(input, metadata, selected);
        var endpoints = new Dictionary<long, string>();
        foreach (var item in items)
        {
            var body = complete[item.Key];
            var (module, token) = set.Host(body.Host.Entity);
            try
            {
                var (decoded, scope, _) = set.Reader.GeneratedBody(module, token, body);
                var snapshot = target.Lift(item.Address).Snapshot ?? throw new InvalidDataException("终点缺少快照");
                var expanded = IlExpander.Expand(decoded, metadata, scope, snapshot.Terms, 1, snapshot.PointerBits);
                facts.BeginCheck();
                var verdict = CoExecution.Check(snapshot, expanded.Graph, decoded, facts, address => target.Lift(address).Snapshot);
                endpoints.Add(item.Key, verdict.Verdict == Verdict.Proved ? "通过" : $"{verdict.Verdict}：{facts.Detail(verdict)}");
            }
            catch (ExpansionException e) { endpoints.Add(item.Key, e.Message); }
            catch (InvalidDataException e) { endpoints.Add(item.Key, e.Message); }
            catch (BadImageFormatException e) { endpoints.Add(item.Key, e.Message); }
        }
        var problems = set.Verify(main.Select(key => complete[key].Host.Entity), out int passed);
        if (directory != null && endpoints.Values.All(r => r == "通过")) set.Publish(directory);
        return new(endpoints, set.Count, set.Reader.DecodedMethods, set.Seconds, set.Peak, passed, problems,
            input.AssemblyMetadata.Value.UnknownParameterDefaults.Select(p => $"方法 {p.Key.Method} 参数 {p.Key.Sequence}：{p.Value}").ToArray());
    }
}
