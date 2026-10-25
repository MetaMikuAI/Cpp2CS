using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Idioms;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// 类初始化时机的普查（执行对照中 CIL 侧触发点的依据）：对直接调用有静态构造的类型 T 的方法，统计调用之前同一函数里
/// 是否有对 T 的显式类初始化，按 T 是否泛型、是否精确初始化、被调方法的种类（构造/静态/实例）、调用场合分类。
/// </summary>
internal static class ClassInitCensus
{
    [Command("classinit", "普查调用之前的显式类初始化（执行对照中类初始化触发点的依据）", Arguments = "<binary> <metadata> <所有者前缀>")]
    public static int Run(string binary, string metadata, string prefix)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var functions = facts.Code.Functions.Where(f => f.Region == CodeRegion.Managed)
            .Where(f => facts.EntriesAt(f.Start).Any(e => e.Method is not null && e.Method.Method.Owner.FullName.StartsWith(prefix, StringComparison.Ordinal)))
            .ToArray();
        Console.Error.WriteLine($"  {functions.Length} 个函数");
        var counts = new SortedDictionary<string, (int With, int Without, string Example)>(StringComparer.Ordinal);
        // 不记录模板实例（只要改写结果）
        var lifters = new ThreadLocal<(FunctionLifter, IdiomRewriter)>(() => (new FunctionLifter(facts), new IdiomRewriter(facts) { RecordFilter = _ => false }));
        Parallel.ForEach(System.Collections.Concurrent.Partitioner.Create(0, functions.Length, 500), range =>
        {
            var (lifter, rewriter) = lifters.Value;
            var local = new List<(string Key, bool With, ulong Function, MethodRef? Caller, MethodRef Callee)>();
            for (var i = range.Item1; i < range.Item2; i++)
            {
                var f = functions[i];
                var caller = facts.EntriesAt(f.Start).Select(e => e.Method).FirstOrDefault(m => m is not null);
                MachineFunction function;
                try
                {
                    var lifted = lifter.Lift(f.Start);
                    if (!lifted.Succeeded) continue;
                    rewriter.Run(lifted.Function);
                    function = lifted.Function;
                }
                catch (Exception) { continue; }
                var statements = function.Blocks.SelectMany(b => b.Statements).OrderBy(s => s.Address).ToArray();
                var initialized = new HashSet<TypeDef>();
                foreach (var statement in statements)
                {
                    if (statement is not Call call) continue;
                    if (call.Op is { Kind: OpKind.RunClassConstructor, Operand: DefinitionRef t }) { initialized.Add(t.Definition); continue; }
                    if (call.Op is not null || call.Kind is not (CallKind.Direct or CallKind.Tail) || call.Target is not Const target) continue;
                    var callee = facts.EntriesAt(target.Value).Select(e => e.Method).FirstOrDefault(m => m is not null);
                    if (callee is null) continue;
                    var owner = callee.Method.Owner;
                    if (!owner.Methods.Any(m => m.Name == ".cctor")) continue;
                    if (caller is not null && caller.Method.Owner == owner) continue;
                    var kind = callee.Method.Name == ".ctor" ? "构造" : callee.Method.IsStatic ? "静态" : "实例";
                    var context = kind != "构造" ? "" : caller is { Method.Name: ".ctor" } && call.Arguments.Length > 0 && call.Arguments[0] is Use { Variable: { Version: 0 } v } && v.Storage == Storage.Gpr(0)
                        ? "，this 上（基类构造）" : "，其他（newobj 等）";
                    var key = $"{kind}{context}，{(owner.GenericParameters.Count > 0 ? "泛型" : "非泛型")}，{((owner.Attributes & TypeAttributes.BeforeFieldInit) == 0 ? "精确" : "beforefieldinit")}，{(owner.IsValueType ? "值类型" : "引用类型")}";
                    local.Add((key, initialized.Contains(owner), f.Start, caller, callee));
                }
            }
            lock (counts)
                foreach (var (key, with, start, caller, callee) in local)
                {
                    var (w, wo, e) = counts.GetValueOrDefault(key, (0, 0, ""));
                    if (with) w++; else wo++;
                    // 例子优先取"没有"的一侧（少数派更值得看）
                    if (e.Length == 0 || !with && wo == 1) e = $"0x{start:x} {caller} → {callee}";
                    counts[key] = (w, wo, e);
                }
        });
        Console.WriteLine($"  {functions.Length} 个函数（所有者前缀 {prefix}）");
        foreach (var (key, (w, wo, example)) in counts)
            Console.WriteLine($"  {key}：之前有显式初始化 {w}，没有 {wo}；例 {example}");
        return 0;
    }
}
