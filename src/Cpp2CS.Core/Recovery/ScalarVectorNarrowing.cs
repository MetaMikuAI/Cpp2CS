using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>
/// L3 入口的标量投影。Arm ARM DDI 0487B.a C1.2 的标量寄存器写入清高位，
/// 在本 IR 中由 Assign 的窄值及 SsaBuilder 的 ZeroExtend128 表示。
/// 只在每个读取都恰好取原标量宽度时去掉外壳；保留定义位置，不能把加载搬到使用处。
/// </summary>
internal static class ScalarVectorNarrowing
{
    internal static Expr Low(Expr value, int width) => value.Width == width ? value
        : value.Width > width ? Fold.Convert(ConvKind.Truncate, value, width) : value;

    internal static int Run(IReadOnlyList<Block> blocks, Func<Call, IReadOnlyDictionary<Storage, int>> callWidths, Func<Call, IReadOnlyDictionary<Storage, int>>? resultWidths = null)
    {
        // 标量 spill 的低位往返只替换 SSA 值引用，不移动加载或重新求值。
        var copies = blocks.SelectMany(b => b.Statements).OfType<Define>()
            .Where(d => d.Value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Operand: Use })
            .ToDictionary(d => d.Target, d => (Ir.Convert)d.Value);
        Expr? Project(Expr expression)
        {
            if (expression is not Use original) return null;
            var current = original;
            var seen = new HashSet<Variable>();
            while (seen.Add(current.Variable) && copies.TryGetValue(current.Variable, out var copy)
                && current.Width <= copy.Width && current.Width <= copy.Operand.Width)
                current = new Use(((Use)copy.Operand).Variable, current.Width);
            return current == original ? null : current;
        }
        foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Project));

        // AAPCS64 C.1/C.2：标量及 HFA 分量只占 v 寄存器低位；未知签名不提供宽度。
        foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call call && callWidths(call) is { Count: > 0 } widths)
                {
                    var args = call.Arguments.Select((e, k) => k < call.Sources.Length && widths.TryGetValue(call.Sources[k], out var width) && width > 0
                        ? Low(e, width) : e).ToArray();
                    if (!args.AsSpan().SequenceEqual(call.Arguments)) block.Statements[i] = call with { Arguments = args };
                }

        var candidates = blocks.SelectMany(b => b.Statements).OfType<Define>()
            .Where(d => d.Target.Storage.Bank == Bank.Vec && d.Value is Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 128, Operand.Width: 32 or 64 } c
                && !ExprMap.Walk(c.Operand).Any(e => e is Insert or Intrinsic))
            .ToDictionary(d => d.Target, d => ((Ir.Convert)d.Value).Operand);
        // φ 网：经 φ 相连的向量寄存器值。网中每个非 φ 定义都是同宽标量的清高位、每个读取都恰好取这个宽度时，
        // 整个网都是这个标量（如循环中的 float 局部变量 t = 0; t += dt）；φ 本身不改，位宽随来源变窄。
        var phis = blocks.SelectMany(b => b.Statements).OfType<Phi>().Where(p => p.Target.Storage.Bank == Bank.Vec).ToArray();
        var parent = new Dictionary<Variable, Variable>();
        Variable Find(Variable v)
        {
            while (parent.TryGetValue(v, out var up) && up != v) v = parent[v] = parent.GetValueOrDefault(up, up);
            return v;
        }
        foreach (var phi in phis)
        {
            parent.TryAdd(phi.Target, phi.Target);
            foreach (var source in phi.Sources)
            {
                parent.TryAdd(source, source);
                var (a, b) = (Find(phi.Target), Find(source));
                if (a != b) parent[a] = b;
            }
        }
        var phiTargets = phis.Select(p => p.Target).ToHashSet();
        // 标量浮点返回值（AAPCS64 C.1：只占 v0 的低位）作为网的成员，本身不改写。
        var scalarResults = new Dictionary<Variable, int>();
        if (resultWidths is not null)
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Defines.Length > 0 && parent.Count > 0))
            {
                var widths = resultWidths(call);
                for (var k = 0; k < call.Defines.Length && k < call.Results.Length; k++)
                    if (widths.TryGetValue(call.Results[k], out var width) && parent.ContainsKey(call.Defines[k])) scalarResults[call.Defines[k]] = width;
            }
        var webWidth = new Dictionary<Variable, int>();
        foreach (var web in parent.Keys.GroupBy(Find))
        {
            // 被调用破坏的来源（版本 -1）没有值，不约束宽度。
            var widths = web.Select(v => candidates.TryGetValue(v, out var scalar) ? scalar.Width : scalarResults.TryGetValue(v, out var result) ? result
                : phiTargets.Contains(v) || v.Version < 0 ? 0 : -1).ToArray();
            if (widths.Contains(-1) || widths.Where(w => w > 0).Distinct().Count() != 1) continue;
            var width = widths.First(w => w > 0);
            foreach (var v in web) webWidth[v] = width;
        }
        var used = new HashSet<Variable>();
        var rejected = new HashSet<Variable>();
        foreach (var statement in blocks.SelectMany(b => b.Statements))
        {
            // φ 隐含读取全部寄存器：不在可收窄的网中时不建立跨 φ 的窄值关系，也不推测高位内容。
            if (statement is Phi phi)
            {
                rejected.UnionWith(phi.Sources.Where(v => !webWidth.ContainsKey(v)));
                continue;
            }
            // 调用中只是透传的向量寄存器（callWidths 给出宽度 0）不是使用。
            var passThrough = statement is Call passing && callWidths(passing) is { Count: > 0 } passingWidths
                ? passing.Arguments.Where((_, k) => k < passing.Sources.Length && passingWidths.TryGetValue(passing.Sources[k], out var w) && w == 0).ToHashSet(ReferenceEqualityComparer.Instance)
                : null;
            foreach (var use in ExprMap.Operands(statement).Where(e => passThrough is null || !passThrough.Contains(e)).SelectMany(ExprMap.Walk).OfType<Use>())
                if (webWidth.TryGetValue(use.Variable, out var width) || candidates.TryGetValue(use.Variable, out var scalar) && (width = scalar.Width) > 0)
                {
                    used.Add(use.Variable);
                    if (use.Width != width) rejected.Add(use.Variable);
                }
        }
        // 网中任何成员被拒绝，整个网都不收窄。
        foreach (var web in webWidth.Keys.GroupBy(Find).ToArray())
            if (web.Any(rejected.Contains))
                rejected.UnionWith(web);
            else if (web.Any(used.Contains))
                used.UnionWith(web);
        var changed = 0;
        foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Define d && used.Contains(d.Target) && !rejected.Contains(d.Target)
                    && candidates.TryGetValue(d.Target, out var scalar))
                {
                    block.Statements[i] = d with { Value = scalar };
                    changed++;
                }
        return changed;
    }
}
