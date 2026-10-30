using Cpp2CS.Machine.Flow;
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

    internal static int Run(IReadOnlyList<Block> blocks, Func<Call, IReadOnlyDictionary<Storage, int>> callWidths, Func<Call, IReadOnlyDictionary<Storage, int>>? resultWidths = null,
        IReadOnlyDictionary<Storage, int>? inputWidths = null)
    {
        // 标量 spill 的低位往返只替换 SSA 值引用，不移动加载或重新求值。
        var copies = blocks.SelectMany(b => b.Statements).OfType<Define>()
            .Where(d => d.Value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Operand: Use })
            .ToDictionary(d => d.Target, d => (Ir.Convert)d.Value);
        Expr? Project(Expr expression)
        {
            if (expression is Intrinsic duplicate) return RepeatedConstant(duplicate) ?? RepeatedVariable(duplicate);
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

        return NarrowDefinitions(blocks, callWidths, resultWidths, inputWidths);
    }

    /// <summary>仅收窄已证明的定义；调用实参投影已完成时可在类型推断后复用。</summary>
    internal static int NarrowDefinitions(IReadOnlyList<Block> blocks, Func<Call, IReadOnlyDictionary<Storage, int>> callWidths,
        Func<Call, IReadOnlyDictionary<Storage, int>>? resultWidths = null, IReadOnlyDictionary<Storage, int>? inputWidths = null,
        Action<Define, Define>? replaced = null)
    {
        var candidates = blocks.SelectMany(b => b.Statements).OfType<Define>()
            .Where(d => (d.Target.Storage.Bank is Bank.Vec or Bank.Temp && d.Value.Width == 128 || d.Target.Storage.Bank == Bank.Stack && d.Value.Width == 64)
                && d.Value is Ir.Convert { Kind: ConvKind.ZeroExtend, Operand.Width: 32 or 64 } c
                && !ExprMap.Walk(c.Operand).Any(e => e is Insert or Intrinsic))
            .ToDictionary(d => d.Target, d => ((Ir.Convert)d.Value).Operand);
        // φ 网：经 φ 相连的向量寄存器值。网中每个非 φ 定义都是同宽标量的清高位、每个读取都恰好取这个宽度时，
        // 整个网都是这个标量（如循环中的 float 局部变量 t = 0; t += dt）；φ 本身不改，位宽随来源变窄。
        var phis = blocks.SelectMany(b => b.Statements).OfType<Phi>().ToArray();
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
        // 常量位型可存于整数寄存器，也可能被提升为 64 位后写入向量低位；仅全部观察低 32 位时截断。
        var observed = blocks.SelectMany(b => b.Statements).Where(s => s is not Phi)
            .SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>())
            .GroupBy(u => Find(u.Variable)).ToDictionary(g => g.Key, g => g.Select(u => u.Width).Distinct().ToArray());
        foreach (var definition in blocks.SelectMany(b => b.Statements).OfType<Define>())
        {
            // 栈上的向量暂存可能只读取一个标量；收窄读取保留原位置，未观察的高位不参与后续栈合流。
            if (definition.Target.Storage.Bank == Bank.Vec && definition.Value is Load { Width: 128, Address: FrameAddress } load
                && observed.GetValueOrDefault(Find(definition.Target)) is [var readWidth and (32 or 64)])
                candidates[definition.Target] = load with { Width = readWidth };
            var constant = definition.Value switch
            {
                Const { Width: 64 } c => c,
                Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 128, Operand: Const { Width: 64 } c } => c,
                _ => null,
            };
            if (constant is not null && observed.GetValueOrDefault(Find(definition.Target)) is [32])
                candidates[definition.Target] = Expr.C(constant.Value, 32);
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
                : v.Version == 0 && inputWidths?.TryGetValue(v.Storage, out var input) == true ? input
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
                    var replacement = d with { Value = scalar };
                    block.Statements[i] = replacement;
                    replaced?.Invoke(d, replacement);
                    changed++;
                }
        return changed;
    }

    /// <summary>常量逐道复制转成完整位片，保留浮点位型；非恒定操作数不在使用处重复求值。</summary>
    internal static Expr? RepeatedConstant(Intrinsic duplicate)
    {
        var laneWidth = duplicate.Name switch { "vdup.8" => 8, "vdup.16" => 16, "vdup.32" => 32, "vdup.64" => 64, _ => 0 };
        if (laneWidth == 0 || duplicate.Width is not (64 or 128) || duplicate.Arguments is not [Const lane] || lane.Width != laneWidth) return null;
        ulong word = 0;
        for (var low = 0; low < 64; low += laneWidth) word |= (lane.Value & Expr.Mask(laneWidth)) << low;
        var half = Expr.C(word, 64);
        return duplicate.Width == 64 ? half : new Insert(new Insert(Expr.C(0, 128), half, 0), half, 64);
    }

    /// <summary>SSA 标量逐道复制保留同一快照；访存及其他表达式不重复求值。</summary>
    internal static Expr? RepeatedVariable(Intrinsic duplicate)
    {
        var laneWidth = duplicate.Name switch { "vdup.8" => 8, "vdup.16" => 16, "vdup.32" => 32, "vdup.64" => 64, _ => 0 };
        if (laneWidth == 0 || duplicate.Width is not (64 or 128) || duplicate.Arguments is not [Use { Variable.Version: >= 0 } lane]
            || lane.Width != laneWidth) return null;
        Expr result = Expr.C(0, duplicate.Width);
        for (var low = 0; low < duplicate.Width; low += laneWidth) result = new Insert(result, lane, low);
        return result;
    }
}
