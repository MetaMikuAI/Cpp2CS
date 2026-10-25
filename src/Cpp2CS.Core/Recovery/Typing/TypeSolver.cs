using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Typing;

/// <summary>
/// 解一轮约束。规则：
/// 0. 调用破坏的值没有类型，其余约束一概不看；它也不向流的目标传播；
/// 1. 运行时引用与托管类型（定义或使用）同时出现即冲突；
/// 2. 每个变量收到的定义类型是一个集合：自己的定义，加上沿流（φ、复制）传来的全部定义类型。下界是集合的汇合：
///    引用类型取最小公共超类（沿基类链）；整数与 bool 是同一种类，取与顺序无关的代表（位宽来自变量的定义，
///    写出时由下降阶段取局部类型）；浮点、值类型要求相同；
/// 3. 下界必须可赋给每个使用的类型；整数与 bool 之间的使用是投影（截断或扩展），不冲突。下界满足全部使用时，结果是下界；
/// 4. 下界不满足某个使用时，若存在一个使用类型 U，每个定义类型都可赋给 U、U 又可赋给全部使用，结果是最具体的这样的 U。
///    典型情形是 φ 汇合了实现同一接口的不同类：沿基类链的公共超类是 object，接口才是满足使用的类型；
/// 5. 没有定义时（如只由常量定义的 φ），在使用的类型中取能赋给其余全部使用的最具体者；
/// 6. 其余情形冲突。冲突的结果仍带着下界（<see cref="ConflictResult.Lower"/>），供下一轮的贡献者推导；
///    冲突本身只在最终结果中成为洞，不会让下一轮的推导失去依据（否则会在"冲突—类型消失—约束消失"之间振荡）。
/// 求解只依赖约束本身，不读贡献者的任何状态。
/// </summary>
public static class TypeSolver
{
    public static Dictionary<Variable, TypeResult> Solve(TypeConstraints constraints, ManagedTypes types)
    {
        var result = new Dictionary<Variable, TypeResult>();
        var incoming = new Dictionary<Variable, Dictionary<TypeRef, TypeEvidence>>();
        bool Add(Variable v, TypeRef type, TypeEvidence evidence)
        {
            if (constraints.Clobbered.ContainsKey(v)) return false;
            if (!incoming.TryGetValue(v, out var set)) incoming[v] = set = new();
            return set.TryAdd(type, evidence);
        }
        foreach (var (v, list) in constraints.Definitions)
            foreach (var (type, evidence) in list)
                Add(v, type, evidence);
        // 沿流传播定义类型到不动点。类型都来自有限的定义集合，因此终止。
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var (to, sources) in constraints.FlowEdges)
                foreach (var (source, evidence) in sources)
                    if (incoming.TryGetValue(source, out var from))
                        foreach (var type in from.Keys.ToArray())
                            changed |= Add(to, type, evidence);
        }

        foreach (var v in constraints.Variables)
        {
            if (constraints.Clobbered.TryGetValue(v, out var clobbered)) { result[v] = new ClobberedResult(clobbered.First()); continue; }
            var uses = constraints.Uses.TryGetValue(v, out var useSet) ? useSet.ToList() : [];
            var defined = incoming.TryGetValue(v, out var set)
                ? set.OrderBy(p => p.Key.ToString(), StringComparer.Ordinal).ToArray() : [];
            if (constraints.Runtime.TryGetValue(v, out var runtime))
            {
                var managed = defined.Length > 0 ? defined[0].Value : uses.Select(u => u.Evidence).FirstOrDefault();
                var first = runtime.First();
                result[v] = managed is null && runtime.Select(r => r.Kind).Distinct().Count() == 1
                    ? new RuntimeResult(first.Kind)
                    : new ConflictResult($"运行时引用 {first.Evidence} 与 {managed?.ToString() ?? "另一种运行时引用"} 冲突");
                continue;
            }
            if (defined.Length > 0)
            {
                var (bound, evidence) = defined[0];
                string? disjoint = null;
                foreach (var (type, source) in defined.Skip(1))
                {
                    if (Join(types, bound, type) is { } joined) { bound = joined; continue; }
                    disjoint = $"定义 {bound}（{evidence}）与 {type}（{source}）没有公共类型";
                    break;
                }
                if (disjoint is not null) { result[v] = new ConflictResult(disjoint); continue; }
                var violated = uses.FirstOrDefault(u => !Assignable(types, bound, u.Type));
                if (violated.Evidence is null) { result[v] = new ManagedResult(bound); continue; }
                var upper = MostSpecific(types, uses.Select(u => u.Type).Distinct()
                    .Where(t => defined.All(d => Assignable(types, d.Key, t)) && uses.All(u => Assignable(types, t, u.Type))).ToArray());
                result[v] = upper is not null ? new ManagedResult(upper)
                    : new ConflictResult($"定义 {bound}（{evidence}）不能当作 {violated.Type} 使用（{violated.Evidence}）", bound);
                continue;
            }
            if (uses.Count == 0) continue;
            var specific = MostSpecific(types, uses.Select(u => u.Type).Distinct().Where(t => uses.All(u => Assignable(types, t, u.Type))).ToArray());
            result[v] = specific is not null ? new ManagedResult(specific)
                : new ConflictResult($"使用的类型互不兼容：{string.Join("；", uses.Select(u => $"{u.Type}（{u.Evidence}）"))}");
        }
        return result;
    }

    /// <summary>都满足同一组使用的候选里最具体的一个：整数取代表；引用类型取可赋给其余全部候选者。没有候选时为 null。</summary>
    private static TypeRef? MostSpecific(ManagedTypes types, TypeRef[] candidates)
    {
        if (candidates.Length == 0) return null;
        if (candidates.All(t => Integral(types, t))) return candidates.Aggregate((x, y) => Representative(types, x, y));
        return candidates.OrderBy(t => t.ToString(), StringComparer.Ordinal).FirstOrDefault(t => candidates.All(c => Assignable(types, t, c)));
    }

    /// <summary>
    /// 引用类型取最小公共超类（沿 a 的基类链找第一个 b 可赋给的类型）；整数与 bool 取代表类型（<see cref="Representative"/>）；
    /// 其余类型必须相同。
    /// </summary>
    public static TypeRef? Join(ManagedTypes types, TypeRef a, TypeRef b)
    {
        if (a.Equals(b)) return a;
        if (Integral(types, a) && Integral(types, b)) return Representative(types, a, b);
        if (!ManagedTypes.IsReferenceType(a) || !ManagedTypes.IsReferenceType(b)) return null;
        for (TypeRef? current = a; current is not null; current = BaseOf(current))
            if (Assignable(types, b, current)) return current;
        return types.Object;
    }

    private static TypeRef? BaseOf(TypeRef type) =>
        type is DefinitionRef d ? d.Definition.BaseType?.Substitute(d.Arguments, []) : null;

    /// <summary>整数（含枚举、char）与 bool：寄存器里的位，位宽由定义决定，使用处的宽度差异由写出阶段截断或扩展。</summary>
    public static bool Integral(ManagedTypes types, TypeRef type) => types.Kind(type) is TypeKind.Int or TypeKind.Bool;

    /// <summary>
    /// 同一种类的两个整数类型的代表：与汇合的顺序无关。依次优先整数（不是 bool）、位宽大者、有符号者，最后按名称。
    /// 代表只决定种类与符号提示，不决定局部变量的位宽。
    /// </summary>
    public static TypeRef Representative(ManagedTypes types, TypeRef a, TypeRef b)
    {
        (int, int, int) Rank(TypeRef t) => (types.Kind(t) == TypeKind.Int ? 1 : 0, types.Bits(t), ManagedTypes.IsSigned(t) ? 1 : 0);
        var (ra, rb) = (Rank(a), Rank(b));
        if (ra != rb) return ra.CompareTo(rb) > 0 ? a : b;
        return string.CompareOrdinal(a.ToString(), b.ToString()) <= 0 ? a : b;
    }

    private static bool Assignable(ManagedTypes types, TypeRef from, TypeRef to) =>
        from.Equals(to) || Integral(types, from) && Integral(types, to) || types.IsAssignable(from, to);
}
