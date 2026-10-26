using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private sealed record ArraySpan(Expr Array, Expr Start, MethodRef Factory);
        private readonly Dictionary<(Call Call, int Parameter), ArraySpan> arraySpans = [];

        // 数组尾切片内联为 data + start、Length - start；保留原有空值与越界分支。
        [Analysis("数组切片", 95, After = ["类型"])]
        private void PrepareArraySpans()
        {
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                if (Resolve(call) is not { } target || owner.abi.Classify(target, out _) is not { } signature) continue;
                var registers = ArgumentsOf(call);
                for (var i = 0; i < signature.Parameters.Length; i++)
                {
                    if (signature.Parameters[i] is not { Type: DefinitionRef { Definition.FullName: "System.Span", Arguments: [var element] },
                        Passing: Passing.Registers, Pieces: [var data, var length] }
                        || !element.Equals(types.Byte) || data.Offset != 0 || length.Offset != 8
                        || !registers.TryGetValue(data.Register, out var pointer) || !registers.TryGetValue(length.Register, out var count)) continue;
                    var hidden = new HashSet<Variable>();
                    Expr Top(Expr e, bool hide = false, int depth = 0)
                    {
                        if (depth > 20) return e;
                        if (e is Ir.Convert c) return Top(c.Operand, hide, depth + 1);
                        if (e is Use u && values.TryGetValue(u.Variable, out var value))
                        {
                            if (hide && known.GetValueOrDefault(u.Variable) is ArrayRef) return e;
                            if (hide) hidden.Add(u.Variable);
                            return Top(value, hide, depth + 1);
                        }
                        return e;
                    }
                    ArraySpan? Match(Expr p, Expr n)
                    {
                        var terms = new List<Expr>();
                        void Flatten(Expr e)
                        {
                            e = Top(e, true);
                            if (e is Binary { Op: BinOp.Add } add) { Flatten(add.Left); Flatten(add.Right); }
                            else terms.Add(e);
                        }
                        Flatten(p);
                        if (terms.Count != 3 || terms.OfType<Const>().ToArray() is not [Const { Value: 32 }]
                            || terms.OfType<Use>().Where(u => known.GetValueOrDefault(u.Variable) is ArrayRef { Element: var t } && t.Equals(element)).ToArray() is not [var array]) return null;
                        var start = terms.Single(t => t is not Const && t != array);
                        if (Top(n) is not Binary { Op: BinOp.Sub, Left: var size, Right: var index }
                            || Top(index) != Top(start)
                            || Top(size) is not Load { Width: 32, Address: Binary { Op: BinOp.Add, Left: var root, Right: Const { Value: 24 } } }
                            || Top(root) != Top(array)) return null;
                        var factory = types.CorlibDefinition("System.MemoryExtensions")?.Methods.FirstOrDefault(m =>
                            m.Name == "AsSpan" && m.IsStatic && m.GenericParameters.Count == 1
                            && m.Parameters is [{ Type: ArrayRef { Rank: 1, IsVector: true, Element: GenericParameterRef } }, { Type: var offset }]
                            && offset.Equals(types.Int32));
                        return factory is null ? null : new(array, start, new MethodRef(factory, [], [element]));
                    }
                    var candidate = Match(pointer, count);
                    if (candidate is null)
                    {
                        hidden.Clear();
                        if (Top(pointer) is not Use p || !phis.TryGetValue(p.Variable, out var pp)
                            || Top(count) is not Use n || !phis.TryGetValue(n.Variable, out var np)
                            || pp.Sources.Length != 2 || np.Sources.Length != 2
                            || !blocks.Any(b => b.Statements.Contains(pp) && b.Statements.Contains(np))) continue;
                        for (var arm = 0; arm < 2; arm++)
                        {
                            hidden.Clear();
                            if (Top(new Use(pp.Sources[1 - arm], 64), true) is Const { Value: 0 }
                                && Top(new Use(np.Sources[1 - arm], 64)) is Const { Value: 0 })
                                candidate = Match(new Use(pp.Sources[arm], 64), new Use(np.Sources[arm], 64));
                            if (candidate is not null)
                            {
                                var join = blocks.Single(b => b.Statements.Contains(pp));
                                var block = join.Predecessors[1 - arm];
                                var seen = new HashSet<Flow.Block>();
                                var nullArray = false;
                                while (seen.Add(block) && block.Predecessors.ToArray() is [var parent])
                                {
                                    if (parent.Statements.LastOrDefault() is Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 } } comparison } branch
                                        && Top(comparison.Left) == Top(candidate.Array))
                                    {
                                        nullArray = (branch.Target == block.Start) == (comparison.Cond == Cond.Eq);
                                        break;
                                    }
                                    block = parent;
                                }
                                if (nullArray) { hidden.Add(pp.Target); break; }
                                candidate = null;
                            }
                        }
                    }
                    if (candidate is null) continue;
                    // 只吸收地址临时量；原数组、索引、长度以及其他用途的值仍按原路径恢复。
                    foreach (var variable in ExprMap.Walk(candidate.Start).OfType<Use>().Select(u => u.Variable)) hidden.Remove(variable);
                    if (blocks.SelectMany(b => b.Statements).Any(s => s != call
                        && !(s is Define d && hidden.Contains(d.Target)) && !(s is Phi phi && hidden.Contains(phi.Target))
                        && ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => hidden.Contains(u.Variable)))) continue;
                    arraySpans[(call, i)] = candidate;
                    runtime.UnionWith(hidden);
                }
            }
        }

        [ArgumentRule(5)]
        private ManagedValue? ArraySpanArgument(AbiValue parameter, ArgumentSite site)
        {
            if (!arraySpans.TryGetValue((site.Call, site.Index), out var span)) return null;
            var result = StructLocal(parameter.Type, 0);
            site.Output.Add(new ManagedCall(site.Call.Address, new ManagedInvocation(span.Factory, null,
                [RecoverAs(span.Array, new ArrayRef(types.Byte, 1), site.Call.Address), RecoverAs(span.Start, types.Int32, site.Call.Address)], false), result, false));
            return result;
        }
    }
}
