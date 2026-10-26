using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        // AsSpan(string) 内联后以数据引用、长度两个寄存器传递；null 路径二者同时为零。
        [ArgumentRule(6)]
        private ManagedValue? StringSpanArgument(AbiValue parameter, ArgumentSite site)
        {
            if (parameter is not { Type: DefinitionRef { Definition.FullName: "System.ReadOnlySpan", Arguments: [var element] },
                Passing: Passing.Registers, Pieces: [var data, var length] }
                || !element.Equals(types.Char) || data.Offset != 0 || length.Offset != 8
                || !site.Registers.TryGetValue(data.Register, out var pointer) || !site.Registers.TryGetValue(length.Register, out var count)
                || types.CorlibMethod("System.MemoryExtensions", "AsSpan", types.String) is not { } asSpan
                || !asSpan.Method.ReturnType.Equals(parameter.Type)) return null;
            Expr Top(Expr e, int depth = 0) => depth > 16 ? e : e switch
            {
                Ir.Convert c => Top(c.Operand, depth + 1),
                Use u when values.TryGetValue(u.Variable, out var value) => Top(value, depth + 1),
                _ => e,
            };
            Expr? Source(Expr p, Expr n)
            {
                if (Top(p) is not Use u || !results.TryGetValue(u.Variable, out var result)
                    || Resolve(result.Call) is not { Method: { Owner.FullName: "System.String", Name: "GetRawStringData" } }
                    || result.Call.Arguments.FirstOrDefault() is not { } text) return null;
                return Top(n) is Load { Width: 32, Address: Binary { Op: BinOp.Add, Left: var root, Right: Const { Value: 16 } } }
                    && Top(root) == Top(text) ? text : null;
            }
            bool NullPath(Flow.Block block, Expr text)
            {
                var seen = new HashSet<Flow.Block>();
                while (seen.Add(block) && block.Predecessors.ToArray() is [var parent])
                {
                    if (parent.Statements.LastOrDefault() is Branch branch)
                        return branch.Condition is Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 } } comparison
                            && Top(comparison.Left) == Top(text) && (branch.Target == block.Start) == (comparison.Cond == Cond.Eq);
                    block = parent;
                }
                return false;
            }
            Expr? source = Source(pointer, count);
            if (source is null && Top(pointer) is Use p && phis.TryGetValue(p.Variable, out var pp)
                && Top(count) is Use n && phis.TryGetValue(n.Variable, out var np)
                && pp.Sources.Length == 2 && np.Sources.Length == 2
                && blocks.FirstOrDefault(b => b.Statements.Contains(pp) && b.Statements.Contains(np)) is { Predecessors.Count: 2 } join)
            {
                for (var i = 0; i < 2; i++)
                    if (Top(new Use(pp.Sources[1 - i], 64)) is Const { Value: 0 }
                        && Top(new Use(np.Sources[1 - i], 64)) is Const { Value: 0 })
                        if (Source(new Use(pp.Sources[i], 64), new Use(np.Sources[i], 64)) is { } text && NullPath(join.Predecessors[1 - i], text)) source = text;
            }
            if (source is null) return null;
            var local = StructLocal(parameter.Type, 0);
            site.Output.Add(new ManagedCall(site.Call.Address, new ManagedInvocation(asSpan, null,
                [RecoverAs(source, types.String, site.Call.Address)], false), local, false));
            return local;
        }
    }
}
