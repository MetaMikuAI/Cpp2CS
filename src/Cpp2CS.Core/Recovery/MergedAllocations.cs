using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>互斥分支分配同一类型、汇合后统一构造时，证明纯路径后把分配并到构造前。</summary>
internal static class MergedAllocations
{
    internal static bool Run(MachineFunction function, Func<Call, DefinitionRef, bool> constructor)
    {
        if (function.Range.ExceptionRegions.Length != 0) return false;
        var changed = false;
        Dominators? dominators = null;
        foreach (var destination in function.Blocks)
        {
            if (destination.IsLandingPad || destination.Handler is not null || destination.Predecessors.Count is < 2 or > 4
                || destination.Statements.FirstOrDefault(s => s is not (Phi or Nop)) is not Call
                    { Kind: CallKind.Direct, Op: null, Sources: [var receiver, ..], Arguments: [Use { Width: 64 } self, ..] } call
                || receiver != Storage.Gpr(0)) continue;
            var phis = destination.Statements.OfType<Phi>().ToArray();
            if (phis.FirstOrDefault(p => p.Target == self.Variable) is not { } merged
                || merged.Sources.Length != destination.Predecessors.Count || merged.Sources.Distinct().Count() < 2) continue;
            var allocations = function.Blocks.SelectMany(b => b.Statements.OfType<Call>().Where(c => c is
                    { Kind: CallKind.Direct, Op: { Kind: OpKind.NewObject, Operand: DefinitionRef }, Defines: [not null] })
                .Select(c => (Block: b, Call: c))).ToDictionary(p => p.Call.Defines[0]);
            if (merged.Sources.Any(v => !allocations.ContainsKey(v))) continue;
            var sources = merged.Sources.Distinct().Select(v => allocations[v]).ToArray();
            var first = sources[0].Call;
            var type = (DefinitionRef)first.Op!.Operand!;
            if (!constructor(call, type) || sources.Any(p => !Equals(p.Call.Op!.Operand, type)
                || p.Call.Arguments.Any(a => a is not (Symbol or Const))
                || !p.Call.Arguments.SequenceEqual(first.Arguments))) continue;
            var aliases = phis.Where(p => p.Sources.SequenceEqual(merged.Sources)).ToHashSet();
            var created = merged.Sources.ToHashSet();
            if (function.Blocks.SelectMany(b => b.Statements).Any(s => s is Phi phi
                    ? !aliases.Contains(phi) && phi.Sources.Any(created.Contains)
                    : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => created.Contains(u.Variable)))) continue;
            dominators ??= Dominators.Compute(function);
            if (merged.Sources.Select((v, i) => (Allocation: allocations[v], Parent: destination.Predecessors[i]))
                    .Any(p => !dominators.Dominates(p.Allocation.Block.Index, p.Parent.Index))
                || sources.Any(p => !PurePaths(p.Block, p.Block.Statements.IndexOf(p.Call) + 1, destination))) continue;

            foreach (var source in sources) source.Block.Statements.Remove(source.Call);
            var aliasVariables = aliases.Select(p => p.Target).ToHashSet();
            destination.Statements.RemoveAll(s => s is Phi p && aliases.Contains(p));
            // 其余 phi 保留原入边顺序；对象别名改为同一已构造对象。
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var statement = block.Statements[i];
                    block.Statements[i] = statement is Phi phi
                        ? phi with { Sources = phi.Sources.Select(v => aliasVariables.Contains(v) ? self.Variable : v).ToArray() }
                        : ExprMap.MapOperands(statement, e => ExprMap.Map(e, value => value is Use u
                            && aliasVariables.Contains(u.Variable) ? new Use(self.Variable, u.Width) : null));
                }
            var position = destination.Statements.FindIndex(s => s is not (Phi or Nop));
            destination.Statements.Insert(position, first with { Address = call.Address, Defines = [self.Variable] });
            changed = true;
        }
        return changed;
    }

    private static bool PurePaths(Block source, int start, Block destination)
    {
        var active = new HashSet<Block>();
        var complete = new HashSet<Block>();
        return Visit(source, start);

        bool Visit(Block block, int index)
        {
            if (block == destination) return true;
            if (block.IsLandingPad || block.Handler is not null || active.Contains(block)) return false;
            if (complete.Contains(block)) return true;
            active.Add(block);
            if (block.Statements.Skip(index).Any(s => s switch
                {
                    Nop or Phi or Jump => false,
                    Define d => !Pure(d.Value),
                    Branch b => !Pure(b.Condition),
                    _ => true,
                }) || !block.NormalSuccessors.Any() || block.NormalSuccessors.Any(next => !Visit(next, 0))) return false;
            active.Remove(block);
            complete.Add(block);
            return true;
        }
    }

    private static bool Pure(Expr expression) => ExprMap.Walk(expression).All(e => e is Const or Use or Symbol
        or Binary or Unary or Ir.Convert or Compare or Select or Logical or Not or Extract or Insert);
}
