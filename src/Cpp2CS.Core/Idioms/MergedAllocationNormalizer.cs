using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Idioms;

/// <summary>把两臂末尾的同类型分配合并到共同构造处，保留分支选出的构造参数。</summary>
internal static class MergedAllocationNormalizer
{
    public static bool Run(MachineFunction function, ProgramFacts facts)
    {
        var changed = false;
        foreach (var block in function.Blocks)
            foreach (var phi in block.Statements.OfType<Phi>().ToArray())
            {
                if (!block.Statements.Contains(phi) || phi.Sources.Length < 2 || phi.Sources.Length != block.Predecessors.Count) continue;
                var allocations = new List<(Block Block, Call Call)>();
                foreach (var (pred, source) in block.Predecessors.Zip(phi.Sources))
                {
                    var at = pred.Statements.FindIndex(s => s is Call { Op.Kind: OpKind.NewObject } c && c.Defines.FirstOrDefault() == source);
                    if (at < 0 || pred.NormalSuccessors.ToArray() is not [var next] || next != block) break;
                    allocations.Add((pred, (Call)pred.Statements[at]));
                }
                if (allocations.Count != phi.Sources.Length || allocations.Select(a => a.Call.Op!.Operand).Distinct().ToArray() is not [DefinitionRef type]) continue;
                var aliases = block.Statements.OfType<Phi>().Where(p => p.Sources.SequenceEqual(phi.Sources)).ToArray();
                var aliasTargets = aliases.Select(p => p.Target).ToHashSet();
                var constructor = block.Statements.OfType<Call>().FirstOrDefault();
                if (constructor is not { Op: null, Target: Const target, Arguments: [Use receiver, ..] }
                    || !aliasTargets.Contains(receiver.Variable)
                    || !facts.EntriesAt(target.Value).Any(e => e.Method is { Method.Name: ".ctor" } m && m.Method.Owner == type.Definition)) continue;
                if (function.Blocks.SelectMany(b => b.Statements).Except(aliases).Any(s => phi.Sources.Any(v => AllocationPairing.Uses(s, v)))) continue;
                var prefix = block.Statements.TakeWhile(s => !ReferenceEquals(s, constructor)).Where(s => s is not Phi).ToArray();
                if (allocations.Any(a => AllocationPairing.MotionProblem(function.Range, a.Block, a.Call, block, constructor,
                    a.Block.Statements.Skip(a.Block.Statements.IndexOf(a.Call) + 1).Where(s => s is not Jump).Concat(prefix), a.Call.Defines[0]!) is not null)) continue;
                foreach (var alias in aliases) block.Statements.Remove(alias);
                foreach (var allocation in allocations) allocation.Block.Statements.Remove(allocation.Call);
                var merged = allocations[0].Call with { Address = constructor.Address, Defines = [phi.Target] };
                block.Statements.Insert(block.Statements.IndexOf(constructor), merged);
                foreach (var current in function.Blocks)
                    for (var i = 0; i < current.Statements.Count; i++)
                    {
                        if (current.Statements[i] is Phi p)
                            current.Statements[i] = p with { Sources = p.Sources.Select(v => aliasTargets.Contains(v) ? phi.Target : v).ToArray() };
                        else current.Statements[i] = ExprMap.MapOperands(current.Statements[i], e => ExprMap.Map(e,
                            x => x is Use u && aliasTargets.Contains(u.Variable) ? u with { Variable = phi.Target } : null));
                    }
                changed = true;
            }
        return changed;
    }
}
