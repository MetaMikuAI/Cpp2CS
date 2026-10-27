using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Idioms;

/// <summary>把类型合流后的分配与无参构造移入必经分支，保留对象值的合流。</summary>
internal static class ClassPhiAllocations
{
    public static bool Run(MachineFunction function, Func<ulong, bool> constructor, Func<Variable> fresh)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        DefinitionRef? Type(Variable variable)
        {
            var seen = new HashSet<Variable>();
            while (seen.Add(variable) && definitions.TryGetValue(variable, out var value))
            {
                if (value is Symbol { Kind: SymbolKind.Class, Value: DefinitionRef type }) return type;
                if (value is not Use copy) break;
                variable = copy.Variable;
            }
            return null;
        }
        var changed = false;
        foreach (var block in function.Blocks)
        {
            var prefix = block.Statements.Where(s => s is not (Phi or Nop)).Take(2).ToArray();
            if (block.IsLandingPad || prefix is not [Call { Kind: CallKind.Direct, Op: { Kind: OpKind.NewObject, Operand: null },
                    Arguments: [Use { Width: 64 } pointer], Defines: [var created] } allocation,
                Call { Kind: CallKind.Direct, Op: null, Target: Const target, Defines.Length: 0,
                    Arguments: [Use receiver, Const { Value: 0 }] } ctor]
                || receiver.Variable != created || !constructor(target.Value)
                || block.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == pointer.Variable) is not { } phi
                || phi.Sources.Length != block.Predecessors.Count || block.Predecessors.Count < 2
                || block.Predecessors.Any(p => p == block || p.Handler != block.Handler
                    || p.NormalSuccessors.Count() != 1 || !p.NormalSuccessors.Contains(block))) continue;
            var types = phi.Sources.Select(Type).ToArray();
            if (types.Any(t => t is null || t.Definition.IsValueType)) continue;
            var sources = new Variable[types.Length];
            for (var i = 0; i < sources.Length; i++)
            {
                var parent = block.Predecessors[i];
                sources[i] = fresh();
                var at = parent.Statements.Count - (parent.Statements.LastOrDefault() is Jump ? 1 : 0);
                parent.Statements.Insert(at, allocation with { Defines = [sources[i]], Op = new(OpKind.NewObject, types[i]),
                    Arguments = [new Symbol(SymbolKind.Class, types[i]!)] });
                parent.Statements.Insert(at + 1, ctor with { Arguments = [new Use(sources[i], receiver.Width), ctor.Arguments[1]] });
            }
            block.Statements.Remove(allocation);
            block.Statements.Remove(ctor);
            block.Statements.Insert(block.Statements.TakeWhile(s => s is Phi).Count(), new Phi(allocation.Address, created, sources));
            changed = true;
        }
        return changed;
    }
}
