using Cpp2CS.Ir;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class ArrayPointerLoopsPass
{
    internal static bool ArrayPointerLoops(this IdiomState state)
    {
        int Stride(ArrayRef array) => ManagedTypes.IsReferenceType(array.Element) ? 8 : state.owner.abi.Size(array.Element);
        var arrays = state.All.OfType<Call>().Where(c => c.Op is { Kind: OpKind.NewArray, Operand: ArrayRef { IsVector: true } } && c.Defines.FirstOrDefault() is not null)
            .ToDictionary(c => c.Defines[0], c => Stride((ArrayRef)c.Op!.Operand!));
        var signatures = state.facts.EntriesAt(state.function.Entry).Select(e => e.Method).OfType<MethodRef>().Distinct().Select(m => state.owner.abi.Classify(m, out _)).ToArray();
        if (signatures.Length == 0 && state.facts.Unregistered.At(state.function.Entry) is { } identity) signatures = [identity.Abi];
        if (signatures.Length > 0 && signatures.All(s => s is not null))
            foreach (var parameter in signatures[0]!.Arguments.Where(a => a is { Type: ArrayRef { IsVector: true }, Passing: Passing.Registers, Pieces.Length: 1 }))
            {
                var register = parameter.Pieces[0].Register;
                var sizes = signatures.Select(s => s!.Arguments.FirstOrDefault(a => a.Pieces.Any(p => p.Register == register))?.Type is ArrayRef { IsVector: true } array ? Stride(array) : -1).Distinct().ToArray();
                if (sizes is [> 0 and var size]) arrays[new Variable(register, 0)] = size;
            }
        Func<Expr, TypeRef?>? typeOf = null;
        return Run(state.function, arrays, state.RawDefinition, state.Fresh,
            e => (typeOf ??= DelegateCallNormalizer.TypeQuery(state.facts, state.function))(e) is ArrayRef { IsVector: true } array ? Stride(array) : 0);
    }

    internal static bool Run(MachineFunction function, IReadOnlyDictionary<Variable, int> arrays, Func<Expr, Expr?> definition, Func<Variable> fresh, Func<Expr, int>? arrayStride = null)
    {
        Use Root(Use value)
        {
            var seen = new HashSet<Variable>();
            while (seen.Add(value.Variable) && definition(value) is Use copy)
                value = copy;
            return value;
        }
        int Stride(Use array) => arrays.TryGetValue(Root(array).Variable, out var size) ? size : arrayStride?.Invoke(array) ?? 0;
        var owners = function.Blocks.SelectMany(b => b.Statements.SelectMany(s => s switch
            { Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines.Where(v => v is not null), _ => [] }).Select(v => (Variable: v, Block: b)))
            .ToDictionary(p => p.Variable, p => p.Block);
        var dominators = Dominators.Compute(function);
        Expr Expand(Expr value, int depth = 0)
        {
            if (depth > 16) return value;
            if (value is Use use && Stride(use) == 0 && definition(use) is (Use or Const or Binary { Op: BinOp.Add or BinOp.Sub }) and var source)
                return Expand(source, depth + 1);
            return value is Binary { Op: BinOp.Add or BinOp.Sub } binary
                ? Fold.Simplify(binary with { Left = Expand(binary.Left, depth + 1), Right = Expand(binary.Right, depth + 1) }) : value;
        }

        var changed = false;
        foreach (var block in function.Blocks)
            foreach (var pointer in block.Statements.OfType<Phi>().Where(p => p.Sources.Length == 2 && block.Predecessors.Count == 2).ToArray())
            {
                for (var seed = 0; seed < 2; seed++)
                {
                    var initial = Expand(new Use(pointer.Sources[seed], 64));
                    var terms = TermsPass.Terms(initial);
                    if (terms.OfType<Use>().Where(u => Stride(u) > 0).ToArray() is not [var array]
                        || terms.OfType<Const>().Aggregate(0L, (sum, c) => sum + c.Signed) < RuntimeLayout.ArrayData
                        || ExprMap.Walk(initial).OfType<Use>().Any(u => u.Variable.Version != 0
                            && (!owners.TryGetValue(u.Variable, out var owner) || owner == block || !dominators.Dominates(owner.Index, block.Index)))
                        || Stride(array) is not (> 0 and var stride)
                        || definition(new Use(pointer.Sources[1 - seed], 64)) is not Binary { Op: BinOp.Add, Left: Use previous, Right: Const step }
                        || step.Value != (ulong)stride || previous.Variable != pointer.Target
                        || function.Blocks.SelectMany(b => b.Statements).OfType<Phi>().Any(p => p != pointer && p.Sources.Contains(pointer.Target)))
                        continue;
                    var index = block.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources.Length == 2 && definition(new Use(p.Sources[seed], 64)) is Const { Value: 0 } && definition(new Use(p.Sources[1 - seed], 64)) is Binary { Op: BinOp.Add, Left: Use prior, Right: Const { Value: 1 }, Width: 64 } && prior.Variable == p.Target);
                    if (index is null)
                    {
                        var advanceBlock = function.Blocks.FirstOrDefault(b => b.Statements.OfType<Define>().Any(d => d.Target == pointer.Sources[1 - seed]));
                        if (advanceBlock is null) continue;
                        var origin = fresh(); var next = fresh(); var selected = fresh();
                        var parent = block.Predecessors[seed];
                        parent.Statements.Insert(parent.Statements.Count - (parent.Statements.LastOrDefault() is Jump or Branch ? 1 : 0), new Define(pointer.Address, origin, Expr.C(0, 64)));
                        var advance = advanceBlock.Statements.FindIndex(s => s is Define d && d.Target == pointer.Sources[1 - seed]);
                        advanceBlock.Statements.Insert(advance + 1, new Define(advanceBlock.Statements[advance].Address, next, new Binary(BinOp.Add, new Use(selected, 64), Expr.C(1, 64), 64)));
                        var sources = new Variable[2]; sources[seed] = origin; sources[1 - seed] = next;
                        index = new Phi(pointer.Address, selected, sources);
                        block.Statements.Insert(0, index);
                    }
                    block.Statements.Remove(pointer);
                    var address = new Binary(BinOp.Add, initial, Fold.Binary(BinOp.Mul, new Use(index.Target, 64), Expr.C((ulong)stride, 64), 64), 64);
                    foreach (var current in function.Blocks)
                        for (var i = 0; i < current.Statements.Count; i++)
                            current.Statements[i] = ExprMap.MapOperands(current.Statements[i], e => ExprMap.Map(e, part => part is Use use && use.Variable == pointer.Target ? address : null));
                    changed = true;
                    break;
                }
            }

        return changed;
    }
}
