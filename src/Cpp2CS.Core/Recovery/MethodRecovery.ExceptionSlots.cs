using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>仅供 BeginCatch/ResumeUnwind 使用的原生异常指针备份由托管异常区域接管。</summary>
        [Analysis("异常指针栈槽", 15, After = ["异常值"])]
        private void ExceptionPointerSlots()
        {
            if (exceptionLayout is not { Succeeded: true }) return;
            var statements = blocks.SelectMany(b => b.Statements).ToArray();
            HashSet<Variable> Aliases(IEnumerable<Variable> seeds)
            {
                var result = seeds.ToHashSet();
                for (var changed = true; changed;)
                {
                    changed = false;
                    foreach (var statement in statements)
                    {
                        if (statement is Define { Value: Use { Width: 64 } use } define && result.Contains(use.Variable))
                            changed |= result.Add(define.Target);
                        if (statement is Phi phi && phi.Sources.Any(result.Contains)
                            && phi.Sources.All(v => v == phi.Target || result.Contains(v))) changed |= result.Add(phi.Target);
                    }
                }
                return result;
            }
            var pointers = Aliases(values.Where(p => p.Value is Intrinsic { Name: "eh_exception" }).Select(p => p.Key));
            var candidates = statements.OfType<Store>().Where(s => s is { Target: FrameAddress, Value: Use { Width: 64 } u } && pointers.Contains(u.Variable))
                .Select(s => ((FrameAddress)s.Target).Offset).Distinct();
            foreach (var offset in candidates)
            {
                bool Touches(Stmt statement) =>
                    statement is Store s && FrameOffset(s.Target) is { } at && at < offset + 8 && at + s.Value.Width / 8 > offset
                    || ExprMap.Operands(statement).SelectMany(ExprMap.Walk).Any(e =>
                        e is Load l && FrameOffset(l.Address) is { } start && start < offset + 8 && start + l.Width / 8 > offset
                        || FrameOffset(e) is { } address && address >= offset && address < offset + 8);
                var references = statements.Where(Touches).ToArray();
                if (references.Any(s => s switch
                    {
                        Store { Value: Use { Width: 64 } u } store => FrameOffset(store.Target) != offset || !pointers.Contains(u.Variable),
                        Define { Value: Load { Width: 64 } load } => FrameOffset(load.Address) != offset,
                        _ => true,
                    })) continue;
                var loaded = Aliases(references.OfType<Define>().Select(d => d.Target));
                bool Reads(Stmt s) => s is Phi p ? p.Sources.Any(loaded.Contains)
                    : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => loaded.Contains(u.Variable));
                if (statements.Where(Reads).Any(s => s switch
                    {
                        Define { Value: Use } d => !loaded.Contains(d.Target),
                        Phi p => !loaded.Contains(p.Target),
                        Call { Op.Kind: OpKind.BeginCatch or OpKind.ResumeUnwind, Arguments: [Use u] } => !loaded.Contains(u.Variable),
                        _ => true,
                    })) continue;
                dropped.UnionWith(references);
                runtime.UnionWith(loaded);
            }
        }
    }
}
