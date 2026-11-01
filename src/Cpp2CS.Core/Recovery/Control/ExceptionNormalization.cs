using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// C++ 异常机制到 IL 异常语义的规范化。IL2CPP 的托管异常总以 Il2CppExceptionWrapper 抛出：落地块中 selector 对托管异常
/// 恒为 LSDA 里 catch(Il2CppExceptionWrapper&amp;) 动作的序号（没有 catch 动作时为 0，即只做清理），其余分支对 IL 不可达。
/// 只调用 std::terminate 的落地块表示 noexcept 析构中再次抛出，IL 中异常照常向外传播，指向它的异常边删去。
/// clang 为每个调用点生成的落地跳板（只含跳转）合并到跳转目标：异常边直接指向目标，目标成为落地块。
/// </summary>
internal static class ExceptionNormalization
{
    public static void Run(MachineFunction function)
    {
        if (!function.Blocks.Any(b => b.IsLandingPad)) return;
        foreach (var pad in function.Blocks.Where(b => b.IsLandingPad))
        {
            var filter = function.Range.ExceptionRegions.Where(r => r.LandingPad == pad.Start).SelectMany(r => r.Actions)
                .FirstOrDefault(a => a.Kind == "typed-catch")?.Filter ?? 0;
            for (var i = 0; i < pad.Statements.Count; i++)
                if (pad.Statements[i] is Define { Value: Intrinsic { Name: "eh_selector" } } selector)
                    pad.Statements[i] = selector with { Value = Expr.C(unchecked((ulong)filter), selector.Value.Width) };
        }
        foreach (var block in function.Blocks.ToArray())
            if (block.Handler is { } pad && Terminates(pad))
                MachineFunction.RemoveEdgeAt(block, block.Successors.Count - 1);
        MergeTrampolines(function);
        Machine.Ssa.Lowering.Cleanup(function);
        while (FoldBranches(function))
            Machine.Ssa.Lowering.Cleanup(function);
    }

    /// <summary>只含跳转的落地块：异常边改指跳转目标，目标 φ 的来源取跳板提供的值。</summary>
    private static void MergeTrampolines(MachineFunction function)
    {
        foreach (var pad in function.Blocks.Where(b => b.IsLandingPad).ToArray())
        {
            if (pad.Statements.Any(s => s is not (Jump or Nop)) || pad.Successors is not [var target] || target == pad) continue;
            var through = target.Predecessors.IndexOf(pad);
            var sources = target.Statements.TakeWhile(s => s is Phi).Cast<Phi>().Select(p => p.Sources[through]).ToArray();
            foreach (var thrower in pad.Predecessors.Where(p => p.Handler == pad).ToArray())
            {
                MachineFunction.RemoveEdgeAt(thrower, thrower.Successors.Count - 1);
                MachineFunction.AddEdge(thrower, target);
                thrower.Handler = target;
                for (var i = 0; i < sources.Length; i++)
                {
                    var phi = (Phi)target.Statements[i];
                    target.Statements[i] = phi with { Sources = [.. phi.Sources, sources[i]] };
                }
            }
            target.IsLandingPad = true;
        }
        function.Renumber();
    }

    /// <summary>落地块只取异常并调用 std::terminate。</summary>
    private static bool Terminates(Block pad) => pad.Statements.All(s => s is Define { Value: Intrinsic { Name: "eh_exception" or "eh_selector" } } or Define { Value: Const } or Nop
        || s is Call { Op.Kind: OpKind.Terminate or OpKind.BeginCatch });

    /// <summary>条件为常量的分支改为跳转，删去不可达的边。</summary>
    private static bool FoldBranches(MachineFunction function)
    {
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch branch || Fold.Simplify(branch.Condition) is not Const c) continue;
            var (kept, dropped) = c.Value != 0 ? (branch.Target, branch.Fallthrough) : (branch.Fallthrough, branch.Target);
            block.Statements[^1] = new Jump(branch.Address, kept);
            if (kept != dropped && block.Successors.FirstOrDefault(s => s.Start == dropped) is { } dead)
                MachineFunction.RemoveEdge(block, dead);
            changed = true;
        }
        if (changed) function.Renumber();
        return changed;
    }
}
