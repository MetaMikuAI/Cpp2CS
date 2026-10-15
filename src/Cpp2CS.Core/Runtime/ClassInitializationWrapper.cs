using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Runtime;

/// <summary>类初始化包装：只接受同一参数的初始化、完成标志分支和私有栈保存。</summary>
public static class ClassInitializationWrapper
{
    public static bool Matches(MachineFunction function, CallingConvention convention, int constructorFinished, Func<ulong, bool> isClassInit)
    {
        if (function.Problems.Count != 0 || function.Blocks.Any(b => b.Handler is not null || b.IsLandingPad
            || b.Statements.SkipLast(1).Any(s => s is Branch or Jump or Return))) return false;
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var argument = new Use(new Variable(convention.IntegerArguments[0], 0), 64);
        if (statements.OfType<Call>().ToArray() is not [var call] || call is not { Kind: CallKind.Direct or CallKind.Tail, Target: Const target }
            || !isClassInit(target.Value) || statements.OfType<Return>().ToArray() is not [var ret] || ret.Value != argument) return false;
        var index = Array.IndexOf(call.Sources, convention.IntegerArguments[0]);
        if (index < 0 || index >= call.Arguments.Length || call.Arguments[index] != argument) return false;
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr value, HashSet<Variable> seen)
        {
            if (value is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var source))
                return Fold.Convert(ConvKind.Truncate, Expand(source, seen), use.Width);
            if (value is Ir.Convert convert) return Fold.Convert(convert.Kind, Expand(convert.Operand, seen), convert.Width);
            return value;
        }
        var branches = statements.OfType<Branch>().ToArray();
        Load? flag = null;
        if (branches is [var branch])
        {
            if (Expand(branch.Condition, []) is not Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 } } comparison
                || Expand(comparison.Left, []) is not Load { Width: 32, Address: Binary { Op: BinOp.Add, Right: Const offset } address } load
                || address.Left != argument || offset.Value != (ulong)constructorFinished || function.Blocks.Count != 3) return false;
            flag = load;
            var entry = function.EntryBlock;
            var initialize = function.Blocks.Single(b => b.Statements.Contains(call));
            var exit = function.Blocks.Single(b => b.Statements.Contains(ret));
            var returnsToExit = call.Kind == CallKind.Direct && initialize.Statements.LastOrDefault() is Jump jump && jump.Target == exit.Start
                && initialize.Successors.Count == 1 && initialize.Successors[0] == exit;
            var tailExits = call.Kind == CallKind.Tail && initialize.Statements.LastOrDefault() == call && initialize.Successors.Count == 0;
            if (entry == initialize || entry == exit || initialize == exit || entry.Statements.LastOrDefault() != branch
                || !(returnsToExit || tailExits) || exit.Statements.LastOrDefault() != ret
                || entry.Successors.Count != 2 || !entry.Successors.Contains(initialize) || !entry.Successors.Contains(exit)
                || exit.Successors.Count != 0
                || (comparison.Cond == Cond.Eq ? branch.Target : branch.Fallthrough) != initialize.Start
                || (comparison.Cond == Cond.Eq ? branch.Fallthrough : branch.Target) != exit.Start) return false;
        }
        else if (call.Kind != CallKind.Direct || branches.Length != 0 || function.Blocks.Count != 1 || function.EntryBlock.Successors.Count != 0
            || function.EntryBlock.Statements.LastOrDefault() != ret) return false;
        foreach (var statement in statements)
        {
            if (statement == call || statement == ret || statement is Branch or Jump) continue;
            if (statement is Nop { Text: "branch to next" or "hint #0" or "prfm" }) continue;
            if (statement is Store { Target: FrameAddress frame, Value: Use { Variable.Version: 0 } saved }
                && saved.Width % 8 == 0 && frame.Offset < 0 && frame.Offset + saved.Width / 8 <= 0) continue;
            if (statement is Define define && ExprMap.Walk(define.Value).All(e => e switch
            {
                Load load => load == flag,
                Intrinsic or Unknown or Read => false,
                _ => true,
            })) continue;
            return false;
        }
        return true;
    }
}
