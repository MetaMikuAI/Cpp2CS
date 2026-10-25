using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>小型状态分派的精确分区：条件仅由同一 int 字段与常量的相等比较组成。</summary>
internal sealed record StateDispatch(Expr Receiver, int Offset, IReadOnlyDictionary<uint, ulong[]> Cases, ulong[] Otherwise)
{
    internal bool Same(StateDispatch other) => Offset == other.Offset && Otherwise.SequenceEqual(other.Otherwise)
        && Cases.Keys.Concat(other.Cases.Keys).Distinct().All(k => Cases.GetValueOrDefault(k, Otherwise).SequenceEqual(other.Cases.GetValueOrDefault(k, other.Otherwise)));

    internal static StateDispatch? Read(MachineFunction function, Func<Call, Call?> managedCall)
    {
        if (function.Blocks.Count > 24 || function.Range.ExceptionRegions.Any()) return null;
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr e, int depth = 0) => depth > 32 ? new Unknown("状态分派循环", e.Width) : Fold.Simplify(ExprMap.Map(e,
            p => p is Use u && definitions.TryGetValue(u.Variable, out var value)
                ? Fold.Convert(value.Width < u.Width ? ConvKind.ZeroExtend : ConvKind.Truncate, Expand(value, depth + 1), u.Width) : null));
        var blocks = function.Blocks.ToDictionary(b => b.Start, b => b.Statements.Select(s => ExprMap.MapOperands(s, e => Expand(e))).ToArray());
        var calls = blocks.Values.SelectMany(s => s).OfType<Call>().ToArray();
        var normalized = calls.Select(managedCall).ToArray();
        if (normalized.Length == 0 || normalized.Any(c => c is not { Op: null, Target: Const, Arguments.Length: 1 })) return null;
        var receiver = normalized[0]!.Arguments[0];
        if (normalized.Any(c => c!.Arguments[0] != receiver)) return null;
        var loads = blocks.Values.SelectMany(s => s).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Load>()
            .Where(l => l is { Width: 32, Address: Binary { Op: BinOp.Add, Right: Const } b } && b.Left == receiver).Distinct().ToArray();
        if (loads is not [var field]) return null;
        var offset = ((Const)((Binary)field.Address).Right).Value;
        if (offset > int.MaxValue) return null;
        var constants = new HashSet<uint>();
        bool Affine(Expr e, out int coefficient, out uint constant)
        {
            coefficient = 0; constant = 0;
            if (e == field) { coefficient = 1; return true; }
            if (e is Const c && c.Width <= 32) { constant = (uint)c.Value; return true; }
            if (e is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Width: >= 32, Operand.Width: >= 32 } cast)
                return Affine(cast.Operand, out coefficient, out constant);
            if (e is Binary { Op: BinOp.Add or BinOp.Sub, Width: 32 } b
                && Affine(b.Left, out var left, out var lc) && Affine(b.Right, out var right, out var rc))
            {
                coefficient = b.Op == BinOp.Add ? left + right : left - right;
                constant = b.Op == BinOp.Add ? unchecked(lc + rc) : unchecked(lc - rc);
                return coefficient is 0 or 1;
            }
            return false;
        }
        bool Condition(Expr e, uint state, out bool result)
        {
            result = false;
            if (e is Logical l && Condition(l.Left, state, out var left) && Condition(l.Right, state, out var right))
            { result = l.IsAnd ? left && right : left || right; return true; }
            if (e is Not n && Condition(n.Operand, state, out var operand)) { result = !operand; return true; }
            if (e is not Compare { Cond: Cond.Eq or Cond.Ne } c || !Affine(c.Left, out var x, out var a)
                || !Affine(c.Right, out var y, out var b) || x == y) return false;
            constants.Add(x == 1 ? unchecked(b - a) : unchecked(a - b));
            result = unchecked((uint)x * state + a) == unchecked((uint)y * state + b);
            if (c.Cond == Cond.Ne) result = !result;
            return true;
        }
        foreach (var statement in blocks.Values.SelectMany(s => s))
        {
            if (statement is Branch branch && !Condition(branch.Condition, 0, out _)) return null;
            if (statement is not (Define or Branch or Jump or Return { Value: null } or Call or Nop)) return null;
            if (ExprMap.Operands(statement).SelectMany(ExprMap.Walk).Any(e => e is Unknown or Intrinsic or FrameAddress)) return null;
            // 接收者链和状态字段以外的读取不能在匹配时丢失。
            if (ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Load>()
                .Any(l => l != field && !ExprMap.Walk(receiver).Contains(l))) return null;
        }
        ulong[]? Run(uint state)
        {
            var visited = new HashSet<ulong>();
            var current = function.Entry;
            var trace = new List<ulong>();
            while (visited.Add(current) && blocks.TryGetValue(current, out var statements))
            {
                ulong? next = null;
                foreach (var statement in statements)
                {
                    // 清理调用可能改变状态；其后的代码只能结束，不能继续用旧状态解释分支。
                    if (trace.Count != 0 && statement is not (Return or Jump or Nop)) return null;
                    if (statement is Call call)
                    {
                        trace.Add(((Const)call.Target).Value);
                        if (call.Kind == CallKind.Tail) return trace.ToArray();
                    }
                    if (statement is Return) return trace.ToArray();
                    if (statement is Jump jump) next = jump.Target;
                    if (statement is Branch branch)
                    {
                        if (!Condition(branch.Condition, state, out var taken)) return null;
                        next = taken ? branch.Target : branch.Fallthrough;
                    }
                }
                if (next is null) return null;
                current = next.Value;
            }
            return null;
        }
        uint outside = 0;
        while (constants.Contains(outside)) outside++;
        if (Run(outside) is not { } otherwise) return null;
        var cases = new Dictionary<uint, ulong[]>();
        foreach (var constant in constants.ToArray())
        {
            if (Run(constant) is not { } trace) return null;
            cases[constant] = trace;
        }
        return new(receiver, (int)offset, cases, otherwise);
    }
}
