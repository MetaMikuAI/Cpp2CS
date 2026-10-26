using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>小型状态分派的精确分区：同一 int 字段的相等、有限范围和范围内位掩码判断。</summary>
internal sealed record StateDispatch(Expr Receiver, int Offset, IReadOnlyDictionary<uint, ulong[]> Cases, ulong[] Otherwise)
{
    internal bool Same(StateDispatch other) => Offset == other.Offset && Otherwise.SequenceEqual(other.Otherwise)
        && Cases.Keys.Concat(other.Cases.Keys).Distinct().All(k => Cases.GetValueOrDefault(k, Otherwise).SequenceEqual(other.Cases.GetValueOrDefault(k, other.Otherwise)));

    internal static StateDispatch? Read(MachineFunction function, Func<Call, Call?> managedCall)
    {
        if (function.Blocks.Count > 24 || function.Range.ExceptionRegions.Any()) return null;
        // 入口在循环中时 CFG 会增加同地址的空入口块；这种图不属于按地址解释的小型状态分派。
        if (function.Blocks.Select(b => b.Start).Distinct().Count() != function.Blocks.Count) return null;
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
        bool Partition(Expr e)
        {
            if (e is Logical l) return Partition(l.Left) && Partition(l.Right);
            if (e is Not n) return Partition(n.Operand);
            if (e is not Compare c) return false;
            if (Affine(c.Left, out var x, out var a) && Affine(c.Right, out var y, out var b) && x != y)
            {
                if (c.Cond is Cond.Eq or Cond.Ne)
                { constants.Add(x == 1 ? unchecked(b - a) : unchecked(a - b)); return true; }
                if (c.Cond is Cond.Ugt or Cond.Ule && x == 1 && y == 0 && b <= 256)
                {
                    for (uint i = 0; i <= b; i++) constants.Add(unchecked(i - a));
                    return true;
                }
            }
            return BitTest(c);
        }
        bool BitTest(Compare c) => c is { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 },
            Left: Binary { Op: BinOp.And, Right: Const, Left: Binary { Op: BinOp.Shl, Left: Const { Value: 1 }, Right: var shift } } }
            && Affine(shift, out var coefficient, out _) && coefficient == 1;
        bool Condition(Expr e, uint state, out bool result)
        {
            result = false;
            if (e is Logical l)
            {
                if (!Condition(l.Left, state, out var left)) return false;
                // 范围外必须由范围守卫短路，不能用一个取样值推断周期性的位掩码。
                if (l.IsAnd != left) { result = left; return true; }
                return Condition(l.Right, state, out result);
            }
            if (e is Not n && Condition(n.Operand, state, out var operand)) { result = !operand; return true; }
            if (e is not Compare c || BitTest(c) && !constants.Contains(state)) return false;
            var evaluated = Fold.Simplify(ExprMap.Map(c, part => part == field ? Expr.C(state, 32) : null));
            if (evaluated is not Const value) return false;
            result = value.Value != 0;
            return true;
        }
        foreach (var statement in blocks.Values.SelectMany(s => s))
        {
            if (statement is Branch branch && !Partition(branch.Condition)) return null;
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
