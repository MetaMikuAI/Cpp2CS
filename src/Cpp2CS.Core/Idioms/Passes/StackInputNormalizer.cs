using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>AAPCS64 栈上传入的标量、浮点聚合分量及隐藏 MethodInfo：只读且不传址时改写成入口 SSA 值。</summary>
internal static class StackInputNormalizer
{
    public static bool Run(MachineFunction function, ManagedAbi abi, AbiSignature[] signatures, out int? methodInfoOffset)
    {
        methodInfoOffset = null;
        if (signatures.Length == 0) return false;
        var layouts = signatures.Select(abi.StackArguments).ToArray();
        Dictionary<int, int> Slots(StackAbiSignature layout)
        {
            var slots = layout.Parameters.Where(p => !p.Indirect && p.Size is 1 or 2 or 4 or 8
                && abi.Kind(p.Type) is ValueKind.Integer or ValueKind.Reference or ValueKind.Float or ValueKind.Double)
                .ToDictionary(p => p.Offset, p => p.Size * 8);
            foreach (var parameter in layout.Parameters.Where(p => !p.Indirect && abi.Kind(p.Type) == ValueKind.Struct))
                if (abi.Hfa(parameter.Type) is { } hfa)
                    for (var i = 0; i < hfa.Count; i++) slots.Add(parameter.Offset + i * hfa.Width / 8, hfa.Width);
            if (layout.MethodInfoOffset is { } hidden) slots.Add(hidden, 64);
            return slots;
        }
        var candidates = Slots(layouts[0]);
        foreach (var layout in layouts.Skip(1))
        {
            var slots = Slots(layout);
            foreach (var offset in candidates.Keys.Where(o => slots.GetValueOrDefault(o) != candidates[o]).ToArray()) candidates.Remove(offset);
        }
        if (candidates.Count == 0) return false;
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var aliases = new Dictionary<Variable, long>();
        long? Offset(Expr expression) => expression switch
        {
            FrameAddress f => f.Offset,
            Use u when aliases.TryGetValue(u.Variable, out var at) => at,
            Binary { Op: BinOp.Add, Right: Const c } b when Offset(b.Left) is { } at => at + c.Signed,
            Binary { Op: BinOp.Sub, Right: Const c } b when Offset(b.Left) is { } at => at - c.Signed,
            _ => null,
        };
        var definitions = statements.OfType<Define>().Concat(function.Dead.Select(d => d.Define)).ToArray();
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var define in definitions)
                if (!aliases.ContainsKey(define.Target) && Offset(define.Value) is { } at) { aliases.Add(define.Target, at); changed = true; }
        }
        var escaped = new List<long>();
        void Visit(Expr expression)
        {
            if (expression is Load load && Offset(load.Address) is not null) return;
            if (Offset(expression) is { } at) { if (at >= 0) escaped.Add(at); return; }
            foreach (var child in ExprMap.Children(expression)) Visit(child);
        }
        foreach (var statement in statements)
        {
            if (statement is Define define && aliases.ContainsKey(define.Target)) continue;
            if (statement is Store store && Offset(store.Target) is { } at)
            {
                foreach (var offset in candidates.Keys.Where(o => at < o + candidates[o] / 8 && o < at + store.Value.Width / 8).ToArray())
                    candidates.Remove(offset);
                Visit(store.Value);
            }
            else if (statement is Phi phi)
            {
                foreach (var source in phi.Sources) Visit(new Use(source, source.Width));
            }
            else foreach (var operand in ExprMap.Operands(statement)) Visit(operand);
        }
        foreach (var offset in candidates.Keys.Where(o => escaped.Any(at => at <= o)).ToArray()) candidates.Remove(offset);
        if (candidates.Count == 0) return false;
        var promoted = new HashSet<int>();
        Expr? Map(Expr expression)
        {
            if (expression is not Load load || Offset(load.Address) is not { } at || at < 0 || at > int.MaxValue)
                return null;
            var parts = new List<(int Offset, int Width)>();
            for (var covered = 0; covered < load.Width;)
            {
                var offset = checked((int)at + covered / 8);
                if (!candidates.TryGetValue(offset, out var width) || covered + width > load.Width)
                    return null;
                parts.Add((offset, width));
                covered += width;
            }
            // 合并读取仍须完整覆盖连续的已知参数片，不读取对齐填充。
            Expr result = new Const(0, load.Width);
            foreach (var part in parts)
            {
                promoted.Add(part.Offset);
                var value = new Use(new Variable(Storage.Slot(part.Offset), 0), part.Width);
                result = parts.Count == 1 ? value : new Insert(result, value, checked((int)(part.Offset - at) * 8));
            }
            return result;
        }
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Map));
        if (layouts[0].MethodInfoOffset is { } hiddenOffset && promoted.Contains(hiddenOffset)
            && layouts.All(l => l.MethodInfoOffset == hiddenOffset)) methodInfoOffset = hiddenOffset;
        return promoted.Count > 0;
    }
}
