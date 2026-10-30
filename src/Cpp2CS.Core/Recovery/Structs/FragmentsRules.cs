using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class FragmentsRules
{
    /// <summary>恢复期间遍历结构体片的叶子；最终方法体仍须通过片残留检查。</summary>
    internal static IEnumerable<ManagedValue> WalkRecoveryValue(ManagedValue value)
    {
        var children = value is Fragment fragment ? fragment.Parts.Select(p => p.Value) : value is AggregatePiece part ? [part.Root] : ManagedValues.Children(value);
        return children.SelectMany(FragmentsRules.WalkRecoveryValue).Prepend(value);
    }

    internal static LocalValue StructLocal(this RecoveryScope ctx, TypeRef type, int width) => new(new Variable(Storage.Temp(ctx.State.Structs.Locals.Next()), 1), type, width);
    /// <summary>循环中的结构体片按相同叶子汇合；填充仍没有值，不能借助零初值把填充变成整数。</summary>
    [Analysis("片汇合", 98, After = ["结构体写入汇合"])]
    internal static void PrepareFragmentPhis(this RecoveryScope ctx)
    {
        var phis = ctx.blocks.SelectMany(b => b.Statements).OfType<Phi>().ToArray();
        var targets = phis.Select(p => p.Target).ToHashSet();
        var links = phis.SelectMany(p => p.Sources.SelectMany(s => new[] { (From: p.Target, To: s), (From: s, To: p.Target) })).ToLookup(p => p.From, p => p.To);
        var seen = new HashSet<Variable>();
        foreach (var phi in phis)
        {
            if (seen.Contains(phi.Target))
                continue;
            var web = new HashSet<Variable>();
            var pending = new Stack<Variable>();
            pending.Push(phi.Target);
            while (pending.TryPop(out var next))
                if (web.Add(next))
                    foreach (var linked in links[next])
                        pending.Push(linked);
            seen.UnionWith(web);
            var width = phi.Target.Width;
            if (width is not (64 or 128) || web.Any(v => v.Width != width || ctx.State.Structs.structPhiMembers.ContainsKey(v)))
                continue;
            var fragments = new List<Fragment>();
            var zeros = new List<Variable>();
            var complete = true;
            foreach (var source in web.Where(v => !targets.Contains(v)))
            {
                if (ctx.values.GetValueOrDefault(source) is Const { Value: 0 } zero && zero.Width == width)
                {
                    zeros.Add(source);
                    continue;
                }

                if (!ctx.Variable(source, width).TryGet(out var value, out _) || value is not Fragment fragment)
                {
                    complete = false;
                    break;
                }

                fragments.Add(fragment);
            }

            if (!complete || fragments.Count == 0)
                continue;
            var shape = fragments[0].Parts.Select(p => (p.Low, p.Value.Type, p.Value.Width)).ToArray();
            if (fragments.Any(f => !f.Parts.Select(p => (p.Low, p.Value.Type, p.Value.Width)).SequenceEqual(shape)))
                continue;
            foreach (var target in web.Where(targets.Contains))
                ctx.State.Structs.fragmentLocals[target] = new Fragment(shape.Select(p => new Part(p.Low, ctx.StructLocal(p.Type, p.Width))).ToArray(), ctx.types.UInt64, width);
            ctx.State.Lowering.inlined.UnionWith(zeros);
        }
    }

    internal static RecoveryResult<Fragment?> MemoryFragment(this RecoveryScope ctx, Expr root, TypeRef type, long offset, int width)
    {
        if (type is not (ByRefRef or DefinitionRef))
            return (Fragment?)null;
        var leaves = ctx.ScalarStructPaths(type).ToArray();
        if (leaves.Any(p => p.Offset < offset + width / 8 && offset < p.Offset + ctx.types.Size(p.Type) && (p.Offset < offset || p.Offset + ctx.types.Size(p.Type) > offset + width / 8)))
            return (Fragment?)null;
        var paths = leaves.Where(p => p.Offset >= offset && p.Offset + ctx.types.Size(p.Type) <= offset + width / 8).OrderBy(p => p.Offset).ToArray();
        // 叶子之间可以有填充（如 ValueTuple<bool, int> 的 3 字节）：片只按叶子使用，打包成整数时才因填充报洞。
        var cursor = offset;
        var gaps = false;
        foreach (var p in paths)
        {
            if (p.Offset < cursor)
                return (Fragment?)null;
            gaps |= p.Offset != cursor;
            cursor = p.Offset + ctx.types.Size(p.Type);
        }

        gaps |= cursor != offset + width / 8;
        if (paths.Length == 0 || paths.Length < 2 && !gaps || cursor > offset + width / 8)
            return (Fragment?)null;
        if (!ctx.Recover(root, null).TryGet(out var value, out var failure))
            return failure;
        return new Fragment(paths.Select(p => new Part((p.Offset - (int)offset) * 8, ctx.PathValue(value, p.Path))).ToArray(), ctx.types.UInt64, width);
    }

    internal static RecoveryResult<Fragment?> FragmentVariable(this RecoveryScope ctx, Variable variable, int width)
    {
        if (!ctx.State.Lowering.inlined.Contains(variable) && ctx.State.Structs.fragmentLocals.TryGetValue(variable, out var cached))
            return ctx.ResizeFragment(cached, width).Map<Fragment?>(value => (Fragment)value);
        if (ctx.State.Structs.fragmentActive.Count == 0)
            ctx.State.Structs.fragmentSteps = 0;
        if (ctx.State.Structs.fragmentActive.Count >= 64 || ++ctx.State.Structs.fragmentSteps > 1024)
            return (Fragment?)null;
        if (!ctx.values.TryGetValue(variable, out var expression) || expression is not (Load { Width: > 8 } or Use or Ir.Convert or Ir.Select or Insert or Binary { Op: BinOp.LShr, Right: Const }) || !ctx.State.Structs.fragmentActive.Add(variable))
            return (Fragment?)null;
        var recovered = RecoverFragment();
        ctx.State.Structs.fragmentActive.Remove(variable);
        // 可选探测未获得片时，普通局部变量路径仍会检查类型和位宽。
        return recovered.TryGet(out var result, out _) ? result : (Fragment?)null;
        RecoveryResult<Fragment?> RecoverFragment()
        {
            if (!ctx.Recover(expression, null).TryGet(out var value, out var failure))
                return failure;
            if (value is not Fragment fragment)
                return (Fragment?)null;
            if (ctx.State.Lowering.inlined.Contains(variable))
                return ctx.ResizeFragment(fragment, width).Map<Fragment?>(v => (Fragment)v);
            var locals = new Fragment(fragment.Parts.Select(p => new Part(p.Low, ctx.StructLocal(p.Value.Type, p.Value.Width))).ToArray(), fragment.Type, fragment.Width);
            ctx.State.Structs.fragmentLocals.Add(variable, locals);
            return ctx.ResizeFragment(locals, width).Map<Fragment?>(v => (Fragment)v);
        }
    }

    internal static RecoveryResult<ManagedValue> ResizeFragment(this RecoveryScope ctx, Fragment fragment, int width)
    {
        if (width == fragment.Width)
            return fragment;
        var parts = new List<Part>();
        foreach (var part in fragment.Parts.Where(p => p.Low < width))
        {
            if (part.Low + part.Value.Width <= width)
            {
                parts.Add(part);
                continue;
            }

            if (!ctx.Slice(part.Value, 0, width - part.Low).TryGet(out var value, out var failure))
                return failure;
            parts.Add(new(part.Low, value));
        }

        // 零扩展的高位来自指令语义，不是结构体填充；逐字节保留已知的零。
        for (var low = fragment.Width; low < width; low += 8)
            parts.Add(new Part(low, new ConstantValue(0, ctx.types.Byte, 8)));
        return new Fragment(parts, fragment.Type, width);
    }

    internal static RecoveryResult<ManagedValue> InsertedFragment(this RecoveryScope ctx, Insert insert)
    {
        var pieces = new List<(int Low, Expr Value)>();
        Expr current = insert;
        while (current is Insert part)
        {
            pieces.Add((part.Low, part.Value));
            current = part.Base;
        }

        // 完整覆盖的逐道运算直接拆成叶子，避免恢复中间插入时生成 48/96 位的临时切片。
        var cursor = 0;
        var ordered = pieces.OrderBy(p => p.Low).ToArray();
        var complete = true;
        foreach (var piece in ordered)
        {
            complete &= piece.Low == cursor && piece.Value.Width is 8 or 16 or 32 or 64;
            cursor += piece.Value.Width;
        }

        if (current is Const { Value: 0 } && insert.Width is 32 or 64 or 128 && complete && cursor == insert.Width)
        {
            var leaves = new List<Part>();
            foreach (var piece in ordered)
            {
                if (!ctx.Recover(piece.Value, null).TryGet(out var value, out var failure))
                    return failure;
                if (value is Fragment fragment)
                    leaves.AddRange(fragment.Parts.Select(p => new Part(piece.Low + p.Low, p.Value)));
                else
                    leaves.Add(new(piece.Low, value));
            }

            return new Fragment(leaves, ctx.types.UInt64, insert.Width);
        }

        if (ctx.Recover(insert.Base, null).TryGet(out var original, out _) && ctx.Recover(insert.Value, null).TryGet(out var inserted, out _) && (original is Fragment || inserted is Fragment))
        {
            var parts = new List<Part>();
            void Append(ManagedValue value, int at)
            {
                if (value is Fragment fragment)
                    parts.AddRange(fragment.Parts.Select(p => new Part(at + p.Low, p.Value)));
                else
                    parts.Add(new Part(at, value));
            }

            if (insert.Low > 0)
            {
                if (!ctx.Slice(original, 0, insert.Low).TryGet(out var low, out var failure))
                    return failure;
                Append(low, 0);
            }

            Append(inserted, insert.Low);
            var end = insert.Low + insert.Value.Width;
            if (end < insert.Width)
            {
                if (!ctx.Slice(original, end, insert.Width - end).TryGet(out var high, out var failure))
                    return failure;
                Append(high, end);
            }

            return new Fragment(parts, ctx.types.UInt64, insert.Width);
        }

        if ((current is not Const { Value: 0 } || pieces.Any(p => p.Value.Width is not (32 or 64))) && Fold.ScalarInsert(insert) is { } scalar)
            return ctx.Recover(scalar, null);
        if (current is not Const { Value: 0 } || insert.Width is not (32 or 64 or 128))
            return RecoveryDiagnostics.Fail(0, "向量 插入基值或位宽尚未支持", rule: "InsertedFragment");
        return RecoveryDiagnostics.Fail(0, "向量 插入未完整覆盖独立叶子", rule: "InsertedFragment");
    }

    internal static RecoveryResult<ManagedValue> Slice(this RecoveryScope ctx, ManagedValue value, int low, int width)
    {
        if (low == 0 && width == value.Width && value is not Fragment)
            return value;
        if (value is AggregatePiece part && low % 8 == 0 && width % 8 == 0 && low + width <= part.Width)
            return part with
            {
                Offset = part.Offset + low / 8,
                Width = width
            };
        if (value is Fragment fragment)
        {
            var exact = fragment.Parts.Where(p => p.Low == low && p.Value.Width == width).ToArray();
            if (exact.Length == 1)
                return exact[0].Value;
            var containing = fragment.Parts.Where(p => p.Low <= low && p.Low + p.Value.Width >= low + width).ToArray();
            if (containing.Length == 1)
                return ctx.Slice(containing[0].Value, low - containing[0].Low, width);
            var parts = fragment.Parts.Where(p => p.Low >= low && p.Low + p.Value.Width <= low + width).Select(p => new Part(p.Low - low, p.Value)).ToArray();
            return new Fragment(parts, fragment.Type, width);
        }

        if (width is not (8 or 16 or 32 or 64) || value.Width > 64 || low + width > value.Width)
            return RecoveryDiagnostics.Fail(0, $"结构体 位段 [{low},{low + width}) 无法由已证明的叶子重建", rule: "Slice");
        var resultType = ctx.types.Integer(width, false);
        if (value is ConstantValue constant)
            return new ConstantValue((constant.Bits >> low) & Expr.Mask(width), resultType, width);
        if (value is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } conversion)
        {
            if (low + width <= conversion.Operand.Width)
                return ctx.Slice(conversion.Operand, low, width);
            if (conversion.Kind == ConvKind.ZeroExtend && low >= conversion.Operand.Width)
                return new ConstantValue(0, resultType, width);
        }

        if (value is BinaryValue binary)
        {
            // 按位操作可逐段投影；加法只有低段至少一侧全零（不可能产生进位）时才可拆开。
            if (binary.Op is BinOp.And or BinOp.Or or BinOp.Xor || binary.Op == BinOp.Add && (low == 0 || FragmentsRules.ZeroLow(binary.Left, low) || FragmentsRules.ZeroLow(binary.Right, low)))
            {
                if (!ctx.Slice(binary.Left, low, width).TryGet(out var left, out var failure))
                    return failure;
                if (!ctx.Slice(binary.Right, low, width).TryGet(out var right, out failure))
                    return failure;
                if (left is ConstantValue { Bits: 0 })
                {
                    if (binary.Op == BinOp.And)
                        return left;
                    if (binary.Op is BinOp.Or or BinOp.Xor or BinOp.Add)
                        return right;
                }

                if (right is ConstantValue { Bits: 0 })
                {
                    if (binary.Op == BinOp.And)
                        return right;
                    if (binary.Op is BinOp.Or or BinOp.Xor or BinOp.Add)
                        return left;
                }

                if (binary.Op == BinOp.And && right is ConstantValue mask && mask.Bits == Expr.Mask(width))
                    return left;
                return new BinaryValue(binary.Op, left, right, resultType, width);
            }

            if (binary.Right is ConstantValue shift)
            {
                var count = (int)(shift.Bits & (ulong)(binary.Width - 1));
                if (binary.Op == BinOp.Shl && low >= count)
                    return ctx.Slice(binary.Left, low - count, width);
                if (binary.Op == BinOp.Shl && low + width <= count)
                    return new ConstantValue(0, resultType, width);
                if (binary.Op == BinOp.LShr && low + count + width <= binary.Width)
                    return ctx.Slice(binary.Left, low + count, width);
            }
        }

        if (!ctx.Coerce(value, ctx.types.Integer(value.Width, false), 0).TryGet(out var raw, out var convertFailure))
            return convertFailure;
        if (low != 0)
            raw = new BinaryValue(BinOp.LShr, raw, new ConstantValue((ulong)low, ctx.types.Int32, 32), raw.Type, raw.Width);
        return ctx.Coerce(raw, ctx.types.Integer(width, false), 0);
    }

    internal static bool ZeroLow(ManagedValue value, int bits) => value switch
    {
        ConstantValue c => (c.Bits & Expr.Mask(bits)) == 0,
        BinaryValue { Op: BinOp.And } b => FragmentsRules.ZeroLow(b.Left, bits) || FragmentsRules.ZeroLow(b.Right, bits),
        BinaryValue { Op: BinOp.Or or BinOp.Xor } b => FragmentsRules.ZeroLow(b.Left, bits) && FragmentsRules.ZeroLow(b.Right, bits),
        BinaryValue { Op: BinOp.Shl, Right: ConstantValue c } b => (int)(c.Bits & (ulong)(b.Width - 1)) >= bits,
        ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } c => FragmentsRules.ZeroLow(c.Operand, Math.Min(bits, c.Operand.Width)),
        _ => false,
    };
    internal static RecoveryResult<ManagedValue> Pack(this RecoveryScope ctx, Fragment fragment)
    {
        if (fragment.Parts is [var single] && single.Low == 0 && single.Value.Width == fragment.Width)
            return single.Value;
        if (fragment.Width is not (8 or 16 or 32 or 64))
            return RecoveryDiagnostics.Fail(0, $"结构体 {fragment.Width} 位片必须逐叶子使用", rule: "Pack");
        var cursor = 0;
        ManagedValue result = new ConstantValue(0, ctx.types.Integer(fragment.Width, false), fragment.Width);
        foreach (var part in fragment.Parts.OrderBy(p => p.Low))
        {
            if (part.Low != cursor)
                return RecoveryDiagnostics.Fail(0, "结构体 不能把填充重建成整数", rule: "Pack");
            cursor += part.Value.Width;
            if (!ctx.Coerce(part.Value, ctx.types.Integer(part.Value.Width, false), 0).TryGet(out var raw, out var failure))
                return failure;
            if (!ctx.Coerce(raw, result.Type, 0).TryGet(out raw, out failure))
                return failure;
            if (part.Low != 0)
                raw = new BinaryValue(BinOp.Shl, raw, new ConstantValue((ulong)part.Low, ctx.types.Int32, 32), raw.Type, raw.Width);
            result = new BinaryValue(BinOp.Or, result, raw, result.Type, result.Width);
        }

        if (cursor != fragment.Width)
            return RecoveryDiagnostics.Fail(0, "结构体 不能把填充重建成整数", rule: "Pack");
        return result;
    }

    [DefineRule(10)]
    internal static RecoveryResult<bool> DefineFragment(this LoweringScope ctx, Define define, List<ManagedStatement> output)
    {
        if (define.Value is not (Load { Width: > 8 } or Use or Ir.Convert or Ir.Select or Insert or Binary { Op: BinOp.LShr, Right: Const }))
            return false;
        if (!ctx.Values.Recover(define.Value, null).TryGet(out var value, out var failure))
            return failure;
        if (value is not Fragment source)
            return false;
        if (!ctx.Values.FragmentVariable(define.Target, source.Width).TryGet(out var target, out failure))
            return failure;
        if (target is null)
            return RecoveryDiagnostics.Fail(define.Address, "结构体 片局部变量未建立", rule: "DefineFragment");
        if (!source.Parts.Select(p => (p.Low, p.Value.Width)).SequenceEqual(target.Parts.Select(p => (p.Low, p.Value.Width))))
            return RecoveryDiagnostics.Fail(define.Address, "结构体 片快照与来源的叶子范围不一致", rule: "DefineFragment");
        for (var i = 0; i < source.Parts.Count; i++)
        {
            // 合流分析可能细化来源类型；已建立的等宽整数快照仍须按位保存浮点叶子。
            var local = (LocalValue)target.Parts[i].Value;
            if (!ctx.Values.Coerce(source.Parts[i].Value, local.Type, define.Address).TryGet(out var leaf, out failure))
                return failure;
            output.Add(new ManagedAssignment(define.Address, local, leaf));
        }

        return true;
    }

    [StoreTargetRule(10)]
    internal static RecoveryResult<bool> StoreFragment(this LoweringScope ctx, Store store, ManagedValue target, List<ManagedStatement> output)
    {
        if (target is not Fragment fragment)
            return false;
        // 宽零写入覆盖的每个完整叶子均为该类型的零；无需把 128 位常量压成标量。
        if (ctx.Values.FrameZero(store.Value))
        {
            foreach (var part in fragment.Parts)
                output.Add(new ManagedStore(store.Address, part.Value, new ConstantValue(0, part.Value.Type, part.Value.Width)));
            return true;
        }

        if (!ctx.Values.Recover(store.Value, null).TryGet(out var source, out var failure))
            return failure;
        foreach (var part in fragment.Parts)
        {
            if (!ctx.Values.Slice(source, part.Low, part.Value.Width).Bind(value => ctx.Values.Coerce(value, part.Value.Type, store.Address)).TryGet(out var value, out failure))
                return failure;
            output.Add(new ManagedStore(store.Address, part.Value, value));
        }

        return true;
    }
}
