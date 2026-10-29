using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        // 只在 L3 内存活；必须在写出前拆回叶子，不能把引用叶子转成整数或让填充成为托管值。
        private sealed record Part(int Low, ManagedValue Value);
        private sealed record Fragment(IReadOnlyList<Part> Parts, TypeRef Type, int Width) : ManagedValue(Type, Width);
        private readonly Dictionary<Variable, Fragment> fragmentLocals = new();
        private readonly HashSet<Variable> fragmentActive = [];
        private int fragmentSteps;
        private int nextStructLocal = -1;

        /// <summary>恢复期间遍历结构体片的叶子；最终方法体仍须通过片残留检查。</summary>
        private static IEnumerable<ManagedValue> WalkRecoveryValue(ManagedValue value)
        {
            var children = value is Fragment fragment ? fragment.Parts.Select(p => p.Value)
                : value is AggregatePiece part ? [part.Root] : ManagedValues.Children(value);
            return children.SelectMany(WalkRecoveryValue).Prepend(value);
        }

        private LocalValue StructLocal(TypeRef type, int width) => new(new Variable(Storage.Temp(nextStructLocal--), 1), type, width);

        /// <summary>循环中的结构体片按相同叶子汇合；填充仍没有值，不能借助零初值把填充变成整数。</summary>
        [Analysis("片汇合", 98, After = ["结构体写入汇合"])]
        private void PrepareFragmentPhis()
        {
            var phis = blocks.SelectMany(b => b.Statements).OfType<Phi>().ToArray();
            var targets = phis.Select(p => p.Target).ToHashSet();
            var links = phis.SelectMany(p => p.Sources.SelectMany(s => new[] { (From: p.Target, To: s), (From: s, To: p.Target) }))
                .ToLookup(p => p.From, p => p.To);
            var seen = new HashSet<Variable>();
            foreach (var phi in phis)
            {
                if (seen.Contains(phi.Target)) continue;
                var web = new HashSet<Variable>();
                var pending = new Stack<Variable>(); pending.Push(phi.Target);
                while (pending.TryPop(out var next))
                    if (web.Add(next)) foreach (var linked in links[next]) pending.Push(linked);
                seen.UnionWith(web);
                var width = phi.Target.Width;
                if (width is not (64 or 128) || web.Any(v => v.Width != width || structPhiMembers.ContainsKey(v))) continue;
                var fragments = new List<Fragment>();
                var zeros = new List<Variable>();
                var complete = true;
                foreach (var source in web.Where(v => !targets.Contains(v)))
                {
                    if (values.GetValueOrDefault(source) is Const { Value: 0 } zero && zero.Width == width) { zeros.Add(source); continue; }
                    if (!Variable(source, width).TryGet(out var value, out _) || value is not Fragment fragment) { complete = false; break; }
                    fragments.Add(fragment);
                }
                if (!complete || fragments.Count == 0) continue;
                var shape = fragments[0].Parts.Select(p => (p.Low, p.Value.Type, p.Value.Width)).ToArray();
                if (fragments.Any(f => !f.Parts.Select(p => (p.Low, p.Value.Type, p.Value.Width)).SequenceEqual(shape))) continue;
                foreach (var target in web.Where(targets.Contains))
                    fragmentLocals[target] = new Fragment(shape.Select(p => new Part(p.Low, StructLocal(p.Type, p.Width))).ToArray(), types.UInt64, width);
                inlined.UnionWith(zeros);
            }
        }

        private RecoveryResult<Fragment?> MemoryFragment(Expr root, TypeRef type, long offset, int width)
        {
            if (type is not (ByRefRef or DefinitionRef)) return (Fragment?)null;
            var leaves = ScalarStructPaths(type).ToArray();
            if (leaves.Any(p => p.Offset < offset + width / 8 && offset < p.Offset + types.Size(p.Type)
                && (p.Offset < offset || p.Offset + types.Size(p.Type) > offset + width / 8))) return (Fragment?)null;
            var paths = leaves.Where(p => p.Offset >= offset && p.Offset + types.Size(p.Type) <= offset + width / 8)
                .OrderBy(p => p.Offset).ToArray();
            // 叶子之间可以有填充（如 ValueTuple<bool, int> 的 3 字节）：片只按叶子使用，打包成整数时才因填充报洞。
            var cursor = offset;
            var gaps = false;
            foreach (var p in paths)
            {
                if (p.Offset < cursor) return (Fragment?)null;
                gaps |= p.Offset != cursor;
                cursor = p.Offset + types.Size(p.Type);
            }
            gaps |= cursor != offset + width / 8;
            if (paths.Length == 0 || paths.Length < 2 && !gaps || cursor > offset + width / 8) return (Fragment?)null;
            if (!Recover(root, null).TryGet(out var value, out var failure)) return failure;
            return new Fragment(paths.Select(p => new Part((p.Offset - (int)offset) * 8, PathValue(value, p.Path))).ToArray(), types.UInt64, width);
        }

        /// <summary>加载的多叶子片在原定义处逐叶子快照；后续字段写入不能改变已经读出的片。</summary>
        private RecoveryResult<Fragment?> FragmentVariable(Variable variable, int width)
        {
            if (!inlined.Contains(variable) && fragmentLocals.TryGetValue(variable, out var cached))
                return ResizeFragment(cached, width).Map<Fragment?>(value => (Fragment)value);
            if (fragmentActive.Count == 0) fragmentSteps = 0;
            if (fragmentActive.Count >= 64 || ++fragmentSteps > 1024) return (Fragment?)null;
            if (!values.TryGetValue(variable, out var expression) || expression is not (Load { Width: > 32 } or Use or Ir.Convert or Insert or Binary { Op: BinOp.LShr, Right: Const })
                || !fragmentActive.Add(variable)) return (Fragment?)null;
            var recovered = RecoverFragment();
            fragmentActive.Remove(variable);
            // 可选探测未获得片时，普通局部变量路径仍会检查类型和位宽。
            return recovered.TryGet(out var result, out _) ? result : (Fragment?)null;

            RecoveryResult<Fragment?> RecoverFragment()
            {
                if (!Recover(expression, null).TryGet(out var value, out var failure)) return failure;
                if (value is not Fragment fragment) return (Fragment?)null;
                if (inlined.Contains(variable)) return ResizeFragment(fragment, width).Map<Fragment?>(v => (Fragment)v);
                var locals = new Fragment(fragment.Parts.Select(p => new Part(p.Low, StructLocal(p.Value.Type, p.Value.Width))).ToArray(), fragment.Type, fragment.Width);
                fragmentLocals.Add(variable, locals);
                return ResizeFragment(locals, width).Map<Fragment?>(v => (Fragment)v);
            }
        }

        private RecoveryResult<ManagedValue> ResizeFragment(Fragment fragment, int width)
        {
            if (width == fragment.Width) return fragment;
            var parts = new List<Part>();
            foreach (var part in fragment.Parts.Where(p => p.Low < width))
            {
                if (part.Low + part.Value.Width <= width) { parts.Add(part); continue; }
                if (!Slice(part.Value, 0, width - part.Low).TryGet(out var value, out var failure)) return failure;
                parts.Add(new(part.Low, value));
            }
            // 零扩展的高位来自指令语义，不是结构体填充；逐字节保留已知的零。
            for (var low = fragment.Width; low < width; low += 8)
                parts.Add(new Part(low, new ConstantValue(0, types.Byte, 8)));
            return new Fragment(parts, fragment.Type, width);
        }

        /// <summary>覆盖整个向量的逐道计算保留为独立叶子，按原定义顺序快照。</summary>
        private RecoveryResult<ManagedValue> InsertedFragment(Insert insert)
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
            if (current is Const { Value: 0 } && insert.Width is 32 or 64 or 128
                && complete && cursor == insert.Width)
            {
                var leaves = new List<Part>();
                foreach (var piece in ordered)
                {
                    if (!Recover(piece.Value, null).TryGet(out var value, out var failure)) return failure;
                    if (value is Fragment fragment) leaves.AddRange(fragment.Parts.Select(p => new Part(piece.Low + p.Low, p.Value)));
                    else leaves.Add(new(piece.Low, value));
                }
                return new Fragment(leaves, types.UInt64, insert.Width);
            }
            if (Recover(insert.Base, null).TryGet(out var original, out _) && Recover(insert.Value, null).TryGet(out var inserted, out _)
                && (original is Fragment || inserted is Fragment))
            {
                var parts = new List<Part>();
                void Append(ManagedValue value, int at)
                {
                    if (value is Fragment fragment) parts.AddRange(fragment.Parts.Select(p => new Part(at + p.Low, p.Value)));
                    else parts.Add(new Part(at, value));
                }
                if (insert.Low > 0)
                {
                    if (!Slice(original, 0, insert.Low).TryGet(out var low, out var failure)) return failure;
                    Append(low, 0);
                }
                Append(inserted, insert.Low);
                var end = insert.Low + insert.Value.Width;
                if (end < insert.Width)
                {
                    if (!Slice(original, end, insert.Width - end).TryGet(out var high, out var failure)) return failure;
                    Append(high, end);
                }
                return new Fragment(parts, types.UInt64, insert.Width);
            }
            if ((current is not Const { Value: 0 } || pieces.Any(p => p.Value.Width is not (32 or 64)))
                && Fold.ScalarInsert(insert) is { } scalar) return Recover(scalar, null);
            if (current is not Const { Value: 0 } || insert.Width is not (32 or 64 or 128)) return Fail(0, "向量 插入基值或位宽尚未支持");
            return Fail(0, "向量 插入未完整覆盖独立叶子");
        }

        private RecoveryResult<ManagedValue> Slice(ManagedValue value, int low, int width)
        {
            if (low == 0 && width == value.Width && value is not Fragment) return value;
            if (value is AggregatePiece part && low % 8 == 0 && width % 8 == 0 && low + width <= part.Width)
                return part with { Offset = part.Offset + low / 8, Width = width };
            if (value is Fragment fragment)
            {
                var exact = fragment.Parts.Where(p => p.Low == low && p.Value.Width == width).ToArray();
                if (exact.Length == 1) return exact[0].Value;
                var containing = fragment.Parts.Where(p => p.Low <= low && p.Low + p.Value.Width >= low + width).ToArray();
                if (containing.Length == 1) return Slice(containing[0].Value, low - containing[0].Low, width);
                var parts = fragment.Parts.Where(p => p.Low >= low && p.Low + p.Value.Width <= low + width)
                    .Select(p => new Part(p.Low - low, p.Value)).ToArray();
                return new Fragment(parts, fragment.Type, width);
            }
            if (width is not (8 or 16 or 32 or 64) || value.Width > 64 || low + width > value.Width)
                return Fail(0, $"结构体 位段 [{low},{low + width}) 无法由已证明的叶子重建");
            var resultType = types.Integer(width, false);
            if (value is ConstantValue constant) return new ConstantValue((constant.Bits >> low) & Expr.Mask(width), resultType, width);
            if (value is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } conversion)
            {
                if (low + width <= conversion.Operand.Width) return Slice(conversion.Operand, low, width);
                if (conversion.Kind == ConvKind.ZeroExtend && low >= conversion.Operand.Width) return new ConstantValue(0, resultType, width);
            }
            if (value is BinaryValue binary)
            {
                // 按位操作可逐段投影；加法只有低段至少一侧全零（不可能产生进位）时才可拆开。
                if (binary.Op is BinOp.And or BinOp.Or or BinOp.Xor
                    || binary.Op == BinOp.Add && (low == 0 || ZeroLow(binary.Left, low) || ZeroLow(binary.Right, low)))
                {
                    if (!Slice(binary.Left, low, width).TryGet(out var left, out var failure)) return failure;
                    if (!Slice(binary.Right, low, width).TryGet(out var right, out failure)) return failure;
                    if (left is ConstantValue { Bits: 0 })
                    {
                        if (binary.Op == BinOp.And) return left;
                        if (binary.Op is BinOp.Or or BinOp.Xor or BinOp.Add) return right;
                    }
                    if (right is ConstantValue { Bits: 0 })
                    {
                        if (binary.Op == BinOp.And) return right;
                        if (binary.Op is BinOp.Or or BinOp.Xor or BinOp.Add) return left;
                    }
                    if (binary.Op == BinOp.And && right is ConstantValue mask && mask.Bits == Expr.Mask(width)) return left;
                    return new BinaryValue(binary.Op, left, right, resultType, width);
                }
                if (binary.Right is ConstantValue shift)
                {
                    var count = (int)(shift.Bits & (ulong)(binary.Width - 1));
                    if (binary.Op == BinOp.Shl && low >= count) return Slice(binary.Left, low - count, width);
                    if (binary.Op == BinOp.Shl && low + width <= count) return new ConstantValue(0, resultType, width);
                    if (binary.Op == BinOp.LShr && low + count + width <= binary.Width) return Slice(binary.Left, low + count, width);
                }
            }
            if (!Coerce(value, types.Integer(value.Width, false), 0).TryGet(out var raw, out var convertFailure)) return convertFailure;
            if (low != 0) raw = new BinaryValue(BinOp.LShr, raw, new ConstantValue((ulong)low, types.Int32, 32), raw.Type, raw.Width);
            return Coerce(raw, types.Integer(width, false), 0);
        }

        private static bool ZeroLow(ManagedValue value, int bits) => value switch
        {
            ConstantValue c => (c.Bits & Expr.Mask(bits)) == 0,
            BinaryValue { Op: BinOp.And } b => ZeroLow(b.Left, bits) || ZeroLow(b.Right, bits),
            BinaryValue { Op: BinOp.Or or BinOp.Xor } b => ZeroLow(b.Left, bits) && ZeroLow(b.Right, bits),
            BinaryValue { Op: BinOp.Shl, Right: ConstantValue c } b => (int)(c.Bits & (ulong)(b.Width - 1)) >= bits,
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } c => ZeroLow(c.Operand, Math.Min(bits, c.Operand.Width)),
            _ => false,
        };

        private RecoveryResult<ManagedValue> Pack(Fragment fragment)
        {
            if (fragment.Parts is [var single] && single.Low == 0 && single.Value.Width == fragment.Width) return single.Value;
            if (fragment.Width is not (8 or 16 or 32 or 64)) return Fail(0, $"结构体 {fragment.Width} 位片必须逐叶子使用");
            var cursor = 0;
            ManagedValue result = new ConstantValue(0, types.Integer(fragment.Width, false), fragment.Width);
            foreach (var part in fragment.Parts.OrderBy(p => p.Low))
            {
                if (part.Low != cursor) return Fail(0, "结构体 不能把填充重建成整数");
                cursor += part.Value.Width;
                if (!Coerce(part.Value, types.Integer(part.Value.Width, false), 0).TryGet(out var raw, out var failure)) return failure;
                if (!Coerce(raw, result.Type, 0).TryGet(out raw, out failure)) return failure;
                if (part.Low != 0) raw = new BinaryValue(BinOp.Shl, raw, new ConstantValue((ulong)part.Low, types.Int32, 32), raw.Type, raw.Width);
                result = new BinaryValue(BinOp.Or, result, raw, result.Type, result.Width);
            }
            if (cursor != fragment.Width) return Fail(0, "结构体 不能把填充重建成整数");
            return result;
        }

        [DefineRule(10)]
        private RecoveryResult<bool> DefineFragment(Define define, List<ManagedStatement> output)
        {
            if (define.Value is not (Load { Width: > 32 } or Use or Ir.Convert or Insert or Binary { Op: BinOp.LShr, Right: Const })) return false;
            if (!Recover(define.Value, null).TryGet(out var value, out var failure)) return failure;
            if (value is not Fragment source) return false;
            if (!FragmentVariable(define.Target, source.Width).TryGet(out var target, out failure)) return failure;
            if (target is null) return Fail(define.Address, "结构体 片局部变量未建立");
            for (var i = 0; i < source.Parts.Count; i++)
                output.Add(new ManagedAssignment(define.Address, (LocalValue)target.Parts[i].Value, source.Parts[i].Value));
            return true;
        }

        [StoreTargetRule(10)]
        private RecoveryResult<bool> StoreFragment(Store store, ManagedValue target, List<ManagedStatement> output)
        {
            if (target is not Fragment fragment) return false;
            if (!Recover(store.Value, null).TryGet(out var source, out var failure)) return failure;
            foreach (var part in fragment.Parts)
            {
                if (!Slice(source, part.Low, part.Value.Width).Bind(value => Coerce(value, part.Value.Type, store.Address)).TryGet(out var value, out failure)) return failure;
                output.Add(new ManagedStore(store.Address, part.Value, value));
            }
            return true;
        }
    }
}
