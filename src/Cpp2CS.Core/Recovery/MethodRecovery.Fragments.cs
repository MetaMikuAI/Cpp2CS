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
            var children = value is Fragment fragment ? fragment.Parts.Select(p => p.Value) : ManagedValues.Children(value);
            return children.SelectMany(WalkRecoveryValue).Prepend(value);
        }

        private LocalValue StructLocal(TypeRef type, int width) => new(new Variable(Storage.Temp(nextStructLocal--), 1), type, width);

        private Fragment? MemoryFragment(Expr root, TypeRef type, long offset, int width)
        {
            if (type is not (ByRefRef or DefinitionRef)) return null;
            var leaves = StructPaths(type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)).ToArray();
            if (leaves.Any(p => p.Offset < offset + width / 8 && offset < p.Offset + types.Size(p.Type)
                && (p.Offset < offset || p.Offset + types.Size(p.Type) > offset + width / 8))) return null;
            var paths = leaves.Where(p => p.Offset >= offset && p.Offset + types.Size(p.Type) <= offset + width / 8)
                .OrderBy(p => p.Offset).ToArray();
            // 叶子之间可以有填充（如 ValueTuple<bool, int> 的 3 字节）：片只按叶子使用，打包成整数时才因填充报洞。
            var cursor = offset;
            var gaps = false;
            foreach (var p in paths)
            {
                if (p.Offset < cursor) return null;
                gaps |= p.Offset != cursor;
                cursor = p.Offset + types.Size(p.Type);
            }
            gaps |= cursor != offset + width / 8;
            if (paths.Length == 0 || paths.Length < 2 && !gaps || cursor > offset + width / 8) return null;
            var value = Recover(root, null);
            return new Fragment(paths.Select(p => new Part((p.Offset - (int)offset) * 8, PathValue(value, p.Path))).ToArray(), types.UInt64, width);
        }

        /// <summary>加载的多叶子片在原定义处逐叶子快照；后续字段写入不能改变已经读出的片。</summary>
        private Fragment? FragmentVariable(Variable variable, int width)
        {
            // 内联的变量没有定义语句，不能用片局部变量（内联分析之前的恢复可能已经缓存了它们）。
            if (!inlined.Contains(variable) && fragmentLocals.TryGetValue(variable, out var cached)) return (Fragment)ResizeFragment(cached, width);
            // 片识别是可选探测；长标量转换链保留为 SSA 局部值，避免探测递归耗尽宿主栈。
            // 未证实的结构体仍由 LocalOf 的类型/位宽检查留洞，不补默认值。
            if (fragmentActive.Count == 0) fragmentSteps = 0;
            if (fragmentActive.Count >= 64 || ++fragmentSteps > 1024) return null;
            if (!values.TryGetValue(variable, out var expression) || expression is not (Load { Width: > 32 } or Use or Ir.Convert or Insert) || !fragmentActive.Add(variable)) return null;
            try
            {
                if (Recover(expression, null) is not Fragment fragment) return null;
                if (inlined.Contains(variable)) return (Fragment)ResizeFragment(fragment, width);
                var locals = new Fragment(fragment.Parts.Select(p => new Part(p.Low, StructLocal(p.Value.Type, p.Value.Width))).ToArray(), fragment.Type, fragment.Width);
                fragmentLocals.Add(variable, locals);
                return (Fragment)ResizeFragment(locals, width);
            }
            catch (HoleException) { return null; }
            finally { fragmentActive.Remove(variable); }
        }

        private ManagedValue ResizeFragment(Fragment fragment, int width)
        {
            if (width == fragment.Width) return fragment;
            var parts = fragment.Parts.Where(p => p.Low < width).Select(p => p.Low + p.Value.Width <= width ? p
                : new Part(p.Low, Slice(p.Value, 0, width - p.Low))).ToList();
            // 零扩展的高位来自指令语义，不是结构体填充；逐字节保留已知的零。
            for (var low = fragment.Width; low < width; low += 8)
                parts.Add(new Part(low, new ConstantValue(0, types.Byte, 8)));
            return new Fragment(parts, fragment.Type, width);
        }

        /// <summary>覆盖整个向量的逐道计算保留为独立叶子，按原定义顺序快照。</summary>
        private Fragment InsertedFragment(Insert insert)
        {
            var pieces = new List<(int Low, Expr Value)>();
            Expr current = insert;
            while (current is Insert part)
            {
                pieces.Add((part.Low, part.Value));
                current = part.Base;
            }
            if (current is not Const { Value: 0 } || insert.Width != 128) throw Fail(0, "向量 插入基值或位宽尚未支持");
            var cursor = 0;
            var leaves = new List<Part>();
            foreach (var piece in pieces.OrderBy(p => p.Low))
            {
                if (piece.Low != cursor || piece.Value.Width is not (32 or 64)) throw Fail(0, "向量 插入未完整覆盖独立叶子");
                cursor += piece.Value.Width;
                leaves.Add(new(piece.Low, Recover(piece.Value, null)));
            }
            if (cursor != insert.Width) throw Fail(0, "向量 插入未覆盖整个向量");
            return new Fragment(leaves, types.UInt64, insert.Width);
        }

        private ManagedValue Slice(ManagedValue value, int low, int width)
        {
            if (low == 0 && width == value.Width && value is not Fragment) return value;
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
                throw Fail(0, $"结构体 位段 [{low},{low + width}) 无法由已证明的叶子重建");
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
                    var left = Slice(binary.Left, low, width);
                    var right = Slice(binary.Right, low, width);
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
            var raw = Coerce(value, types.Integer(value.Width, false), 0);
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

        private ManagedValue Pack(Fragment fragment)
        {
            if (fragment.Parts is [var single] && single.Low == 0 && single.Value.Width == fragment.Width) return single.Value;
            if (fragment.Width is not (8 or 16 or 32 or 64)) throw Fail(0, $"结构体 {fragment.Width} 位片必须逐叶子使用");
            var cursor = 0;
            ManagedValue result = new ConstantValue(0, types.Integer(fragment.Width, false), fragment.Width);
            foreach (var part in fragment.Parts.OrderBy(p => p.Low))
            {
                if (part.Low != cursor) throw Fail(0, "结构体 不能把填充重建成整数");
                cursor += part.Value.Width;
                var raw = Coerce(part.Value, types.Integer(part.Value.Width, false), 0);
                raw = Coerce(raw, result.Type, 0);
                if (part.Low != 0) raw = new BinaryValue(BinOp.Shl, raw, new ConstantValue((ulong)part.Low, types.Int32, 32), raw.Type, raw.Width);
                result = new BinaryValue(BinOp.Or, result, raw, result.Type, result.Width);
            }
            if (cursor != fragment.Width) throw Fail(0, "结构体 不能把填充重建成整数");
            return result;
        }

        [DefineRule(10)]
        private bool DefineFragment(Define define, List<ManagedStatement> output)
        {
            if (define.Value is not (Load { Width: > 32 } or Use or Ir.Convert or Insert) || Recover(define.Value, null) is not Fragment source) return false;
            var target = FragmentVariable(define.Target, source.Width)!;
            for (var i = 0; i < source.Parts.Count; i++)
                output.Add(new ManagedAssignment(define.Address, (LocalValue)target.Parts[i].Value, source.Parts[i].Value));
            return true;
        }

        [StoreTargetRule(10)]
        private bool StoreFragment(Store store, ManagedValue target, List<ManagedStatement> output)
        {
            if (target is not Fragment fragment) return false;
            var source = Recover(store.Value, null);
            foreach (var part in fragment.Parts)
                output.Add(new ManagedStore(store.Address, part.Value, Coerce(Slice(source, part.Low, part.Value.Width), part.Value.Type, store.Address)));
            return true;
        }
    }
}
