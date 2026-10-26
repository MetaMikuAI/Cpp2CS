using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    /// <summary>
    /// L3 内存模型：一个地址表达式指向哪里，只在这里回答。
    /// 地址先展开运行时引用、分解为"基址 + 常量偏移 + 变址项"（<c>Split</c>），再按基址的根分类：
    /// - 静态字段：<c>StaticFields</c> 符号 + 偏移，类型来自元数据；
    /// - 帧区域：<c>TypedFrame</c> 或解析到 F3 帧区域的 <c>FrameAddress</c>（<c>FrameAccess</c>），单元由区域类型的布局决定；
    /// - 数组：基址类型为一维数组时，长度、元素（变址或常量下标）；
    /// - 托管指针 / 对象：基址类型（入口参数、类型引擎的解）为引用或 ByRef 时，结构体叶子、打包片、实例字段；
    /// - 对象的类指针（偏移 0）与其余形态：洞。
    /// 不逃逸的标量栈槽已在 L2 提升为 SSA 变量（<see cref="Ssa.FrameSlotPromotion"/>），不再经过这里。
    /// 新的根或路径规则加在这个文件里；类型推断经 HostTyping 调用同一套 Location。
    /// </summary>
    private sealed partial class Context
    {

        private (Expr? Base, long Offset, List<Expr> Terms) Split(Expr address)
        {
            var terms = new List<Expr>();
            void Add(Expr e)
            {
                if (e is Binary { Op: BinOp.Add } b) { Add(b.Left); Add(b.Right); }
                else terms.Add(Expand(e));
            }
            Add(AddressExpression(address));
            long offset = 0;
            var rest = new List<Expr>();
            foreach (var t in terms)
                if (t is Const c) offset += c.Signed;
                else rest.Add(t);
            Expr? baseTerm = rest.FirstOrDefault(t => t is Symbol { Kind: SymbolKind.StaticFields } || TypeOfAddressBase(t) is not null);
            if (baseTerm is not null) rest.Remove(baseTerm);
            return (baseTerm, offset, rest);
        }

        private TypeRef? TypeOfAddressBase(Expr e) => e switch
        {
            TypedFrame f => new ByRefRef(f.Region.Type),
            // 聚合参数的寄存器承载的是 ABI 片；引用叶子的类型由结构体贡献者写入 known。
            Use { Width: 64 } u when u.Variable.Version == 0 && !structArguments.ContainsKey(u.Variable.Storage)
                && arguments.TryGetValue(u.Variable.Storage, out var a) && a.Width == 64 => a.Type,
            Use { Width: 64 } u when known.TryGetValue(u.Variable, out var t) && (ManagedTypes.IsReferenceType(t) || t is ByRefRef) => t,
            _ => null,
        };

        private Expr? BaseOf(Expr address) => Split(address).Base;

        private bool IsStatic(Expr address) => Split(address).Base is Symbol;

        private (Expr Array, Expr Index)? ElementOf(Expr address)
        {
            var (array, offset, rest) = Split(address);
            if (array is null || TypeOfAddressBase(array) is not ArrayRef { IsVector: true } type || offset != RuntimeLayout.ArrayData) return null;
            var size = types.Size(type.Element);
            if (size <= 0) return null;
            return rest switch
            {
                [] => null,
                [Binary { Op: BinOp.Shl, Right: Const shift } scaled] when (1L << (int)shift.Value) == size => (array, scaled.Left),
                [Binary { Op: BinOp.Mul, Right: Const factor } scaled] when (long)factor.Value == size => (array, scaled.Left),
                [var index] when size == 1 => (array, index),
                _ => null,
            };
        }

        /// <summary>访存位置：字段、静态字段、数组长度、数组元素。</summary>
        private ManagedValue Location(Expr address, int width)
        {
            if (FrameAccess(address) is { } frameAccess) return FrameLocation(frameAccess.Region, frameAccess.Offset, width);
            foreach (var part in ExprMap.Walk(address))
            {
                if (part is Use use) CheckPoison(use.Variable);
                if (part is FrameAddress frame && frameHoles.TryGetValue(frame.Offset, out var cause))
                    throw Derived(cause, $"访存 使用未恢复的栈槽 {frame.Offset:x}");
            }
            var (baseTerm, offset, rest) = Split(address);
            switch (baseTerm)
            {
                case Symbol { Kind: SymbolKind.StaticFields, Value: DefinitionRef generic } when rest.Count == 0:
                    // 封闭实例经自身 MethodInfo 的 RGCTX 得到的类型保留泛型参数形式，代入实例的实参。
                    var owner = ClosedInstance ? (DefinitionRef)generic.Substitute(method.TypeArguments, method.MethodArguments) : generic;
                    if (types.StaticField(owner, (int)offset, width / 8) is { } field)
                        return new StaticFieldValue(field.Field, field.Type, width);
                    if (StaticStructLocation(owner, offset, width) is { } component) return component;
                    throw Fail(0, $"静态字段 {owner}+0x{offset:x}:{width} 未匹配");
                case null:
                    throw Fail(0, $"访存 地址 {address} 的基址类型未知");
            }
            var receiverType = TypeOfAddressBase(baseTerm)!;
            if (receiverType is ArrayRef { IsVector: true } array)
            {
                if (rest.Count == 0 && offset == RuntimeLayout.ArrayMaxLength && width is 32 or 64)
                {
                    var length = new ArrayLengthValue(Recover(baseTerm, null), types.Int32, 32);
                    return width == 32 ? length : new ConversionValue(ConvKind.ZeroExtend, length, types.UInt64, 64);
                }
                if (ElementOf(address) is var (_, index) && types.Kind(array.Element) is not (TypeKind.Struct or null) && width == Math.Max(types.Bits(array.Element), 8))
                    return new ArrayElementValue(Recover(baseTerm, null), Index(index), array.Element, width);
                if (rest.Count == 0 && offset >= RuntimeLayout.ArrayData && types.Size(array.Element) is > 0 and var size && (offset - RuntimeLayout.ArrayData) % size == 0
                    && types.Kind(array.Element) is not (TypeKind.Struct or null) && width == types.Bits(array.Element))
                    return new ArrayElementValue(Recover(baseTerm, null), new ConstantValue((ulong)((offset - RuntimeLayout.ArrayData) / size), types.Int32, 32), array.Element, width);
                throw Fail(0, $"数组 {array} 的访问 +0x{offset:x}:{width} 尚未支持");
            }
            if (rest.Count != 0) throw Fail(0, $"访存 地址 {address} 含变址");
            if (receiverType is ByRefRef reference && offset == 0 && width == types.Bits(reference.Element)
                && types.Kind(reference.Element) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference)
                return new IndirectValue(Recover(baseTerm, null), reference.Element, width);
            if (StructLocation(baseTerm, receiverType, offset, width) is { } leaf) return leaf;
            if (MemoryFragment(baseTerm, receiverType, offset, width) is { } fragment) return fragment;
            if (offset == RuntimeLayout.ObjectKlass) throw Fail(0, "访存 读取对象的类指针");
            if (types.InstanceField(receiverType, (int)offset, width / 8) is not { } instance) throw Fail(0, $"字段 {receiverType}+0x{offset:x}:{width} 未匹配");
            return new FieldValue(Recover(baseTerm, null), instance.Field, instance.Type, width);
        }

        /// <summary>静态值类型也可能按成员或多成员片访问；偏移只取匹配版本的布局，不补填充。</summary>
        private ManagedValue? StaticStructLocation(DefinitionRef owner, long offset, int width)
        {
            var slots = facts.Layouts.Of(owner)?.Statics.Where(s => types.Kind(s.Type) == TypeKind.Struct
                && s.Offset <= offset && offset + width / 8 <= s.Offset + types.Size(s.Type)).ToArray();
            if (slots is not [var slot]) return null;
            var root = new StaticFieldValue(new FieldRef(slot.Field, owner), slot.Type, 0);
            var paths = StructPaths(slot.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)
                && slot.Offset + p.Offset >= offset && slot.Offset + p.Offset + types.Size(p.Type) <= offset + width / 8)
                .OrderBy(p => p.Offset).ToArray();
            if (paths.Length == 0) return null;
            var cursor = offset;
            foreach (var p in paths)
            {
                if (slot.Offset + p.Offset < cursor) return null;
                cursor = slot.Offset + p.Offset + types.Size(p.Type);
            }
            var parts = paths.Select(p => new Part((slot.Offset + p.Offset - (int)offset) * 8, PathValue(root, p.Path))).ToArray();
            return parts is [var one] && one.Low == 0 && one.Value.Width == width ? one.Value : new Fragment(parts, types.UInt64, width);
        }

        /// <summary>数组下标：取 64 位地址运算中的下标表达式，恢复为 int。</summary>
        private ManagedValue Index(Expr index)
        {
            while (index is Convert { Kind: ConvKind.SignExtend or ConvKind.ZeroExtend, Width: 64 } c && c.Operand.Width == 32) index = c.Operand;
            var value = Recover(index, types.Int32);
            if (types.Kind(value.Type) is not (TypeKind.Int or TypeKind.Bool)) throw Fail(0, $"数组 下标类型 {value.Type}");
            return value.Width == 32 ? value : value.Width == 64 ? new ConversionValue(ConvKind.Truncate, value, types.Int32, 32) : throw Fail(0, $"数组 下标位宽 {value.Width}");
        }

        private long? FrameOffset(Expr expression, HashSet<Variable>? active = null)
        {
            active ??= [];
            switch (expression)
            {
                case FrameAddress f: return f.Offset;
                case Binary { Op: BinOp.Add, Right: Const c } b when FrameOffset(b.Left, active) is { } offset:
                    return offset + c.Signed;
                case Binary { Op: BinOp.Sub, Right: Const c } b when FrameOffset(b.Left, active) is { } offset:
                    return offset - c.Signed;
                case Use u when active.Add(u.Variable):
                    try
                    {
                        if (values.TryGetValue(u.Variable, out var value)) return FrameOffset(value, active);
                        if (phis.TryGetValue(u.Variable, out var phi))
                        {
                            var offsets = phi.Sources.Select(v => FrameOffset(new Use(v, 64), active)).Distinct().ToArray();
                            return offsets is [var same] ? same : null;
                        }
                        return null;
                    }
                    finally { active.Remove(u.Variable); }
                default: return null;
            }
        }

        private (FrameRegion Region, long Offset)? FrameAccess(Expr address)
        {
            address = Expand(address);
            if (address is TypedFrame frame) return (frame.Region, 0);
            if (address is Binary { Op: BinOp.Add, Right: Const c } b && FrameAccess(b.Left) is { } inner)
                return (inner.Region, inner.Offset + c.Signed);
            return null;
        }

        private ManagedValue FrameLocation(FrameRegion region, long offset, int width)
        {
            if (offset < 0 || offset + width / 8 > region.Size) throw Fail(0, "栈 访存跨越结构体区域");
            // 标量帧区域：整体读写这个局部变量（bool 以字节读写）。
            if (types.Kind(region.Type) != TypeKind.Struct)
                return offset == 0 && width == region.Local.Width ? region.Local : throw Fail(0, "栈 标量栈槽的访问宽度不符");
            var leaves = StructPaths(region.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)).ToArray();
            if (leaves.Any(p => p.Offset < offset + width / 8 && offset < p.Offset + types.Size(p.Type)
                && (p.Offset < offset || p.Offset + types.Size(p.Type) > offset + width / 8)))
                throw Fail(0, "栈 访存只覆盖部分叶子");
            var parts = leaves.Where(p => p.Offset >= offset && p.Offset + types.Size(p.Type) <= offset + width / 8)
                .OrderBy(p => p.Offset).Select(p => new Part((int)(p.Offset - offset) * 8, PathValue(region.Local, p.Path))).ToArray();
            var end = 0;
            foreach (var part in parts)
            {
                if (part.Low < end) throw Fail(0, "栈 栈槽类型冲突：叶子重叠");
                end = part.Low + part.Value.Width;
            }
            if (parts.Length == 0) throw Fail(0, "栈 访存只有填充");
            return parts is [var one] && one.Low == 0 && one.Value.Width == width ? one.Value : new Fragment(parts, types.UInt64, width);
        }

        /// <summary>展开已证明可内联的加法与常量地址计算；字段读取仍保持原 SSA 的求值时机。</summary>
        private Expr AddressExpression(Expr expression)
        {
            var seen = new HashSet<Variable>();
            Expr ExpandAddress(Expr e)
            {
                if (e is Use u && seen.Add(u.Variable) && values.TryGetValue(u.Variable, out var value))
                {
                    if (inlined.Contains(u.Variable) && value is Binary { Op: BinOp.Add }) return ExpandAddress(value);
                    if (value is Use forwarded && TypeOfAddressBase(forwarded) is ByRefRef) return ExpandAddress(value);
                    if (value is Binary { Op: BinOp.Add, Right: Const } addition
                        && TypeOfAddressBase(addition.Left) is { } baseType && (baseType is ByRefRef || ManagedTypes.IsReferenceType(baseType) && baseType is DefinitionRef))
                        return ExpandAddress(value);
                }
                if (e is Binary { Op: BinOp.Add } b) return b with { Left = ExpandAddress(b.Left), Right = ExpandAddress(b.Right) };
                return e;
            }
            return ExpandAddress(expression);
        }

        private ManagedValue? StructLocation(Expr root, TypeRef type, long offset, int width)
        {
            if (type is not (ByRefRef or DefinitionRef)) return null;
            var matches = StructPaths(type).Where(p => p.Offset == offset && types.Kind(p.Type) is not (TypeKind.Struct or null)
                && types.Size(p.Type) * 8 == width && (type is ByRefRef || p.Path.Length > 1)).ToArray();
            // 显式布局同址别名不能仅靠偏移选择一个托管字段。
            return matches.Length == 1 ? PathValue(Recover(root, null), matches[0].Path) : null;
        }

        private ManagedValue StructAddress(Expr expression, TypeRef expected)
        {
            var (root, offset, rest) = Split(expression);
            if (root is null || rest.Count != 0 || TypeOfAddressBase(root) is not { } rootType)
                throw Fail(0, $"调用 {expected} 的 this/ref 地址没有已证明的根");
            if (offset == 0 && rootType is ByRefRef b && b.Element.Equals(expected)) return Recover(root, null);
            var paths = StructPaths(rootType).Where(p => p.Offset == offset && p.Type.Equals(expected)).ToArray();
            if (paths.Length != 1) throw Fail(0, $"调用 {expected} 的 this/ref 子字段地址不唯一或未匹配");
            return new AddressValue(PathValue(Recover(root, null), paths[0].Path));
        }
    }
}
