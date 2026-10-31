using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using Convert = Cpp2CS.Ir.Convert;

namespace Cpp2CS.Recovery;

internal static class MemoryRules
{
    internal static (Expr? Base, long Offset, List<Expr> Terms) Split(this RecoveryScope ctx, Expr address)
    {
        var form = AddressForm.Decompose(ctx.AddressExpression(address), new()
        {
            Expansion = AddressExpansion.Leaves,
            Expand = ctx.Expand,
            Root = t => t is Symbol { Kind: SymbolKind.StaticFields or SymbolKind.ThreadStaticFields } || ctx.TypeOfAddressBase(t) is not null,
        });
        return (form.Root, form.Offset, form.Terms);
    }

    internal static TypeRef? TypeOfAddressBase(this RecoveryScope ctx, Expr e) => e switch
    {
        TypedFrame f => new ByRefRef(f.Region.Type),
        Symbol { Kind: SymbolKind.String } => ctx.types.String,
        // 聚合参数的寄存器承载的是 ABI 片；引用叶子的类型由结构体贡献者写入 known。
        Use { Width: 64 } u when u.Variable.Version == 0 && !ctx.State.Signature.structArguments.ContainsKey(u.Variable.Storage) && ctx.State.Signature.arguments.TryGetValue(u.Variable.Storage, out var a) && a.Width == 64 => a.Type,
        Use { Width: 64 } u when ctx.State.Types.known.TryGetValue(u.Variable, out var t) && (ManagedTypes.IsReferenceType(t) || t is ByRefRef or PointerRef) => t,
        // 条件归约可把已加载的引用内联进字段路径；每层仍须由真实布局确认，不从用途猜加载类型。
        Load { Width: 64 } load when ctx.TypeOfValue(load) is { } t && (ManagedTypes.IsReferenceType(t) || t is ByRefRef or PointerRef) => t,
        _ => null,
    };
    internal static Expr? BaseOf(this RecoveryScope ctx, Expr address) => ctx.Split(address).Base;
    internal static bool IsStatic(this RecoveryScope ctx, Expr address) => ctx.Split(address).Base is Symbol;
    internal static (Expr Array, Expr Index)? ElementOf(this RecoveryScope ctx, Expr address) => ctx.ArrayLocation(address) is { Offset: 0 } location ? (location.Array, location.Index) : null;
    internal static (Expr Array, Expr Index, ArrayRef Type, int Offset)? ArrayLocation(this RecoveryScope ctx, Expr address)
    {
        var (array, offset, rest) = ctx.Split(address);
        if (array is null || ctx.TypeOfAddressBase(array) is not ArrayRef { IsVector: true } type || rest.Count == 0 && offset < RuntimeLayout.ArrayData)
            return null;
        var size = ctx.types.Size(type.Element);
        if (size <= 0)
            return null;
        Expr ExpandIndex(Expr expression, int depth = 0)
        {
            if (depth >= 16)
                return expression;
            return Fold.Simplify(ExprMap.Map(expression, e => e is Use use && ctx.values.TryGetValue(use.Variable, out var value) && value.Width >= use.Width && value is Ir.Binary or Convert && !ExprMap.Walk(value).Any(p => p is Load or Read or Intrinsic or Unknown) ? Fold.Convert(ConvKind.Truncate, ExpandIndex(value, depth + 1), use.Width) : null));
        }

        rest = rest.Select(e => ExpandIndex(e)).ToList();
        Expr? index = rest switch
        {
            [] => new Const(0, 64),
            [Binary { Op: BinOp.Shl, Right: Const shift } scaled] when shift.Value < 63 && (1L << (int)shift.Value) == size => scaled.Left,
            [Binary { Op: BinOp.Mul, Right: Const factor } scaled] when (long)factor.Value == size => scaled.Left,
            [var unscaled] when size == 1 => unscaled,
            _ => null,
        };
        if (index is null)
            return null;
        var displacement = offset - RuntimeLayout.ArrayData;
        var within = (displacement % size + size) % size;
        var elements = (displacement - within) / size;
        if (elements != 0)
            index = Fold.Simplify(new Binary(BinOp.Add, index, new Const(unchecked((ulong)elements), index.Width), index.Width));
        return (array, index, type, (int)within);
    }

    internal static RecoveryResult<ManagedValue> ArrayStructLocation(this RecoveryScope ctx, Expr array, Expr index, ArrayRef type, int offset, int width)
    {
        if (!ctx.Recover(array, null).TryGet(out var arrayValue, out var failure))
            return failure;
        if (!ctx.Index(index).TryGet(out var indexValue, out failure))
            return failure;
        var root = new ArrayElementValue(arrayValue, indexValue, type.Element, 0);
        if (offset + width / 8 > ctx.types.Size(type.Element))
            return RecoveryDiagnostics.Fail(0, "数组 访存跨越结构体元素", rule: "ArrayStructLocation");
        var leaves = ctx.StructPaths(type.Element).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null) && p.Offset < offset + width / 8 && offset < p.Offset + ctx.types.Size(p.Type)).OrderBy(p => p.Offset).ToArray();
        if (leaves.Length == 0 || leaves.Any(p => p.Offset < offset || p.Offset + ctx.types.Size(p.Type) > offset + width / 8) || leaves.Zip(leaves.Skip(1)).Any(p => p.First.Offset + ctx.types.Size(p.First.Type) > p.Second.Offset))
            return RecoveryDiagnostics.Fail(0, "数组 结构体元素叶子重叠或仅被部分覆盖", rule: "ArrayStructLocation");
        var parts = leaves.Select(p => new Part((p.Offset - offset) * 8, ctx.PathValue(root, p.Path))).ToArray();
        return parts is [var single] && single.Low == 0 && single.Value.Width == width ? single.Value : new Fragment(parts, ctx.types.UInt64, width);
    }

    internal static RecoveryResult<ManagedValue> Location(this RecoveryScope ctx, Expr address, int width)
    {
        RecoveryFailure failure;
        if (ctx.AddressExpression(address) is Intrinsic { Name: "managed_field_address" } shared)
        {
            if (!ctx.SharedAddress(shared).TryGet(out var sharedValue, out failure))
                return failure;
            if (sharedValue is AddressValue sharedField && sharedField.Target.Width == width)
                return sharedField.Target;
        }

        if (ctx.FrameAccess(address) is { } frameAccess)
            return ctx.FrameLocation(frameAccess.Region, frameAccess.Offset, width);
        foreach (var part in ExprMap.Walk(address))
        {
            if (part is Use use && ctx.CheckPoison(use.Variable) is { } poison)
                return poison;
            if (part is FrameAddress frame && ctx.State.Frames.frameHoles.TryGetValue(frame.Offset, out var cause))
                return RecoveryDiagnostics.Derived(cause, $"访存 使用未恢复的栈槽 {frame.Offset:x}");
        }

        var (baseTerm, offset, rest) = ctx.Split(address);
        switch (baseTerm)
        {
            case Symbol { Kind: SymbolKind.ThreadStaticFields, Value: DefinitionRef threadType } when rest.Count == 0:
                if (ctx.facts.Layouts.Of(threadType)?.ThreadStatics.FirstOrDefault(s => s.Offset == offset && ctx.types.Bits(s.Type) == width) is { } threadField)
                    return new StaticFieldValue(new FieldRef(threadField.Field, threadType), threadField.Type, width);
                return RecoveryDiagnostics.Fail(0, $"线程静态字段 {threadType}+0x{offset:x}:{width} 未匹配", rule: "Location");
            case Symbol { Kind: SymbolKind.StaticFields, Value: DefinitionRef generic } when rest.Count == 0:
                // 封闭实例经自身 MethodInfo 的 RGCTX 得到的类型保留泛型参数形式，代入实例的实参。
                var owner = ctx.ClosedInstance ? (DefinitionRef)generic.Substitute(ctx.method.TypeArguments, ctx.method.MethodArguments) : generic;
                if (ctx.types.StaticField(owner, (int)offset, width / 8) is { } field)
                    return ctx.types.Kind(field.Type) == TypeKind.Struct && ctx.StaticStructLocation(owner, offset, width) is { } value ? value : new StaticFieldValue(field.Field, field.Type, width);
                if (ctx.StaticStructLocation(owner, offset, width) is { } component)
                    return component;
                if (ctx.StaticMemoryFragment(owner, offset, width) is { } packed)
                    return packed;
                return RecoveryDiagnostics.Fail(0, $"静态字段 {owner}+0x{offset:x}:{width} 未匹配", rule: "Location");
            case null:
                return RecoveryDiagnostics.Fail(0, $"访存 地址 {address} 的基址类型未知", rule: "Location");
        }

        var receiverType = ctx.TypeOfAddressBase(baseTerm)!;
        if (receiverType is PointerRef && width is 8 or 16 or 32 or 64)
            return ctx.Recover(address, null).Map<ManagedValue>(value => new IndirectValue(value, ctx.types.Integer(width, false), width));
        if (receiverType is ArrayRef { IsVector: true } array)
        {
            if (rest.Count == 0 && offset == RuntimeLayout.ArrayMaxLength && width is 32 or 64)
            {
                if (!ctx.Recover(baseTerm, null).TryGet(out var arrayValue, out failure))
                    return failure;
                var length = new ArrayLengthValue(arrayValue, ctx.types.Int32, 32);
                return width == 32 ? length : new ConversionValue(ConvKind.ZeroExtend, length, ctx.types.UInt64, 64);
            }

            if (ctx.ElementOf(address) is var (_, index) && ctx.types.Kind(array.Element) is not (TypeKind.Struct or null) && width == Math.Max(ctx.types.Bits(array.Element), 8))
                return ctx.Recover(baseTerm, null).Bind(value => ctx.Index(index).Map<ManagedValue>(at => new ArrayElementValue(value, at, array.Element, width)));
            if (ctx.types.Kind(array.Element) == TypeKind.Struct && ctx.ArrayLocation(address) is { } element)
                return ctx.ArrayStructLocation(element.Array, element.Index, element.Type, element.Offset, width);
            if (rest.Count == 0 && offset >= RuntimeLayout.ArrayData && ctx.types.Size(array.Element) is > 0 and var size && (offset - RuntimeLayout.ArrayData) % size == 0 && ctx.types.Kind(array.Element) is not (TypeKind.Struct or null) && width == ctx.types.Bits(array.Element))
                return ctx.Recover(baseTerm, null).Map<ManagedValue>(value => new ArrayElementValue(value, new ConstantValue((ulong)((offset - RuntimeLayout.ArrayData) / size), ctx.types.Int32, 32), array.Element, width));
            return RecoveryDiagnostics.Fail(0, $"数组 {array} 的访问 +0x{offset:x}:{width} 尚未支持", rule: "Location");
        }

        if (rest.Count != 0)
            return RecoveryDiagnostics.Fail(0, $"访存 地址 {address} 含变址", rule: "Location");
        if (receiverType is ByRefRef reference && offset == 0 && width == ctx.types.Bits(reference.Element) && ctx.types.Kind(reference.Element) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference)
            return ctx.Recover(baseTerm, null).Map<ManagedValue>(value => new IndirectValue(value, reference.Element, width));
        if (!ctx.StructLocation(baseTerm, receiverType, offset, width).TryGet(out var leaf, out failure))
            return failure;
        if (leaf is not null)
            return leaf;
        if (!ctx.MemoryFragment(baseTerm, receiverType, offset, width).TryGet(out var fragment, out failure))
            return failure;
        if (fragment is not null)
            return fragment;
        if (offset == RuntimeLayout.ObjectKlass)
            return RecoveryDiagnostics.Fail(0, "访存 读取对象的类指针", rule: "Location");
        if (ctx.types.InstanceField(receiverType, (int)offset, width / 8) is not { } instance)
        {
            // 小端整数或枚举字段的低位读取，字段身份和完整宽度仍来自元数据。
            if (width is 8 or 16 or 32)
                foreach (var bytes in new[]
                {
                    2,
                    4,
                    8
                }.Where(bytes => bytes * 8 > width))
                    if (ctx.types.InstanceField(receiverType, (int)offset, bytes) is { } wide && ctx.types.Kind(wide.Type) == TypeKind.Int)
                        return ctx.Recover(baseTerm, null).Map<ManagedValue>(value => new ConversionValue(ConvKind.Truncate, new FieldValue(value, wide.Field, wide.Type, bytes * 8), ctx.types.Integer(width, false), width));
            return RecoveryDiagnostics.Fail(0, $"字段 {receiverType}+0x{offset:x}:{width} 未匹配", rule: "Location");
        }

        return ctx.Recover(baseTerm, null).Map<ManagedValue>(value => new FieldValue(value, instance.Field, instance.Type, width));
    }

    internal static Fragment? StaticMemoryFragment(this RecoveryScope ctx, DefinitionRef owner, long offset, int width)
    {
        var slots = ctx.facts.Layouts.Of(owner)?.Statics.Where(s => ctx.types.Kind(s.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Reference or TypeKind.Float or TypeKind.Double && s.Offset >= offset && s.Offset + ctx.types.Size(s.Type) <= offset + width / 8).OrderBy(s => s.Offset).ToArray();
        if (slots is null || slots.Length < 2)
            return null;
        return new Fragment(slots.Select(s => new Part((s.Offset - (int)offset) * 8, new StaticFieldValue(new FieldRef(s.Field, owner), s.Type, ctx.types.Size(s.Type) * 8))).ToArray(), ctx.types.UInt64, width);
    }

    internal static ManagedValue? StaticStructLocation(this RecoveryScope ctx, DefinitionRef owner, long offset, int width)
    {
        var slots = ctx.facts.Layouts.Of(owner)?.Statics.Where(s => ctx.types.Kind(s.Type) == TypeKind.Struct && s.Offset <= offset && offset + width / 8 <= s.Offset + ctx.types.Size(s.Type)).ToArray();
        if (slots is not [var slot])
            return null;
        var root = new StaticFieldValue(new FieldRef(slot.Field, owner), slot.Type, 0);
        var paths = ctx.StructPaths(slot.Type).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null) && slot.Offset + p.Offset >= offset && slot.Offset + p.Offset + ctx.types.Size(p.Type) <= offset + width / 8).OrderBy(p => p.Offset).ToArray();
        if (paths.Length == 0)
            return null;
        var cursor = offset;
        foreach (var p in paths)
        {
            if (slot.Offset + p.Offset < cursor)
                return null;
            cursor = slot.Offset + p.Offset + ctx.types.Size(p.Type);
        }

        var parts = paths.Select(p => new Part((slot.Offset + p.Offset - (int)offset) * 8, ctx.PathValue(root, p.Path))).ToArray();
        return parts is [var one] && one.Low == 0 && one.Value.Width == width ? one.Value : new Fragment(parts, ctx.types.UInt64, width);
    }

    internal static RecoveryResult<ManagedValue> Index(this RecoveryScope ctx, Expr index)
    {
        while (index is Convert { Kind: ConvKind.SignExtend or ConvKind.ZeroExtend, Width: 64 } c && c.Operand.Width == 32)
            index = c.Operand;
        if (!ctx.Recover(index, ctx.types.Int32).TryGet(out var value, out var failure))
            return failure;
        if (ctx.types.Kind(value.Type) is not (TypeKind.Int or TypeKind.Bool))
            return RecoveryDiagnostics.Fail(0, $"数组 下标类型 {value.Type}", rule: "Index");
        return value.Width == 32 ? value : value.Width == 64 ? new ConversionValue(ConvKind.Truncate, value, ctx.types.Int32, 32) : RecoveryDiagnostics.Fail(0, $"数组 下标位宽 {value.Width}", rule: "Index");
    }

    internal static long? FrameOffset(this RecoveryScope ctx, Expr expression, HashSet<Variable>? active = null)
    {
        active ??= [];
        switch (expression)
        {
            case FrameAddress f:
                return f.Offset;
            case Binary { Op: BinOp.Add, Right: Const c } b when ctx.FrameOffset(b.Left, active) is { } offset:
                return offset + c.Signed;
            case Binary { Op: BinOp.Sub, Right: Const c } b when ctx.FrameOffset(b.Left, active) is { } offset:
                return offset - c.Signed;
            case Use u when active.Add(u.Variable):
                try
                {
                    if (ctx.values.TryGetValue(u.Variable, out var value))
                        return ctx.FrameOffset(value, active);
                    if (ctx.phis.TryGetValue(u.Variable, out var phi))
                    {
                        var offsets = phi.Sources.Select(v => ctx.FrameOffset(new Use(v, 64), active)).Distinct().ToArray();
                        return offsets is [var same] ? same : null;
                    }

                    return null;
                }
                finally
                {
                    active.Remove(u.Variable);
                }

            default:
                return null;
        }
    }

    internal static (FrameRegion Region, long Offset)? FrameAccess(this RecoveryScope ctx, Expr address)
    {
        address = ctx.Expand(address);
        if (address is TypedFrame frame)
            return (frame.Region, 0);
        if (address is Binary { Op: BinOp.Add, Right: Const c } b && ctx.FrameAccess(b.Left) is { } inner)
            return (inner.Region, inner.Offset + c.Signed);
        if (ctx.State.Frames.discoveryFrames.Length > 0 && ctx.FrameOffset(address) is { } offset && ctx.State.Frames.discoveryFrames.Where(r => offset >= r.Offset && offset < r.Offset + r.Size).Take(2).ToArray() is [var region])
            return (region, offset - region.Offset);
        return null;
    }

    internal static RecoveryResult<ManagedValue> FrameLocation(this RecoveryScope ctx, FrameRegion region, long offset, int width)
    {
        if (offset < 0 || offset + width / 8 > region.Size)
            return RecoveryDiagnostics.Fail(0, "栈 访存跨越结构体区域", rule: "FrameLocation");
        // 标量帧区域：整体读写这个局部变量（bool 以字节读写）。
        if (ctx.types.Kind(region.Type) != TypeKind.Struct)
            return offset == 0 && width == region.Local.Width ? region.Local : RecoveryDiagnostics.Fail(0, "栈 标量栈槽的访问宽度不符", rule: "FrameLocation");
        var leaves = ctx.ScalarStructPaths(region.Type).ToArray();
        if (region.Type is DefinitionRef empty && ctx.facts.Layouts.Of(empty) is { Fields.Count: 0 })
            return region.Local with { Width = width };
        // 显式布局允许整数字段与字节字段重叠；精确字段访问不需要重建其他别名。
        if (leaves.Where(p => p.Offset == offset && ctx.types.Size(p.Type) * 8 == width).ToArray() is [var exact])
            return ctx.PathValue(region.Local, exact.Path);
        if (leaves.Any(p => p.Offset < offset + width / 8 && offset < p.Offset + ctx.types.Size(p.Type) && (p.Offset < offset || p.Offset + ctx.types.Size(p.Type) > offset + width / 8)))
            return RecoveryDiagnostics.Fail(0, "栈 访存只覆盖部分叶子", rule: "FrameLocation");
        var parts = leaves.Where(p => p.Offset >= offset && p.Offset + ctx.types.Size(p.Type) <= offset + width / 8).OrderBy(p => p.Offset).Select(p => new Part((int)(p.Offset - offset) * 8, ctx.PathValue(region.Local, p.Path))).ToArray();
        var end = 0;
        foreach (var part in parts)
        {
            if (part.Low < end)
                return RecoveryDiagnostics.Fail(0, "栈 栈槽类型冲突：叶子重叠", rule: "FrameLocation");
            end = part.Low + part.Value.Width;
        }

        if (parts.Length == 0)
            return RecoveryDiagnostics.Fail(0, "栈 访存只有填充", rule: "FrameLocation");
        return parts is [var one] && one.Low == 0 && one.Value.Width == width ? one.Value : new Fragment(parts, ctx.types.UInt64, width);
    }

    internal static Expr AddressExpression(this RecoveryScope ctx, Expr expression)
    {
        var seen = new HashSet<Variable>();
        Expr ExpandAddress(Expr e)
        {
            if (e is Use cursor && ctx.State.Arrays.arrayCursors.TryGetValue(cursor.Variable, out var address))
                return ExpandAddress(address);
            if (e is Use u && seen.Add(u.Variable) && ctx.values.TryGetValue(u.Variable, out var value))
            {
                if (value is Intrinsic { Name: "managed_field_address" or "managed_generic_buffer" or "managed_generic_argument" })
                    return value;
                if (ctx.State.Lowering.inlined.Contains(u.Variable) && value is Binary { Op: BinOp.Add })
                    return ExpandAddress(value);
                if (value is Use forwarded && ctx.TypeOfAddressBase(forwarded) is ByRefRef)
                    return ExpandAddress(value);
                if (value is Binary { Op: BinOp.Add, Right: Const } addition && ctx.TypeOfAddressBase(addition.Left) is { } baseType && (baseType is ByRefRef || ManagedTypes.IsReferenceType(baseType)))
                    return ExpandAddress(value);
            }

            if (e is Binary { Op: BinOp.Add } b)
                return b with
                {
                    Left = ExpandAddress(b.Left),
                    Right = ExpandAddress(b.Right)
                };
            return e;
        }

        return ExpandAddress(expression);
    }

    internal static RecoveryResult<ManagedValue?> StructLocation(this RecoveryScope ctx, Expr root, TypeRef type, long offset, int width)
    {
        if (type is not (ByRefRef or DefinitionRef))
            return (ManagedValue?)null;
        var matches = ctx.ScalarStructPaths(type).Where(p => p.Offset == offset && ctx.types.Size(p.Type) * 8 == width && (type is ByRefRef || p.Path.Length > 1)).ToArray();
        // 显式布局同址别名不能仅靠偏移选择一个托管字段。
        return matches.Length == 1 ? ctx.Recover(root, null).Map<ManagedValue?>(value => ctx.PathValue(value, matches[0].Path)) : (ManagedValue?)null;
    }

    internal static RecoveryResult<ManagedValue> StructAddress(this RecoveryScope ctx, Expr expression, TypeRef expected)
    {
        if (ctx.ArrayLocation(expression) is { } element && ctx.types.Kind(element.Type.Element) == TypeKind.Struct)
        {
            if (!ctx.Recover(element.Array, null).TryGet(out var array, out var failure))
                return failure;
            if (!ctx.Index(element.Index).TryGet(out var index, out failure))
                return failure;
            var value = new ArrayElementValue(array, index, element.Type.Element, 0);
            if (element.Offset == 0 && element.Type.Element.Equals(expected))
                return new AddressValue(value);
            var fields = ctx.StructPaths(element.Type.Element).Where(p => p.Offset == element.Offset && p.Type.Equals(expected)).ToArray();
            if (fields is [var nested])
                return new AddressValue(ctx.PathValue(value, nested.Path));
        }

        var (root, offset, rest) = ctx.Split(expression);
        if (root is Symbol { Kind: SymbolKind.StaticFields } && rest.Count == 0)
        {
            if (!ctx.Location(expression, ctx.types.Size(expected) * 8).TryGet(out var field, out var failure))
                return failure;
            if (field.Type.Equals(expected))
                return new AddressValue(field);
        }

        if (root is null || rest.Count != 0 || ctx.TypeOfAddressBase(root) is not { } rootType)
            return RecoveryDiagnostics.Fail(0, $"调用 {expected} 的 this/ref 地址没有已证明的根", rule: "StructAddress");
        if (offset == 0 && rootType is ByRefRef b && b.Element.Equals(expected))
            return ctx.Recover(root, null);
        var paths = ctx.StructPaths(rootType).Where(p => p.Offset == offset && p.Type.Equals(expected)).ToArray();
        if (paths.Length != 1)
            return RecoveryDiagnostics.Fail(0, $"调用 {expected} 的 this/ref 子字段地址不唯一或未匹配", rule: "StructAddress");
        return ctx.Recover(root, null).Map<ManagedValue>(value => new AddressValue(ctx.PathValue(value, paths[0].Path)));
    }
}
