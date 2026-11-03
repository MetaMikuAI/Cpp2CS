using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>符号值在期望类型下的托管视图：运算、切片、拼接与位组合。</summary>
internal sealed partial class BodyBuilder
{
    /// <summary>符号值在期望类型下的托管视图。</summary>
    private ManagedValue View(Sym sym, TypeRef? expected, ulong address)
    {
        sym = SymTable.Resolve(sym);
        if (expected is DefinitionRef structure && types.Kind(expected) == TypeKind.Struct && sym is not ConcatSym && Bits(sym))
            return StructBits(sym, structure, address);
        if (sym is not LocalSym && locals.TryGetValue(sym, out var known)) return Coerce(known, expected, address);
        switch (sym)
        {
            case ArgSym arg:
                {
                    var type = oracle.Parameter(arg.Index)!;
                    return Coerce(new ArgumentValue(arg.Index, type, Width(type)), expected, address);
                }
            case ConstSym constant:
                return Constant(constant, expected);
            case EntitySym { Symbol: { Kind: SymbolKind.String, Value: string text } }:
                return new StringValue(text, types.String);
            case EntitySym { Symbol: { Kind: SymbolKind.Type, Value: TypeRef token } }:
                return new TypeHandleValue(token, types.RuntimeTypeHandle, 64);
            case ReadSym read:
                Demand(read);
                return Read(read, address) is { } value ? Coerce(value, expected, address) : Hole(address, "内存 读取", expected);
            case ResultSym result when constructions.ContainsKey(result):
                return Hole(address, "构造 对象在构造函数调用前被使用", expected);
            case PhiSym phi:
                {
                    // 空跑时记录使用处要求的类型，作为 φ 的类型约束。
                    if (demand is not null && expected is not null) oracle.Use(phi, expected);
                    var type = oracle.TypeOf(phi) ?? expected ?? oracle.Unconstrained(phi.Width);
                    if (type is null) return Hole(address, "类型 φ 没有类型", expected);
                    phis.Add(phi);
                    return Coerce(Local(phi, type), expected, address);
                }
            case OpSym op:
                return Coerce(Operation(op, expected, address), expected, address);
            case SliceSym slice:
                return Slice(slice, expected, address);
            case ConcatSym concat:
                return Composite(concat, expected, address);
            case LocalSym local when analysis.Memory.Find(local.Space, local.Offset, 1) is { Promoted: false } cell
                && cell.Start == local.Offset && oracle.CellType(cell) is not null:
                return new AddressValue(CellLocal(local));
            case LocalSym local when analysis.Memory.Find(local.Space, local.Offset, 1) is { Promoted: false } && oracle.Locate(local, 8) is { } place:
                return new AddressValue(LocationValue(place, address));
            case UndefSym:
                return Hole(address, "值 未定义", expected);
            case UnknownSym unknown:
                return Hole(address, $"值 {unknown.Reason}", expected);
        }
        return Hole(address, $"值 {sym}", expected);
    }

    private ManagedValue Coerce(ManagedValue value, TypeRef? expected, ulong address = 0)
    {
        if (expected is null || value.Type.Equals(expected) || value is HoleValue) return value;
        // 表示链上的同一段位：进入单字段结构体的字段；最内层为整数时按整数宽度一致的期望取值；外层按字段组成。
        if (oracle.Inside(value.Type, expected) is var (contained, _))
            return Nest(value, contained, expected, false, address);
        if (oracle.Representation(value.Type) is [_, _, ..] && oracle.Innermost(value.Type) is var (path, scalar)
            && (types.Kind(scalar) is TypeKind.Int or TypeKind.Bool && types.Kind(expected) is TypeKind.Int or TypeKind.Bool && types.Size(value.Type) == types.Size(expected)
                || ManagedTypes.IsReferenceType(scalar) && ManagedTypes.IsReferenceType(expected) && types.IsAssignable(scalar, expected)))
            return Coerce(Nest(value, path, scalar, false, address), expected, address);
        if (expected is DefinitionRef wrapper && oracle.Inside(wrapper, value.Type) is var (wrapped, _))
            return Composed(wrapper, [(wrapped, value)], address);
        if (value is ArgumentValue or LocalValue && value.Type is DefinitionRef source && expected is DefinitionRef target
            && oracle.FieldCopy(source, target) is { } copy)
            return Composed(target, copy.Select(f => (f.Target,
                Coerce(Nest(value, f.Source, f.SourceType, false, address), f.TargetType, address))).ToList(), address);
        if (ManagedTypes.IsReferenceType(value.Type) && ManagedTypes.IsReferenceType(expected)) return value;
        var (from, to) = (types.Kind(value.Type), types.Kind(expected));
        if (Width(value.Type) == Width(expected) && value.Width is 32 or 64
            && (from == TypeKind.Int && to is TypeKind.Float or TypeKind.Double
                || to == TypeKind.Int && from is TypeKind.Float or TypeKind.Double))
            return new ConversionValue(ConvKind.Bitcast, value, expected, value.Width);
        if (from is TypeKind.Int or TypeKind.Bool && to is TypeKind.Int or TypeKind.Bool)
        {
            var (a, b) = (Width(value.Type), Width(expected));
            if (to == TypeKind.Bool && value.Width == 1) return value;
            // 1 位的真值（比较、逻辑运算）作为整数使用时须显式零扩展，即使布尔与目标整数的存储宽度相同。
            if (a == b && !(from == TypeKind.Bool && to == TypeKind.Int && value.Width < b)) return value;
            return new ConversionValue(a < b ? (ManagedTypes.IsSigned(value.Type) ? ConvKind.SignExtend : ConvKind.ZeroExtend) : ConvKind.Truncate, value, expected, b);
        }
        return value;
    }

    private ManagedValue Constant(ConstSym constant, TypeRef? expected)
    {
        if (expected is not null)
        {
            if ((ManagedTypes.IsReferenceType(expected) || expected is PointerRef or ByRefRef) && constant.Value == 0) return new ConstantValue(0, expected, 64);
            switch (types.Kind(expected))
            {
                case TypeKind.Bool: return new ConstantValue(constant.Value != 0 ? 1UL : 0UL, expected, 8);
                case TypeKind.Int or TypeKind.Float or TypeKind.Double or TypeKind.Pointer:
                    return new ConstantValue(constant.Value & Expr.Mask(Width(expected)), expected, Width(expected));
            }
        }
        return constant.Width switch
        {
            1 => new ConstantValue(constant.Value, types.Boolean, 8),
            8 or 16 or 32 or 64 => new ConstantValue(constant.Value, types.Integer(constant.Width, true), constant.Width),
            _ => new ConstantValue(constant.Value, types.Int64, 64),
        };
    }

    private ManagedValue Operation(OpSym op, TypeRef? expected, ulong address)
    {
        var natural = oracle.TypeOf(op);
        switch (op.Op.Kind)
        {
            case OperatorKind.Compare when op.Op.Cond is Cond.Eq or Cond.Ne && ClassIdentity(op.Args[0], op.Args[1]) is var (owner, sealedType):
                {
                    // 对象的类指针与密封类比较：等价于对象是否为该类型（读取类指针蕴含对象非空）。
                    var instance = new IsInstValue(View(owner, types.Object, address), sealedType);
                    return new ComparisonValue(op.Op.Cond == Cond.Eq ? Cond.Ne : Cond.Eq, instance, new ConstantValue(0, types.Object, 64), types.Boolean);
                }
            case OperatorKind.Compare:
                {
                    // 整段位的比较使用结构体所包住的标量或引用。
                    var hint = oracle.TypeOf(op.Args[0]) ?? oracle.TypeOf(op.Args[1]);
                    if (hint is not null && types.Kind(hint) == TypeKind.Struct && op.Args[1].Width == op.Args[0].Width
                        && types.Size(hint) * 8 == op.Args[0].Width && oracle.Innermost(hint).Type is var scalar
                        && (types.Kind(scalar) is TypeKind.Int or TypeKind.Bool || ManagedTypes.IsReferenceType(scalar)))
                        hint = scalar;
                    return new ComparisonValue(op.Op.Cond, View(op.Args[0], hint, address), View(op.Args[1], hint, address), types.Boolean);
                }
            case OperatorKind.And or OperatorKind.Or:
                return new BooleanValue(op.Op.Kind == OperatorKind.And, View(op.Args[0], types.Boolean, address), View(op.Args[1], types.Boolean, address), types.Boolean);
            case OperatorKind.Not:
                return new NegatedValue(View(op.Args[0], types.Boolean, address), types.Boolean);
            case OperatorKind.Select:
                {
                    // 各路都没有定义类型（常量之间的选择）时按期望类型解释，常量取其位型。
                    var type = oracle.Defined(op) ?? expected ?? types.Integer(op.Width is 8 or 16 or 32 or 64 ? op.Width : 64, true);
                    return new ChoiceValue(View(op.Args[0], types.Boolean, address), View(op.Args[1], type, address), View(op.Args[2], type, address), type, Width(type));
                }
            case OperatorKind.Binary:
                {
                    if (op.Width == 1 && op.Op.Binary is BinOp.And or BinOp.Or or BinOp.Xor)
                    {
                        var left = View(op.Args[0], types.Boolean, address);
                        var right = View(op.Args[1], types.Boolean, address);
                        return op.Op.Binary == BinOp.Xor ? new ComparisonValue(Cond.Ne, left, right, types.Boolean)
                            : new BooleanValue(op.Op.Binary == BinOp.And, left, right, types.Boolean);
                    }
                    var type = expected is not null && types.Kind(expected) is TypeKind.Int && Width(expected) == op.Width ? expected : natural ?? oracle.Unconstrained(op.Width);
                    if (type is null) return Hole(address, $"类型 运算 {op.Op}", expected);
                    return new BinaryValue(op.Op.Binary, View(op.Args[0], type, address), View(op.Args[1], op.Op.Binary is BinOp.Shl or BinOp.LShr or BinOp.AShr ? types.Int32 : type, address), type, op.Width);
                }
            case OperatorKind.Unary:
                {
                    var type = natural ?? (expected is not null && types.Kind(expected) is TypeKind.Int && Width(expected) == op.Width ? expected : oracle.Unconstrained(op.Width));
                    if (type is null) return Hole(address, $"类型 运算 {op.Op}", expected);
                    return new UnaryValue(op.Op.Unary, View(op.Args[0], type, address), type, op.Width);
                }
            case OperatorKind.Convert:
                {
                    var type = natural ?? (expected is not null && Width(expected) == op.Width ? expected : null);
                    if (type is null) return Hole(address, $"类型 转换 {op.Op}", expected);
                    var operandWidth = op.Args[0].Width;
                    // 非标准宽度的片不能交给 conv.i*：先把该片的符号位移到 IL 整数最高位，再算术右移。
                    if (op.Op.Conversion == ConvKind.SignExtend && operandWidth is not (8 or 16 or 32 or 64))
                    {
                        var integer = op.Width > 32 ? types.Int64 : types.Int32;
                        var bits = Width(integer);
                        var shift = new ConstantValue((ulong)(bits - operandWidth), types.Int32, 32);
                        var aligned = new BinaryValue(BinOp.Shl, View(op.Args[0], integer, address), shift, integer, bits);
                        return Coerce(new BinaryValue(BinOp.AShr, aligned, shift, integer, bits), type);
                    }
                    var source = op.Op.Conversion switch
                    {
                        ConvKind.FloatToFloat or ConvKind.FloatToSInt or ConvKind.FloatToUInt => operandWidth == 32 ? types.Single : types.Double,
                        ConvKind.SIntToFloat or ConvKind.SignExtend when operandWidth is 8 or 16 or 32 or 64 => oracle.TypeOf(op.Args[0]) is { } t && types.Kind(t) is TypeKind.Int ? t : types.Integer(operandWidth, true),
                        ConvKind.UIntToFloat when operandWidth is 8 or 16 or 32 or 64 => types.Integer(operandWidth, false),
                        _ => oracle.TypeOf(op.Args[0]),
                    };
                    return new ConversionValue(op.Op.Conversion, View(op.Args[0], source, address), type, op.Width);
                }
        }
        return Hole(address, $"运算 {op.Op} 尚未接入", expected);
    }

    private (Sym Owner, TypeRef Type)? ClassIdentity(Sym left, Sym right)
    {
        foreach (var (a, b) in new[] { (left, right), (right, left) })
            if (oracle.ClassOwner(a) is { } owner && SymTable.Resolve(b) is EntitySym { Symbol: { Kind: SymbolKind.Class, Value: DefinitionRef type } }
                && (type.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) != 0)
                return (owner, type);
        return null;
    }

    /// <summary>原子的一段：值类型的字段；整数的低位截断；bool 的低位即自身。</summary>
    private ManagedValue Slice(SliceSym slice, TypeRef? expected, ulong address)
    {
        if (slice.Base is ReadSym merged && oracle.Part(merged, slice.Low, slice.Width) is { } part)
        {
            Demand(merged);
            return Coerce(LocationValue(part, address), expected);
        }
        var baseType = oracle.TypeOf(slice.Base) ?? (slice.Base is PhiSym ? oracle.Unconstrained(slice.Base.Width) : null);
        if (baseType is null) return Hole(address, $"类型 切片的来源 {slice.Base}", expected);
        var source = View(slice.Base, baseType, address);
        switch (types.Kind(baseType))
        {
            case TypeKind.Struct:
                return oracle.FieldAt(baseType, slice.Low / 8 + RuntimeLayout.ObjectHeaderSize, slice.Width, false, false) is var (path, type) && slice.Low % 8 == 0
                    ? Coerce(Nest(source, path, type, false, address), expected) : Hole(address, $"值 结构体 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected);
            case TypeKind.Bool when slice.Low == 0:
                return Coerce(source, expected, address);
            case TypeKind.Int or TypeKind.Pointer:
                {
                    var target = expected is not null && types.Kind(expected) is TypeKind.Int or TypeKind.Bool && Width(expected) >= slice.Width ? expected
                        : slice.Width is 8 or 16 or 32 or 64 ? types.Integer(slice.Width, false) : baseType;
                    if (target.Equals(types.Boolean) || slice.Width == 1 && types.Kind(target) == TypeKind.Bool)
                        return new ComparisonValue(Cond.Ne, IntegerBits(slice, baseType, address) ?? Hole(address, "值 位", baseType), new ConstantValue(0, baseType, Width(baseType)), types.Boolean);
                    return IntegerBits(slice, target, address) ?? Hole(address, $"值 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected);
                }
        }
        return Hole(address, $"值 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected);
    }

    /// <summary>拼接按期望类型解释：结构体按字段组成；整数为零扩展；bool 的零扩展即自身。</summary>
    private ManagedValue Composite(ConcatSym concat, TypeRef? expected, ulong address)
    {
        if (oracle.CompositeRead(concat) is { } whole) return View(whole, expected, address);
        expected ??= oracle.Unconstrained(concat.Width);
        if (expected is null) return Hole(address, $"类型 拼接没有期望类型 {concat}", null);
        switch (types.Kind(expected))
        {
            case TypeKind.Struct when expected is DefinitionRef structure:
                return StructBits(concat, structure, address);
            case TypeKind.Int or TypeKind.Bool or TypeKind.Pointer:
                {
                    var parts = concat.Parts;
                    var low = parts[0];
                    // bool 的零扩展即自身（C++ bool 只用低位）。
                    if (parts.Skip(1).All(p => p is ConstSym { Value: 0 } or UndefSym) && oracle.TypeOf(low) is { } lowType && types.Kind(lowType) == TypeKind.Bool)
                        return View(low, expected, address);
                    if (Width(expected) > 64) break;
                    // 各段零扩展、移位、按位或；运算按目标位宽截断，目标范围之外及未定义的位不参与。
                    ManagedValue? result = null;
                    var at = 0;
                    foreach (var part in parts)
                    {
                        var bit = at;
                        at += part.Width;
                        if (part is ConstSym { Value: 0 } or UndefSym || bit >= Width(expected)) continue;
                        if (IntegerBits(part, expected, address) is not { } bits) return Hole(address, $"值 拼接段 {part} 作为 {expected}", expected);
                        if (bit > 0) bits = new BinaryValue(BinOp.Shl, bits, new ConstantValue((ulong)bit, types.Int32, 32), expected, Width(expected));
                        result = result is null ? bits : new BinaryValue(BinOp.Or, result, bits, expected, Width(expected));
                    }
                    return result ?? new ConstantValue(0, expected, Width(expected));
                }
        }
        return Hole(address, $"值 拼接 {concat} 作为 {expected}", expected);
    }

    /// <summary>
    /// 结构体值由一段标量位给出（常量、寄存器中按值传递或返回的结构体）：按运行时布局，每个叶子是对应位置的位段；
    /// 为零的叶子由 initobj 给出，全零即 default。
    /// </summary>
    private ManagedValue StructBits(Sym bits, DefinitionRef structure, ulong address)
    {
        if (oracle.WholeRead(bits, structure) is { } whole) return View(whole, structure, address);
        return StructLeaves(bits, structure, address) is { } leaves ? Composed(structure, leaves, address)
            : Hole(address, $"值 {structure} 超出位宽 {bits.Width}", structure);
    }

    /// <summary>没有自然结构体类型、按位片解释的值：拼接、常量与标量原子。</summary>
    private bool Bits(Sym sym) => sym is ConcatSym or ConstSym
        || oracle.TypeOf(sym) is { } natural && types.Kind(natural) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Pointer;

    /// <summary>位片组成的结构体值的非零叶子；位宽不足时为 null。为零的叶子由 initobj 给出。</summary>
    private List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>? StructLeaves(Sym bits, DefinitionRef structure, ulong address)
    {
        var leaves = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        foreach (var (field, type, offset) in oracle.Fields(structure))
        {
            var width = oracle.StorageBits(type);
            if (offset * 8 + width > bits.Width) return null;
            var part = values.Syms.Slice(bits, offset * 8, width);
            if (SymTable.Resolve(part) is ConstSym { Value: 0 }) continue;
            if (type is DefinitionRef nested && types.Kind(type) == TypeKind.Struct && Bits(SymTable.Resolve(part)))
            {
                // 已有整体值保留为字段值；其余位片仍按叶子交给构造函数证明。
                if (oracle.WholeRead(part, nested) is { } whole) leaves.Add(([field], View(whole, type, address)));
                else if (StructLeaves(part, nested, address) is { } inner)
                    leaves.AddRange(inner.Select(l => ((IReadOnlyList<FieldRef>)[field, .. l.Path], l.Value)));
                else return null;
            }
            else leaves.Add(([field], View(part, type, address)));
        }
        return leaves;
    }

    /// <summary>
    /// 对位置的整体写入是否按字段分解：值由位片组成，非零叶子中有不可访问的字段，而该类型没有可能证明这个值的构造函数时
    /// （<see cref="Composed"/> 不能成立），整体写入等于对每个字段的写入（结构体的全部字节都被覆盖，填充不可观察），
    /// 每个字段按字段访问，可经访问器或内联证明。判定只看位片与类型，不求叶子的值，没有副作用。
    /// </summary>
    private bool Leafwise(Sym bits, TypeRef type)
    {
        bits = SymTable.Resolve(bits);
        if (type is not DefinitionRef structure || types.Kind(structure) != TypeKind.Struct || !Bits(bits)
            || types.Size(structure) * 8 > bits.Width || oracle.WholeRead(bits, structure) is not null) return false;
        var hidden = types.Leaves(structure).Any(l => l.Path.Any(f => !this.fields.Accessible(f, f.DeclaringType))
            && SymTable.Resolve(values.Syms.Slice(bits, l.Offset * 8, oracle.LeafBits(l.Type))) is not ConstSym { Value: 0 });
        return hidden && !templates.CanConstructValue(structure);
    }

    /// <summary>按叶子组成结构体值；不可访问的字段由模板层证明构造，失败则记为洞。</summary>
    private ManagedValue Composed(DefinitionRef structure, List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves, ulong address)
    {
        if (leaves.Any(l => l.Path.Any(f => !fields.Accessible(f, f.DeclaringType)))
            && templates.ProveValueConstruction(structure, leaves) is { } construction)
        {
            var arguments = construction.Arguments.Select((value, i) => value is AddressValue ? value
                : Coerce(value, construction.Constructor.Concrete(construction.Constructor.Method.Parameters[i].Type), address)).ToArray();
            return new NewObjectValue(construction.Constructor, arguments) { Transparent = true };
        }
        foreach (var (path, _) in leaves)
            if (path.FirstOrDefault(f => !fields.Accessible(f, f.DeclaringType)) is { } hidden)
                return Hole(address, $"内存 字段 {hidden.Field.Owner.FullName}.{hidden.Field.Name} 对调用方不可访问，结构体值按叶子组成", structure);
        return new ComposedValue(structure, leaves);
    }

    /// <summary>
    /// 一段位作为整数类型 target 的值（零扩展）：常量；整数原子；整数原子的切片为右移与掩码。
    /// 运算在来源的类型中进行，最后按宽度转换到 target。不能表达时为 null。
    /// </summary>
    private ManagedValue? IntegerBits(Sym part, TypeRef target, ulong address)
    {
        part = SymTable.Resolve(part);
        var targetWidth = Width(target);
        switch (part)
        {
            case OpSym operation when oracle.ModularArithmetic(operation) is { } carrier:
                {
                    if (IntegerBits(operation.Args[0], carrier, address) is not { } left
                        || IntegerBits(operation.Args[1], carrier, address) is not { } right) return null;
                    var computed = new BinaryValue(operation.Op.Binary, left, right, carrier, Width(carrier));
                    var masked = new BinaryValue(BinOp.And, computed, new ConstantValue(Expr.Mask(operation.Width), carrier, Width(carrier)), carrier, Width(carrier));
                    return Resize(masked, target);
                }
            case ConcatSym concat:
                return Composite(concat, target, address);
            case ConstSym c:
                return new ConstantValue(c.Value & Expr.Mask(targetWidth), target, targetWidth);
            case SliceSym slice when (oracle.TypeOf(slice.Base) ?? (slice.Base is PhiSym ? oracle.Unconstrained(slice.Base.Width) : null)) is { } sourceType && types.Kind(sourceType) is TypeKind.Int or TypeKind.Pointer or TypeKind.Bool:
                {
                    var sourceWidth = Width(sourceType);
                    var value = View(slice.Base, sourceType, address);
                    if (slice.Low > 0) value = new BinaryValue(BinOp.LShr, value, new ConstantValue((ulong)slice.Low, types.Int32, 32), sourceType, sourceWidth);
                    if (slice.Width < sourceWidth && slice.Low + slice.Width < sourceWidth)
                        value = new BinaryValue(BinOp.And, value, new ConstantValue(Expr.Mask(slice.Width), sourceType, sourceWidth), sourceType, sourceWidth);
                    return Resize(value, target);
                }
            case not ConcatSym when (oracle.TypeOf(part) ?? (part is PhiSym ? oracle.Unconstrained(part.Width) : null)) is { } atomType && types.Kind(atomType) is TypeKind.Int or TypeKind.Bool or TypeKind.Pointer:
                return Resize(View(part, atomType, address), target);
            case not (SliceSym or ConcatSym) when oracle.TypeOf(part) is DefinitionRef structure && types.Kind(structure) == TypeKind.Struct && part.Width <= targetWidth:
                {
                    // 只有全部位都由整数叶子覆盖时，结构体的机器位型才能用字段移位与或表示；不猜测填充字节。
                    var leaves = Leaves(structure, 0).OrderBy(l => l.Offset).ToArray();
                    var covered = 0;
                    foreach (var (_, type, offset) in leaves)
                    {
                        if (types.Kind(type) is not (TypeKind.Int or TypeKind.Bool) || offset * 8 != covered) return null;
                        covered += Width(type);
                    }
                    if (covered != part.Width) return null;
                    var source = View(part, structure, address);
                    ManagedValue? packed = null;
                    foreach (var (path, type, offset) in leaves)
                    {
                        var value = Resize(Nest(source, path, type, false, address), target);
                        if (offset > 0) value = new BinaryValue(BinOp.Shl, value, new ConstantValue((ulong)(offset * 8), types.Int32, 32), target, targetWidth);
                        packed = packed is null ? value : new BinaryValue(BinOp.Or, packed, value, target, targetWidth);
                    }
                    return packed;
                }
        }
        return null;
    }

    /// <summary>整数值按宽度零扩展或截断到 target。</summary>
    private ManagedValue Resize(ManagedValue value, TypeRef target)
    {
        var (from, to) = (Width(value.Type), Width(target));
        if (from == to) return value.Type.Equals(target) ? value : Coerce(value, target);
        return new ConversionValue(from < to ? ConvKind.ZeroExtend : ConvKind.Truncate, value, target, to);
    }

    private IEnumerable<(IReadOnlyList<FieldRef> Path, TypeRef Type, int Offset)> Leaves(DefinitionRef structure, int at) => types.Leaves(structure, at);
}
