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
        // 取址须能写入该位置，不接受只读的访问器证明。
        if (oracle.AddressArm(sym, expected) is { } addressed) return new AddressValue(LocationValue(addressed, address, store: true));
        if (expected is DefinitionRef structure && types.Kind(expected) == TypeKind.Struct && sym is not ConcatSym && oracle.BitRepresentation(sym))
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
            // MethodInfo 指针在 IL 中只有作为方法句柄实参时才是值（表达式树的 ldtoken）。
            case EntitySym { Symbol: { Kind: SymbolKind.Method, Value: MethodRef handle } } when types.RuntimeMethodHandle.Equals(expected):
                return new MethodHandleValue(handle, types.RuntimeMethodHandle, 64);
            case EntitySym { Symbol: { Kind: SymbolKind.Type, Value: TypeRef token } }:
                return new TypeHandleValue(token, types.RuntimeTypeHandle, 64);
            case EntitySym { Symbol: { Kind: SymbolKind.Field, Value: FieldRef field } }:
                return new FieldHandleValue(field, types.RuntimeFieldHandle, 64);
            // 相邻字段合并的读取作为一个整数使用（寄存器搬运之后才取其中的片）。
            case ReadSym { Width: <= 64 } merged when oracle.Locate(merged.Address, merged.Width) is null && oracle.FieldPieces(merged, 0, merged.Width) is not null:
                {
                    var bits = expected is not null && types.Kind(expected) is TypeKind.Int or TypeKind.Pointer && Width(expected) >= merged.Width ? expected
                        : types.Integer(merged.Width <= 32 ? 32 : 64, false);
                    return Coerce(IntegerBits(merged, bits, address) ?? Hole(address, $"值 跨字段的读取 {merged}", bits), expected, address);
                }
            case ReadSym read:
                return Read(read, address) is { } value ? Coerce(value, expected, address) : Hole(address, "内存 读取", expected);
            case ResultSym result when constructions.ContainsKey(result):
                return Hole(address, "构造 对象在构造函数调用前被使用", expected);
            case PhiSym phi:
                {
                    if (oracle.ProjectedField(phi) is var (whole, wholeType, path, fieldType))
                        return Coerce(Nest(View(whole, wholeType, address), path, fieldType, false, address), expected, address);
                    if (oracle.ProjectedScalar(phi) is var (scalar, scalarType, low))
                        return Coerce(IntegerSlice(View(scalar, scalarType, address), low, phi.Width,
                            oracle.Unconstrained(phi.Width) ?? types.Integer(phi.Width <= 32 ? 32 : 64, false), address), expected, address);
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
        if (Repeatable(value) && value.Type is DefinitionRef source && expected is DefinitionRef target
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

    /// <summary>重复求值不改变结果也没有副作用的值：局部、参数以及它们的字段或解引用。</summary>
    private static bool Repeatable(ManagedValue value) => value switch
    {
        ArgumentValue or LocalValue => true,
        FieldValue { Accessor: null } field => Repeatable(field.Receiver),
        IndirectValue indirect => Repeatable(indirect.Address),
        AddressValue address => Repeatable(address.Target),
        _ => false,
    };

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
        if (oracle.ModularArithmetic(op) is { } carrier)
            return IntegerBits(op, carrier, address) ?? Hole(address, $"值 模整数运算 {op.Op}", expected);
        var typing = oracle.OperationTypes(op, expected);
        switch (op.Op.Kind)
        {
            case OperatorKind.Compare when op.Op.Cond is Cond.Eq or Cond.Ne && oracle.ClassIdentity(op.Args[0], op.Args[1]) is var (owner, sealedType):
                {
                    // 对象的类指针与密封类比较：等价于对象是否为该类型（读取类指针蕴含对象非空）。
                    var instance = new IsInstValue(View(owner, types.Object, address), sealedType);
                    return new ComparisonValue(op.Op.Cond == Cond.Eq ? Cond.Ne : Cond.Eq, instance, new ConstantValue(0, types.Object, 64), types.Boolean);
                }
            case OperatorKind.Compare:
                {
                    // 整段位的比较使用结构体所包住的标量或引用。
                    var hint = typing.Inputs[0];
                    return new ComparisonValue(op.Op.Cond, View(op.Args[0], hint, address), View(op.Args[1], hint, address), types.Boolean);
                }
            case OperatorKind.And or OperatorKind.Or:
                return new BooleanValue(op.Op.Kind == OperatorKind.And, View(op.Args[0], types.Boolean, address), View(op.Args[1], types.Boolean, address), types.Boolean);
            case OperatorKind.Not:
                return new NegatedValue(View(op.Args[0], types.Boolean, address), types.Boolean);
            case OperatorKind.Select when oracle.PinnedArray(op) is var (array, arrayType):
                return new PinnedArrayValue(View(array, arrayType, address), arrayType);
            case OperatorKind.Select:
                {
                    // 各路都没有定义类型（常量之间的选择）时按期望类型解释，常量取其位型。
                    var type = typing.Result!;
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
                    var type = typing.Result;
                    if (type is null) return Hole(address, $"类型 运算 {op.Op}", expected);
                    // 指针加减常量：偏移按字节，写成指针偏移。
                    if (type is PointerRef && op.Op.Binary is BinOp.Add or BinOp.Sub && SymTable.Resolve(op.Args[1]) is ConstSym step)
                        return new PointerOffsetValue(View(op.Args[0], type, address), new ConstantValue(op.Op.Binary == BinOp.Add ? step.Value : unchecked(0 - step.Value), types.Int64, 64));
                    return new BinaryValue(op.Op.Binary, View(op.Args[0], type, address), View(op.Args[1], typing.Inputs[1], address), type, op.Width);
                }
            case OperatorKind.Unary:
                {
                    var type = typing.Result;
                    if (type is null) return Hole(address, $"类型 运算 {op.Op}", expected);
                    return new UnaryValue(op.Op.Unary, View(op.Args[0], type, address), type, op.Width);
                }
            case OperatorKind.Convert:
                {
                    var type = typing.Result;
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
                    var source = typing.Inputs[0];
                    return new ConversionValue(op.Op.Conversion, View(op.Args[0], source, address), type, op.Width);
                }
        }
        return Hole(address, $"运算 {op.Op} 尚未接入", expected);
    }

    /// <summary>原子的一段：值类型的字段；整数的低位截断；bool 的低位即自身。</summary>
    private ManagedValue Slice(SliceSym slice, TypeRef? expected, ulong address)
    {
        if (oracle.UntypedWidePhiPiece(slice) is { } widePiece) return View(widePiece, expected, address);
        if (oracle.EnclosingScalar(slice) is { } scalar)
        {
            var target = expected is not null && types.Kind(expected) is TypeKind.Int or TypeKind.Bool or TypeKind.Pointer ? expected
                : types.Integer(oracle.StorageBits(scalar.Type), false);
            return Coerce(IntegerBits(slice, target, address)!, expected, address);
        }
        if (slice.Base is ReadSym merged && oracle.Part(merged, slice.Low, slice.Width) is { } part)
        {
            return Coerce(LocationValue(part, address), expected);
        }
        var baseType = oracle.TypeOf(slice.Base) ?? (slice.Base is PhiSym ? oracle.Unconstrained(slice.Base.Width) : null);
        if (slice.Low % 8 == 0 && baseType is not null && types.Kind(baseType) == TypeKind.Struct
            && oracle.FieldAt(baseType, slice.Low / 8 + RuntimeLayout.ObjectHeaderSize, slice.Width, false, false) is var (path, type))
            return Coerce(Nest(View(slice.Base, baseType, address), path, type, false, address), expected);
        // 跨多个字段的位片（相邻字段合并的读取、按整数使用的结构体）按字段移位与或；模运算的片在载体整数上取。
        if (slice.Width <= 64 && (oracle.FieldPieces(slice) is not null || slice.Base is OpSym modular && oracle.ModularArithmetic(modular) is not null))
        {
            var bits = expected is not null && types.Kind(expected) is TypeKind.Int or TypeKind.Pointer && Width(expected) >= slice.Width ? expected
                : types.Integer(slice.Width <= 32 ? 32 : 64, false);
            return Coerce(IntegerBits(slice, bits, address) ?? Hole(address, $"值 跨字段的片 {slice}", bits), expected, address);
        }
        if (baseType is null) return Hole(address, $"类型 切片的来源 {slice.Base}", expected);
        var source = View(slice.Base, baseType, address);
        switch (types.Kind(baseType))
        {
            case TypeKind.Struct:
                return Hole(address, $"值 结构体 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected);
            case TypeKind.Bool when slice.Low == 0:
                return Coerce(source, expected, address);
            case TypeKind.Int or TypeKind.Pointer or TypeKind.Float or TypeKind.Double:
                {
                    var carrier = oracle.IntegerRepresentation(slice.Base)!.Value.Integer;
                    var target = expected is not null && types.Kind(expected) is TypeKind.Int or TypeKind.Bool && Width(expected) >= slice.Width ? expected
                        : slice.Width is 8 or 16 or 32 or 64 ? types.Integer(slice.Width, false) : carrier;
                    if (target.Equals(types.Boolean) || slice.Width == 1 && types.Kind(target) == TypeKind.Bool)
                        return new ComparisonValue(Cond.Ne, IntegerBits(slice, carrier, address) ?? Hole(address, "值 位", carrier), new ConstantValue(0, carrier, Width(carrier)), types.Boolean);
                    return Coerce(IntegerBits(slice, target, address) ?? Hole(address, $"值 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected), expected, address);
                }
        }
        return Hole(address, $"值 {baseType} 的片 [{slice.Low}:{slice.Width}]", expected);
    }

    /// <summary>拼接按期望类型解释：结构体按字段组成；整数为零扩展；bool 的零扩展即自身。</summary>
    private ManagedValue Composite(ConcatSym concat, TypeRef? expected, ulong address)
    {
        // 整体读取的类型与期望的结构体不同（布局相同的另一个值类型）时，按字段组成。
        if (oracle.CompositeRead(concat) is { } whole
            && !(expected is not null && types.Kind(expected) == TypeKind.Struct && oracle.TypeOf(whole) is { } read && !read.Equals(expected) && oracle.Inside(read, expected) is null && oracle.Inside(expected, read) is null))
            return View(whole, expected, address);
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
        if (oracle.Aggregate(bits, structure) is not { } plan) return Hole(address, $"值 {structure} 超出位宽 {bits.Width}", structure);
        if (plan.Whole is { } whole) return View(whole, structure, address);
        return StructPhi(structure, plan) ?? Composed(structure, plan.Fields.Select(f => (f.Projection.Path, View(f.Value, f.Projection.Type, address))).ToList(), address);
    }

    /// <summary>叶子都是同一块的 φ 时还原出的结构体 φ。Leaves 是各叶子在 φ 中的位段。</summary>
    private sealed record StructPhiPlan(LocalValue Local, DefinitionRef Structure, Block Block, IReadOnlyList<(ValueProjection Projection, PhiSym Phi, int Low)> Leaves);

    private readonly Dictionary<string, StructPhiPlan> structPhis = [];

    /// <summary>
    /// clang 把结构体局部拆成叶子的 φ（SROA），之后按叶子组成时会碰到私有字段。叶子都是同一块的 φ 时还原成一个结构体 φ：
    /// 每条入边上按这条边的叶子组成（默认值、整体复制或构造函数），不需要访问字段。只在有不可访问的叶子时这样做，其余情况逐字段写法同样成立。
    /// </summary>
    private LocalValue? StructPhi(DefinitionRef structure, AggregatePlan plan)
    {
        if (plan.Fields.Count == 0 || !plan.Fields.Any(f => f.Projection.Path.Any(p => !fields.Accessible(p, p.DeclaringType)))) return null;
        var leaves = new List<(ValueProjection, PhiSym, int)>();
        foreach (var field in plan.Fields)
            switch (SymTable.Resolve(field.Value))
            {
                case PhiSym phi: leaves.Add((field.Projection, phi, 0)); break;
                case SliceSym { Base: var root, Low: var low } when SymTable.Resolve(root) is PhiSym phi: leaves.Add((field.Projection, phi, low)); break;
                default: return null;
            }
        var block = leaves[0].Item2.Block;
        if (leaves.Any(l => l.Item2.Block != block)) return null;
        var key = $"{structure}|{string.Join(",", leaves.Select(l => $"{l.Item2.Id}:{l.Item3}:{l.Item1.Bit}"))}";
        if (!structPhis.TryGetValue(key, out var known)) structPhis[key] = known = new(NewLocal(structure), structure, block, leaves);
        return known.Local;
    }

    /// <summary>结构体 φ 在第 index 条入边上的值：叶子取该边的来源，为零或未定义的叶子由默认值给出。</summary>
    private ManagedValue StructPhiSource(StructPhiPlan plan, int index, ulong address)
    {
        // 各叶子是同一个值在布局对应位置上的位段：入边上就是这个值的整体复制，不逐个求叶子（求叶子要读私有字段）。
        Sym? whole = null;
        foreach (var (projection, phi, low) in plan.Leaves)
        {
            var part = phi.Sources[index] is { } piece ? SymTable.Resolve(values.Syms.Slice(piece, low, projection.Width)) : null;
            var (root, bit) = part switch
            {
                SliceSym slice => (SymTable.Resolve(slice.Base), slice.Low),
                { } entire when projection.Bit == 0 => (entire, 0),
                _ => (null, -1),
            };
            if (root is null || bit != projection.Bit || root.Width != types.Size(plan.Structure) * 8 || whole is not null && !ReferenceEquals(whole, root)) { whole = null; break; }
            whole = root;
        }
        if (whole is not null) return View(whole, plan.Structure, address);
        var fields = new List<ProjectedSym>();
        foreach (var (projection, phi, low) in plan.Leaves)
        {
            if (phi.Sources[index] is not { } source) continue;
            var part = values.Syms.Slice(source, low, projection.Width);
            if (SymTable.Resolve(part) is not (ConstSym { Value: 0 } or UndefSym)) fields.Add(new(projection, part));
        }
        // 来源还是一层 φ 时接着还原，不在这里展开成字段。
        return StructPhi(plan.Structure, new AggregatePlan(null, fields))
            ?? Composed(plan.Structure, fields.Select(f => (f.Projection.Path, View(f.Value, f.Projection.Type, address))).ToList(), address);
    }

    /// <summary>
    /// 对位置的整体写入是否按字段分解：值由位片组成，非零叶子中有不可访问的字段，而该类型没有可能证明这个值的构造函数时
    /// （<see cref="Composed"/> 不能成立），整体写入等于对每个字段的写入（结构体的全部字节都被覆盖，填充不可观察），
    /// 每个字段按字段访问，可经访问器或内联证明。判定只看位片与类型，不求叶子的值，没有副作用。
    /// </summary>
    private bool Leafwise(Sym bits, TypeRef type)
    {
        if (type is not DefinitionRef structure || oracle.FieldStores(bits, type) is not { } leaves) return false;
        var hidden = leaves.Any(l => l.Path.Any(f => !fields.Accessible(f, f.DeclaringType)));
        return hidden && !templates.CanConstructValue(structure);
    }

    /// <summary>
    /// 按叶子组成结构体值；不可访问的字段由模板层证明构造。证明失败时，不可访问的字段都和调用方在同一程序集，
    /// 按原生代码逐个写入（源码由主程序集声明的放宽承接）；否则记为洞。
    /// </summary>
    private ManagedValue Composed(DefinitionRef structure, List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves, ulong address)
    {
        if (TryCompose(structure, leaves, address) is { } composed) return composed;
        var hidden = leaves.SelectMany(l => l.Path).Where(f => !fields.Accessible(f, f.DeclaringType)).ToArray();
        var reason = $"内存 字段 {hidden[0].Field.Owner.FullName}.{hidden[0].Field.Name} 对调用方不可访问，结构体值按叶子组成";
        if (hidden.All(f => f.Field.Owner.Assembly == analysis.Method.Method.Owner.Assembly)
            && !Inlining.TemplateRecovery.SharedArgument(analysis.Method, [structure, .. leaves.SelectMany(l => l.Path).Select(f => f.DeclaringType)]))
        {
            unfolded.Add(new Cpp2CS.Diagnostics.RuleTrace(Inlining.TemplateRecovery.UnfoldedRule, address, Cpp2CS.Diagnostics.RewriteStatus.Applied, "same-assembly-leaves", reason, null));
            return new ComposedValue(structure, leaves) { Unfolded = true };
        }
        return Hole(address, reason, structure);
    }

    /// <summary>
    /// 结构体值的托管写法：字段都可访问时逐字段组成；否则依次尝试构造函数证明、同一结构体的复制，
    /// 再把内层结构体的叶子收拢成直接字段的值后重试，最后是对象初始化器。不能写出时为 null，不记洞。
    /// </summary>
    private ManagedValue? TryCompose(DefinitionRef structure, List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves, ulong address)
    {
        if (!leaves.Any(l => l.Path.Any(f => !fields.Accessible(f, f.DeclaringType)))) return new ComposedValue(structure, leaves);
        // 显式布局中重叠的同一段位按可访问的字段组成，不可访问的字段不必再写。
        if (leaves.Where(l => l.Path[^1] is var field && !fields.Accessible(field, field.DeclaringType) && ExplicitLayout(field, out var owner)
            && types.Fields(owner).First(f => f.Path[0].Equals(field)) is var self
            && types.Fields(owner).Where(f => !f.Path[0].Equals(field) && self.Contains(f.Bit, f.Width) && fields.Accessible(f.Path[0], f.Path[0].DeclaringType)).Sum(f => f.Width) == self.Width).ToArray() is { Length: > 0 } covered)
            return TryCompose(structure, leaves.Except(covered).ToList(), address);
        // 叶子全部取自同一个结构体时就是整体复制，先于构造函数证明：后者的实参仍要逐个读私有字段。
        if (StructUpdate(structure, leaves, address, copyOnly: true) is { } copied) return copied;
        if (templates.ProveValueConstruction(structure, leaves) is { } construction)
        {
            var arguments = construction.Arguments.Select((value, i) => value is AddressValue ? value
                : Coerce(value, construction.Constructor.Concrete(construction.Constructor.Method.Parameters[i].Type), address)).ToArray();
            return new NewObjectValue(construction.Constructor, arguments) { Transparent = true };
        }
        if (StructUpdate(structure, leaves, address) is { } updated) return updated;
        if (leaves.All(l => l.Path.Count == 1)) return StructInitializer(structure, leaves, address);
        var direct = new List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)>();
        foreach (var group in leaves.GroupBy(l => l.Path[0]))
        {
            if (group.Count() == 1 && group.First().Path.Count == 1) { direct.Add(group.First()); continue; }
            if (FieldType(group.Key, null) is not DefinitionRef nested || TryCompose(nested,
                group.Select(l => ((IReadOnlyList<FieldRef>)l.Path.Skip(1).ToArray(), l.Value)).ToList(), address) is not { } whole) return null;
            direct.Add(([group.Key], whole));
        }
        return TryCompose(structure, direct, address);
    }

    /// <summary>
    /// 对象初始化器 new S { A = a, B = b } 的逆：initobj 之后逐个写字段，不可访问的字段经证明过的 setter。
    /// setter 内联后只留下字段写入，因此逐个写入与按叶子组成等价；要在值之前写出语句，需要有当前语句序列。
    /// </summary>
    private ManagedValue? StructInitializer(DefinitionRef structure, List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves, ulong address)
    {
        if (!CanEmitBefore(leaves.Select(l => l.Value))) return null;
        var receiver = new ByRefRef(structure);
        var writes = leaves.Select(l => (Field: l.Path[0], Type: FieldType(l.Path[0], null), l.Value)).ToArray();
        if (writes.Any(w => (w.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            || !fields.Accessible(w.Field, w.Field.DeclaringType) && templates.Accessor(w.Field, w.Type, true, receiver) is null)) return null;
        var copy = NewLocal(structure);
        currentOutput!.Add(new ManagedAssignment(address, copy, new ComposedValue(structure, [])));
        foreach (var (field, type, value) in writes)
            currentOutput.Add(new ManagedStore(address, FieldAccess(new AddressValue(copy), field, type, true, address), Coerce(value, type, address)));
        return copy;
    }

    /// <summary>
    /// 叶子取自同一个结构体时，不必逐个访问私有字段：全部相同就是整体复制；只有个别字段不同时，先整体复制再写这些字段（写入照常接受访问器证明）。
    /// </summary>
    private ManagedValue? StructUpdate(DefinitionRef structure, List<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves, ulong address, bool copyOnly = false)
    {
        ManagedValue? source = null;
        var changed = new List<(FieldRef Field, ManagedValue Value)>();
        foreach (var (path, value) in leaves)
        {
            var root = value;
            for (var i = path.Count - 1; i >= 0 && root is not null; i--)
                root = root is FieldValue field && field.Field.Equals(path[i]) ? field.Receiver : null;
            // 来源是同一个结构体位置（局部、形参、静态或实例字段、元素）：在这里整体读取和在这里逐个读叶子读到的是同一组值。
            if (root is LocalValue or ArgumentValue or StaticFieldValue or FieldValue or ArrayElementValue && root.Type.Equals(structure) && (source is null || source.Equals(root))) source = root;
            else if (path is [var direct]) changed.Add((direct, value));
            else return null;
        }
        if (source is null) return null;
        // 没有列出的叶子为零（或未定义，按默认值写出），来源上的这些叶子不一定如此：整个直接字段都没列出时，复制后把它写成零；
        // 只缺一部分叶子时不是一次复制加字段写入。
        foreach (var missing in types.Projections(structure).Where(p => !leaves.Any(l => p.Path.Take(l.Path.Count).SequenceEqual(l.Path))).GroupBy(p => p.Path[0]))
        {
            var field = missing.Key;
            var type = FieldType(field, null);
            if (leaves.Any(l => l.Path[0].Equals(field))) return null;
            changed.Add((field, types.Kind(type) == TypeKind.Struct ? new ComposedValue(type, []) : new ConstantValue(0, type, Width(type))));
        }
        if (changed.Count == 0) return source;
        if (copyOnly || !CanEmitBefore(changed.Select(c => c.Value))) return null;
        var copy = NewLocal(structure);
        currentOutput!.Add(new ManagedAssignment(address, copy, source));
        foreach (var (field, value) in changed)
            currentOutput.Add(new ManagedStore(address, FieldAccess(new AddressValue(copy), field, value.Type, true, address), value));
        return copy;
    }

    /// <summary>
    /// 能否在求值这个值之前写出语句。入边上的值在前驱末尾写出；前驱还有其他出边时，语句在那些路径上也会执行，
    /// 写入的是新的局部，只要被写的值求值时没有效果就不可观察。
    /// </summary>
    private bool CanEmitBefore(IEnumerable<ManagedValue> values) =>
        currentOutput is not null && (!sharedEdge || values.All(NoEffect));

    private bool NoEffect(ManagedValue value) => value switch
    {
        LocalValue or ArgumentValue or ConstantValue or StringValue => true,
        FieldValue { Receiver: var receiver } when types.Kind(receiver.Type) == TypeKind.Struct => NoEffect(receiver),
        ComposedValue composed => composed.Leaves.All(l => NoEffect(l.Value)),
        NewObjectValue { Transparent: true } created => created.Arguments.All(NoEffect),
        _ => false,
    };

    private bool sharedEdge;
    private List<ManagedStatement>? currentOutput;

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
                    if (IntegerBits(operation.Args[0], carrier, address) is not { } left) return null;
                    ManagedValue computed;
                    if (operation.Op.Kind == OperatorKind.Unary) computed = new UnaryValue(operation.Op.Unary, left, carrier, Width(carrier));
                    else if (IntegerBits(operation.Args[1], carrier, address) is { } right) computed = new BinaryValue(operation.Op.Binary, left, right, carrier, Width(carrier));
                    else return null;
                    var masked = new BinaryValue(BinOp.And, computed, new ConstantValue(Expr.Mask(operation.Width), carrier, Width(carrier)), carrier, Width(carrier));
                    return Resize(masked, target);
                }
            case ConcatSym concat:
                return Composite(concat, target, address);
            case ConstSym c:
                return new ConstantValue(c.Value & Expr.Mask(targetWidth), target, targetWidth);
            case PhiSym phi when oracle.ProjectedScalar(phi) is var (scalar, scalarType, low):
                return IntegerSlice(View(scalar, scalarType, address), low, phi.Width, target, address);
            case SliceSym slice when oracle.UntypedWidePhiPiece(slice) is { } widePiece:
                return IntegerBits(widePiece, target, address);
            case SliceSym slice when oracle.EnclosingScalar(slice) is var (scalar, scalarType, low):
                return IntegerSlice(View(scalar, scalarType, address), low, slice.Width, target, address);
            case SliceSym slice when oracle.FieldPieces(slice) is { } pieces:
                return PackedFields(pieces, target, address);
            case ReadSym merged when oracle.Locate(merged.Address, merged.Width) is null && oracle.FieldPieces(merged, 0, merged.Width) is { } parts:
                return PackedFields(parts, target, address);
            case SliceSym { Base: OpSym modular } slice when oracle.ModularArithmetic(modular) is { } wider:
                return IntegerBits(modular, wider, address) is { } whole ? IntegerSlice(whole, slice.Low, slice.Width, target, address) : null;
            case SliceSym slice when oracle.IntegerRepresentation(slice.Base) is var (sourceType, integerType):
                return IntegerSlice(Coerce(View(slice.Base, sourceType, address), integerType, address), slice.Low, slice.Width, target, address);
            case not ConcatSym when oracle.IntegerRepresentation(part) is var (atomType, integerType):
                return Resize(Coerce(View(part, atomType, address), integerType, address), target);
            case not (SliceSym or ConcatSym) when oracle.TypeOf(part) is DefinitionRef structure && types.Kind(structure) == TypeKind.Struct && part.Width <= targetWidth:
                {
                    // 只有全部位都由整数叶子覆盖时，结构体的机器位型才能用字段移位与或表示；不猜测填充字节。
                    if (types.StorageBits(structure) != part.Width || types.IntegerPieces(structure) is not { } leaves) return null;
                    var source = View(part, structure, address);
                    ManagedValue? packed = null;
                    foreach (var leaf in leaves)
                    {
                        var value = Resize(Nest(source, leaf.Path, leaf.Type, false, address), target);
                        if (leaf.Bit > 0) value = new BinaryValue(BinOp.Shl, value, new ConstantValue((ulong)leaf.Bit, types.Int32, 32), target, targetWidth);
                        packed = packed is null ? value : new BinaryValue(BinOp.Or, packed, value, target, targetWidth);
                    }
                    return packed;
                }
        }
        return null;
    }

    /// <summary>按字段分段的位作为整数类型 target 的值：各段移位后按位或。</summary>
    private ManagedValue? PackedFields(IReadOnlyList<(int Bit, Sym Piece)> pieces, TypeRef target, ulong address)
    {
        var targetWidth = Width(target);
        ManagedValue? packed = null;
        foreach (var (bit, piece) in pieces)
        {
            if (bit >= targetWidth) break;
            if (IntegerBits(piece, target, address) is not { } value) return null;
            if (bit > 0) value = new BinaryValue(BinOp.Shl, value, new ConstantValue((ulong)bit, types.Int32, 32), target, targetWidth);
            packed = packed is null ? value : new BinaryValue(BinOp.Or, packed, value, target, targetWidth);
        }
        return packed;
    }

    private ManagedValue IntegerSlice(ManagedValue source, int low, int width, TypeRef target, ulong address)
    {
        var sourceWidth = Width(source.Type);
        var integer = types.Kind(source.Type) is TypeKind.Float or TypeKind.Double ? types.Integer(sourceWidth, false) : source.Type;
        var value = Coerce(source, integer, address);
        if (low > 0) value = new BinaryValue(BinOp.LShr, value, new ConstantValue((ulong)low, types.Int32, 32), integer, sourceWidth);
        if (width < sourceWidth && low + width < sourceWidth)
            value = new BinaryValue(BinOp.And, value, new ConstantValue(Expr.Mask(width), integer, sourceWidth), integer, sourceWidth);
        return Resize(value, target);
    }

    /// <summary>整数值按宽度零扩展或截断到 target。</summary>
    private ManagedValue Resize(ManagedValue value, TypeRef target)
    {
        var (from, to) = (Width(value.Type), Width(target));
        if (from == to) return value.Type.Equals(target) ? value : Coerce(value, target);
        return new ConversionValue(from < to ? ConvKind.ZeroExtend : ConvKind.Truncate, value, target, to);
    }

}
