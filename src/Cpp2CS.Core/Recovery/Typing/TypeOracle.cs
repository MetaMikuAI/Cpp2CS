using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Calls;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

public enum LocationKind : byte { Instance, Reference, Static, ThreadStatic, Element, Length, StringLength, StringChar, Local }

/// <summary>
/// 一次读写指向的 IL 位置。Base：实例字段的对象、经引用访问的指针、数组或字符串，可寻址局部为单元起点的局部地址；
/// Index：元素下标（为 null 时下标为常量 ConstantIndex）；
/// Owner：静态字段所属类型；Path：从根位置进入值类型的字段链；Type：被访问值的类型。
/// </summary>
public sealed record Location(LocationKind Kind, Sym? Base, Sym? Index, long ConstantIndex, TypeRef? Owner, IReadOnlyList<FieldRef> Path, TypeRef Type);

/// <summary>
/// 原子的类型与地址的位置。类型自下而上由定义给出：参数按签名，调用结果按被调用者，读取按位置，φ 取来源的汇合；
/// 常量和拼接没有自然类型，由使用处的期望类型决定。地址分解为根、常量偏移与比例下标，再按运行时布局解释为字段、元素或长度。
/// </summary>
public sealed class TypeOracle : Runtime.IRuntimeTyping
{
    private readonly ManagedTypes types;
    private readonly ProgramFacts facts;
    private readonly MethodRef method;
    private readonly Func<Call, CallShape> shapes;
    private readonly Dictionary<Sym, TypeRef?> memo = [];
    private readonly HashSet<Sym> active = [];
    private readonly Dictionary<Call, MethodRef?> callees = new(ReferenceEqualityComparer.Instance);
    private readonly ValueModel values;
    private readonly MemoryLayout memory;
    private Dictionary<Cell, TypeRef?>? cellTypes;

    public TypeOracle(ManagedTypes types, ProgramFacts facts, MethodRef method, Func<Call, CallShape> shapes, ValueModel values, MemoryLayout? memory = null)
    {
        this.types = types;
        this.facts = facts;
        this.method = method;
        this.shapes = shapes;
        this.values = values;
        this.memory = memory ?? new([]);
    }

    /// <summary>
    /// 地址逃逸的单元作为可寻址的 IL 局部时的类型：取自把单元起点作为 ref、副本实参或结果缓冲区的调用签名，
    /// 或以单元为装箱来源的类型；各处一致且大小覆盖单元时成立。
    /// </summary>
    public TypeRef? CellType(Cell cell)
    {
        if (cellTypes is null)
        {
            cellTypes = [];
            var evidence = new Dictionary<Cell, HashSet<TypeRef>>();
            void Note(Sym pointer, TypeRef? type)
            {
                if (type is null || SymTable.Resolve(pointer) is not LocalSym local || memory.Find(local.Space, local.Offset, 1) is not { Promoted: false } target
                    || target.Start != local.Offset) return;
                if (!evidence.TryGetValue(target, out var set)) evidence[target] = set = [];
                set.Add(type);
            }
            foreach (var call in values.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                var operands = values.Operands(call);
                if (call.Op is { Kind: OpKind.Box, Operand: TypeRef boxed } && operands.Count > 2) Note(operands[2], boxed);
                if (shapes(call).Signature is not { } signature || Callee(call) is not { } callee) continue;
                foreach (var value in signature.Indirections)
                {
                    var position = Array.IndexOf(call.Sources, value.Pieces[0].Register);
                    if (position < 0) continue;
                    var type = value.Index == MachineSignature.ReturnIndex ? Concrete(callee, callee.Method.ReturnType)
                        : value.Index < 0 ? callee.DeclaringType : Concrete(callee, callee.Method.Parameters[value.Index].Type);
                    Note(operands[1 + position], type is ByRefRef byRef ? byRef.Element : type);
                }
            }
            foreach (var (noted, set) in evidence)
                cellTypes[noted] = set.Count == 1 && set.First() is var t && (ManagedTypes.IsReferenceType(t) ? 8 : types.Size(t)) >= noted.Size ? t : null;
        }
        return cellTypes.GetValueOrDefault(cell);
    }

    public ManagedTypes Types => types;

    public TypeRef Substitute(TypeRef type) => type.Substitute(method.TypeArguments, method.MethodArguments);

    public TypeRef? Parameter(int index) => index < 0
        ? (method.Method.Owner.IsValueType ? new ByRefRef(method.DeclaringType) : method.DeclaringType)
        : Substitute(method.Method.Parameters[index].Type);

    public TypeRef ReturnType => Substitute(method.Method.ReturnType);

    // ---- 调用目标 ----

    /// <summary>
    /// 调用的托管目标。共享代码的地址对应多个实例：调用传入的 MethodInfo 实参指名确切的实例时取它；
    /// 实例方法的接收者类型确定声明类型的类型实参时按接收者代入；相同代码折叠的候选按接收者与实参类型选择，
    /// 无法区分时取第一个（折叠的候选机器码相同）。
    /// </summary>
    public MethodRef? Callee(Call call)
    {
        if (callees.TryGetValue(call, out var known)) return known;
        callees[call] = null;
        var shape = shapes(call);
        var candidates = shape.Candidates;
        if (candidates.Count == 0) return null;
        var operands = values.Operands(call);
        Sym? Register(Storage storage) => Array.IndexOf(call.Sources, storage) is var k and >= 0 && k + 1 < operands.Count ? operands[1 + k] : null;
        if (shape.Signature?.MethodInfo is { } info && Register(info.Register) is { } infoSym
            && SymTable.Resolve(infoSym) is EntitySym { Symbol: { Kind: SymbolKind.Method, Value: MethodRef exact } }
            && candidates.Any(c => c.Method == exact.Method))
            return callees[call] = exact;
        var receiver = shape.Signature?.This is { } self && self.Pieces[0].Register.Bank == Bank.Gpr ? Register(self.Pieces[0].Register) : null;
        var receiverType = receiver is not null && call.Op?.Kind != OpKind.CallDelegate ? TypeOf(receiver) : null;
        if (receiverType is ByRefRef byRef) receiverType = byRef.Element;
        var arguments = shape.Signature?.Arguments.Select(a => a.Transfer == Transfer.Value && a.Pieces.Length == 1 && a.Pieces[0].Register.Bank != Bank.Stack
            ? Register(a.Pieces[0].Register) : null).ToArray() ?? [];
        var chosen = candidates.Count == 1 ? candidates[0]
            : candidates.FirstOrDefault(c => Compatible(c, receiverType, arguments)) ?? candidates[0];
        if (receiverType is DefinitionRef owner && !chosen.Method.IsStatic) chosen = Specialize(chosen, owner);
        return callees[call] = chosen;
    }

    /// <summary>接收者的基类链上找到方法的声明类型时，以其类型实参代入。</summary>
    private static MethodRef Specialize(MethodRef candidate, DefinitionRef receiver)
    {
        if (candidate.Method.Owner.GenericParameters.Count == 0) return candidate;
        for (TypeRef? current = receiver; current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []))
            if (d.Definition == candidate.Method.Owner) return candidate with { TypeArguments = d.Arguments };
        return candidate;
    }

    private bool Compatible(MethodRef candidate, TypeRef? receiver, IReadOnlyList<Sym?> arguments)
    {
        var offset = candidate.Method.IsStatic ? 0 : 1;
        if (!candidate.Method.IsStatic && receiver is not null && ManagedTypes.IsReferenceType(receiver)
            && !types.IsAssignable(receiver, candidate.DeclaringType)) return false;
        for (var i = 0; i < candidate.Method.Parameters.Count && i + offset < arguments.Count; i++)
            if (arguments[i + offset] is { } argument && TypeOf(argument) is { } actual && ManagedTypes.IsReferenceType(actual)
                && candidate.Method.Parameters[i].Type.Substitute(candidate.TypeArguments, candidate.MethodArguments) is var expected
                && ManagedTypes.IsReferenceType(expected) && !types.IsAssignable(actual, expected)) return false;
        return true;
    }

    public static TypeRef Concrete(MethodRef callee, TypeRef type) => type.Substitute(callee.TypeArguments, callee.MethodArguments);

    // ---- 原子的类型 ----

    public TypeRef? TypeOf(Sym sym)
    {
        sym = SymTable.Resolve(sym);
        if (memo.TryGetValue(sym, out var known)) return known;
        if (!active.Add(sym)) return null;
        var type = Natural(sym);
        active.Remove(sym);
        if (sym is not PhiSym || type is not null) memo[sym] = type;
        return type;
    }

    private TypeRef? Natural(Sym sym)
    {
        switch (sym)
        {
            case ArgSym arg:
                return Parameter(arg.Index);
            case EntitySym { Symbol: { Kind: SymbolKind.String } }:
                return types.String;
            case ResultSym result when result.Index == 0:
                return ResultType(result.Site);
            case OutSym output when output.Site.Op is null && Callee(output.Site) is { } callee:
                return output.Argument == MachineSignature.ReturnIndex ? Concrete(callee, callee.Method.ReturnType)
                    : (output.Argument < 0 ? null : Concrete(callee, callee.Method.Parameters[output.Argument].Type)) is ByRefRef byRef ? byRef.Element : null;
            case ReadSym read when Decompose(read.Address) is (ResultSym { Site.Op.Kind: OpKind.BeginCatch }, 0, null, _):
                return types.Corlib("System.Exception");
            case ReadSym read:
                return Locate(read.Address, read.Width)?.Type;
            case PhiSym phi:
                {
                    TypeRef? joined = null;
                    foreach (var source in phi.Sources)
                    {
                        if (source is null || SymTable.Resolve(source) is var s && (ReferenceEquals(s, phi) || s is ConstSym or UndefSym)) continue;
                        var t = TypeOf(source);
                        if (t is null) continue;
                        joined = joined is null ? t : Join(joined, t);
                        if (joined is null) return null;
                    }
                    return joined;
                }
            case OpSym op:
                return OperatorType(op) ?? (op.Width is 8 or 16 or 32 or 64 && op.Op.Kind is OperatorKind.Select or OperatorKind.Binary or OperatorKind.Unary
                    ? types.Integer(op.Width, true) : null);
            case SliceSym slice when TypeOf(slice.Base) is { } baseType:
                return types.Kind(baseType) == TypeKind.Struct && FieldAt(baseType, slice.Low / 8 + RuntimeLayout.ObjectHeaderSize, slice.Width, false, false) is var (_, fieldType) ? fieldType
                    : slice.Width == 1 ? types.Boolean : slice.Width is 8 or 16 or 32 or 64 ? types.Integer(slice.Width, false) : null;
        }
        return null;
    }

    private TypeRef? ResultType(Call call)
    {
        if (call.Op is { } op && !shapes(call).IsDispatch)
            return Runtime.RuntimeOps.Of(op.Kind)?.ResultType?.Invoke(op, this);
        return Callee(call) is { } callee && Concrete(callee, callee.Method.ReturnType) is var ret && !ManagedTypes.IsVoid(ret) ? ret : null;
    }

    public DefinitionRef? ExceptionType(string fullName) =>
        (types.CorlibDefinition(fullName) ?? facts.Model.Types.FirstOrDefault(t => t.FullName == fullName && t.GenericParameters.Count == 0)) is { } definition
            ? new DefinitionRef(definition, []) : null;

    private TypeRef? OperatorType(OpSym op)
    {
        switch (op.Op.Kind)
        {
            case OperatorKind.Compare or OperatorKind.And or OperatorKind.Or or OperatorKind.Not:
                return types.Boolean;
            case OperatorKind.Select:
                return TypeOf(op.Args[1]) is { } a ? (TypeOf(op.Args[2]) is { } b ? Join(a, b) : a) : TypeOf(op.Args[2]);
            case OperatorKind.Binary when op.Op.Binary is BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv or BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber:
                return op.Width == 32 ? types.Single : types.Double;
            case OperatorKind.Unary when op.Op.Unary >= UnOp.FNeg:
                return op.Width == 32 ? types.Single : types.Double;
            case OperatorKind.Binary or OperatorKind.Unary:
                {
                    var operand = TypeOf(op.Args[0]);
                    if (operand is not null && types.Kind(operand) is TypeKind.Int && types.Bits(operand) == op.Width) return operand;
                    return op.Width is 8 or 16 or 32 or 64 ? types.Integer(op.Width, op.Op.Kind == OperatorKind.Binary && op.Op.Binary is BinOp.SDiv or BinOp.SRem or BinOp.AShr) : null;
                }
            case OperatorKind.Convert:
                return op.Op.Conversion switch
                {
                    ConvKind.SIntToFloat or ConvKind.UIntToFloat or ConvKind.FloatToFloat => op.Width == 32 ? types.Single : types.Double,
                    ConvKind.FloatToSInt or ConvKind.SignExtend when op.Width is 8 or 16 or 32 or 64 => types.Integer(op.Width, true),
                    ConvKind.FloatToUInt when op.Width is 8 or 16 or 32 or 64 => types.Integer(op.Width, false),
                    _ => null,
                };
        }
        return null;
    }

    /// <summary>两个定义类型的汇合：相同取自身；引用类型沿基类链取最近公共超类；同宽整数取前者。</summary>
    public TypeRef? Join(TypeRef a, TypeRef b)
    {
        if (a.Equals(b)) return a;
        if (types.IsAssignable(a, b)) return b;
        if (types.IsAssignable(b, a)) return a;
        if (ManagedTypes.IsReferenceType(a) && ManagedTypes.IsReferenceType(b))
        {
            for (TypeRef? current = a; current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []))
                if (types.IsAssignable(b, current)) return current;
            return types.Object;
        }
        if (types.Kind(a) is TypeKind.Int or TypeKind.Bool && types.Kind(b) is TypeKind.Int or TypeKind.Bool && types.Bits(a) == types.Bits(b)) return a;
        return null;
    }

    // ---- 位置 ----

    /// <summary>地址的根、常量偏移与比例下标。</summary>
    public (Sym Root, long Offset, Sym? Index, int Scale) Decompose(Sym address)
    {
        address = SymTable.Resolve(address);
        if (address is LocalSym local) return (local, 0, null, 0);
        var terms = new List<Sym>();
        Flatten(address, terms);
        long offset = 0;
        Sym? root = null, index = null;
        var scale = 0;
        var variable = terms.Where(t => t is not ConstSym).ToArray();
        foreach (var term in terms)
        {
            if (term is ConstSym c) { offset += c.Signed; continue; }
            if (Scaled(term) is var (scaled, factor) && factor > 1 && index is null) { (index, scale) = (scaled, factor); continue; }
            if (variable.Length == 1) { root = term; continue; }
            if (root is null && IsAddressRoot(term)) { root = term; continue; }
            if (index is null) { (index, scale) = (term, 1); continue; }
            root ??= term;
        }
        return (root ?? address, offset, index, scale);
    }

    private static void Flatten(Sym sym, List<Sym> terms)
    {
        sym = SymTable.Resolve(sym);
        if (sym is OpSym { Op.Kind: OperatorKind.Binary } add && add.Op.Binary == BinOp.Add)
        {
            Flatten(add.Args[0], terms);
            Flatten(add.Args[1], terms);
        }
        else terms.Add(sym);
    }

    /// <summary>左移或乘常量的下标：低位补零的拼接、或乘以常量。</summary>
    private static (Sym Index, int Factor)? Scaled(Sym term) => term switch
    {
        ConcatSym { Parts: [ConstSym { Value: 0 } zero, var rest] } when zero.Width < 8 => (rest, 1 << zero.Width),
        OpSym { Op.Kind: OperatorKind.Binary, Args: [var x, ConstSym { Value: > 1 and <= 4096 } factor] } mul when mul.Op.Binary == BinOp.Mul => (x, (int)factor.Value),
        _ => null,
    };

    private bool IsAddressRoot(Sym term) => term is EntitySym or LocalSym || TypeOf(term) is { } t && (ManagedTypes.IsReferenceType(t) || t is ByRefRef or PointerRef);

    public Location? Locate(Sym address, int width)
    {
        var (root, offset, index, scale) = Decompose(address);
        if (root is LocalSym local && index is null && memory.Find(local.Space, local.Offset + offset, width / 8) is { Promoted: false } cell && CellType(cell) is { } cellType)
        {
            var at = (int)(local.Offset + offset - cell.Start);
            var cellRoot = values.Syms.Local(cell.Space, cell.Start);
            if (at == 0 && (types.Kind(cellType) != TypeKind.Struct || types.Size(cellType) * 8 == width)) return new(LocationKind.Local, cellRoot, null, 0, null, [], cellType);
            return types.Kind(cellType) == TypeKind.Struct && FieldAt(cellType, at + RuntimeLayout.ObjectHeaderSize, width, false, false) is var (cellPath, fieldType)
                ? new(LocationKind.Local, cellRoot, null, 0, null, cellPath, fieldType) : null;
        }
        if (root is EntitySym { Symbol: { Kind: SymbolKind.StaticFields or SymbolKind.ThreadStaticFields, Value: TypeRef owner } entity } && index is null)
        {
            var thread = entity.Kind == SymbolKind.ThreadStaticFields;
            return FieldAt(owner, (int)offset, width, true, thread) is var (path, type)
                ? new Location(thread ? LocationKind.ThreadStatic : LocationKind.Static, null, null, 0, owner, path, type) : null;
        }
        var rootType = TypeOf(root);
        switch (rootType)
        {
            case ArrayRef array:
                {
                    if (index is null && offset == RuntimeLayout.ArrayMaxLength && width is 32 or 64) return new(LocationKind.Length, root, null, 0, null, [], types.Int32);
                    var size = ElementSize(array.Element);
                    if (size <= 0 || offset < RuntimeLayout.ArrayData || index is not null && scale != size) return null;
                    var within = offset - RuntimeLayout.ArrayData;
                    var (constant, inside) = (within / size, (int)(within % size));
                    if (index is not null && constant != 0) return null;
                    if (inside == 0 && (types.Kind(array.Element) != TypeKind.Struct || width == size * 8))
                        return new(LocationKind.Element, root, index, constant, null, [], array.Element);
                    return FieldAt(array.Element, inside + RuntimeLayout.ObjectHeaderSize, width, false, false) is var (path, fieldType)
                        ? new(LocationKind.Element, root, index, constant, null, path, fieldType) : null;
                }
            case DefinitionRef { Definition.FullName: "System.String" }:
                if (index is null && offset == RuntimeLayout.StringLength) return new(LocationKind.StringLength, root, null, 0, null, [], types.Int32);
                if (offset >= RuntimeLayout.StringChars && (index is null || scale == 2 && offset == RuntimeLayout.StringChars))
                    return new(LocationKind.StringChar, root, index, (offset - RuntimeLayout.StringChars) / 2, null, [], types.Char);
                return null;
            case DefinitionRef reference when ManagedTypes.IsReferenceType(reference) && index is null:
                return FieldAt(reference, (int)offset, width, false, false) is var (fields, fieldType2) ? new(LocationKind.Instance, root, null, 0, null, fields, fieldType2) : null;
            case ByRefRef or PointerRef when index is null:
                {
                    var element = rootType is ByRefRef r ? r.Element : ((PointerRef)rootType).Element;
                    if (offset == 0 && (types.Kind(element) != TypeKind.Struct || types.Size(element) * 8 == width)) return new(LocationKind.Reference, root, null, 0, null, [], element);
                    return types.Kind(element) == TypeKind.Struct && FieldAt(element, (int)offset + RuntimeLayout.ObjectHeaderSize, width, false, false) is var (inner, innerType)
                        ? new(LocationKind.Reference, root, null, 0, null, inner, innerType) : null;
                }
        }
        return null;
    }

    /// <summary>
    /// 跨越多个标量字段的访问按布局拆成逐字段的位置：每段是从该处起恰为一个标量字段的位置，Bit 为段在访问中的位偏移。
    /// 字段之间不能定位的字节按填充跳过；没有任何字段时返回 null。
    /// </summary>
    public IReadOnlyList<(Location Leaf, int Bit)>? Split(Sym address, int width)
    {
        var bytes = width / 8;
        var leaves = new List<(Location, int)>();
        for (var at = 0; at < bytes;)
        {
            var piece = at == 0 ? address : values.Syms.Binary(BinOp.Add, address, values.Syms.Const((ulong)at, 64), 64);
            Location? found = null;
            var size = 0;
            foreach (var w in new[] { 64, 32, 16, 8 })
                if (w / 8 <= bytes - at && Locate(piece, w) is { } location && types.Kind(location.Type) != TypeKind.Struct
                    && (ManagedTypes.IsReferenceType(location.Type) ? 64 : types.Size(location.Type) * 8) == w)
                { (found, size) = (location, w / 8); break; }
            if (found is null) { at++; continue; }
            leaves.Add((found, at * 8));
            at += size;
        }
        return leaves.Count > 0 ? leaves : null;
    }

    private int ElementSize(TypeRef element) => ManagedTypes.IsReferenceType(element) ? 8 : types.Size(element);

    /// <summary>
    /// 类型中 offset 处宽 width 位的字段链。offset 含对象头（值类型同样按装箱布局）；实例字段沿基类链查找。
    /// 访问恰好覆盖一个字段（bool 按字节，枚举按基础类型）时得到该字段；落在值类型字段内部时进入该字段继续查找。
    /// </summary>
    public (IReadOnlyList<FieldRef> Path, TypeRef Type)? FieldAt(TypeRef owner, int offset, int width, bool statics, bool threadStatics)
    {
        for (TypeRef? current = owner; current is DefinitionRef d; current = statics ? null : d.Definition.BaseType?.Substitute(d.Arguments, []))
        {
            if (types.Layouts.Of(d) is not { } layout) return null;
            var slots = threadStatics ? layout.ThreadStatics : statics ? layout.Statics : layout.Fields;
            foreach (var slot in slots)
            {
                var size = ManagedTypes.IsReferenceType(slot.Type) ? 8 : types.Size(slot.Type);
                if (size <= 0 || offset < slot.Offset || offset + width / 8 > slot.Offset + size) continue;
                var field = new FieldRef(slot.Field, d);
                if (offset == slot.Offset && width == size * 8) return ([field], slot.Type);
                if (types.Kind(slot.Type) == TypeKind.Struct
                    && FieldAt(slot.Type, offset - slot.Offset + RuntimeLayout.ObjectHeaderSize, width, false, false) is var (inner, innerType))
                    return ([field, .. inner], innerType);
                return null;
            }
        }
        return null;
    }
}
