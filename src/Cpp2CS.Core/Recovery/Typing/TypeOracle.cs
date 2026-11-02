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
/// <summary>访问的一段：字段 Leaf 的 [FieldBit, FieldBit+Width) 位位于访问的第 Bit 位起。</summary>
public sealed record AccessPart(Location Leaf, int Bit, int FieldBit, int Width);

public sealed record Location(LocationKind Kind, Sym? Base, Sym? Index, long ConstantIndex, TypeRef? Owner, IReadOnlyList<FieldRef> Path, TypeRef Type);

/// <summary>
/// 原子的类型与地址的位置。类型自下而上由定义给出：参数按签名，调用结果按被调用者，读取按位置，φ 取来源的汇合；
/// 常量和拼接没有自然类型，由使用处的期望类型决定。地址分解为根、常量偏移与比例下标，再按运行时布局解释为字段、元素或长度。
/// </summary>
public sealed partial class TypeOracle : Runtime.IRuntimeTyping
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
                if (type is null) return;
                var pending = new Stack<Sym>();
                var seen = new HashSet<Sym>();
                pending.Push(pointer);
                while (pending.Count > 0)
                {
                    var value = SymTable.Resolve(pending.Pop());
                    if (!seen.Add(value)) continue;
                    if (value is PhiSym phi)
                        foreach (var source in phi.Sources.OfType<Sym>()) pending.Push(source);
                    else if (value is OpSym { Op.Kind: OperatorKind.Select } select)
                        foreach (var source in select.Args.Skip(1)) pending.Push(source);
                    else if (value is LocalSym local && memory.Find(local.Space, local.Offset, 1) is { Promoted: false } target && target.Start == local.Offset)
                    {
                        if (!evidence.TryGetValue(target, out var set)) evidence[target] = set = [];
                        set.Add(type);
                    }
                }
            }
            foreach (var call in values.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                var operands = values.Operands(call);
                if (call.Op is { Kind: OpKind.Box, Operand: TypeRef boxed } && operands.Count > 2) Note(operands[2], boxed);
                if (shapes(call).Signature is not { } signature || Callee(call) is not { } callee) continue;
                foreach (var value in signature.Indirections)
                {
                    var position = call.ArgumentIndex(value.Pieces[0].Register);
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

    /// <summary>从接收者运行时类的虚表读取的方法；绑定仍需虚分派，不能当作静态类型上的直接方法。</summary>
    public MethodRef? VirtualMethod(Sym pointer, Sym receiver)
    {
        if (SymTable.Resolve(pointer) is not ReadSym { Width: 64 } read
            || Decompose(read.Address) is not (ReadSym { Width: 64 } klass, var offset, null, _)
            || offset < RuntimeLayout.ClassVtable
            || (offset - RuntimeLayout.ClassVtable) % RuntimeLayout.VirtualInvokeDataSize is not (0 or 8)
            || Decompose(klass.Address) is not (var instance, 0, null, _)
            || !ReferenceEquals(SymTable.Resolve(instance), SymTable.Resolve(receiver))
            || TypeOf(receiver) is not DefinitionRef owner || !ManagedTypes.IsReferenceType(owner)) return null;
        return DispatchResolution.Slot(owner, (int)((offset - RuntimeLayout.ClassVtable) / RuntimeLayout.VirtualInvokeDataSize), interfaceOnly: false);
    }

    public TypeRef? LocationType(Call call, int argument, int width) => argument < call.OriginalArgumentCount
        ? Locate(values.Operands(call)[argument + 1], width)?.Type : null;

    public FieldRef? FieldOperand(Call call, int argument) => argument < call.OriginalArgumentCount
        && SymTable.Resolve(values.Operands(call)[argument + 1]) is EntitySym { Symbol: { Kind: SymbolKind.Field, Value: FieldRef field } } ? field : null;

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
        Sym? Register(Storage storage) => call.ArgumentIndex(storage) is var k and >= 0 && k + 1 < operands.Count ? operands[1 + k] : null;
        Sym? StackInfo() => call.Memory.FirstOrDefault(m => !m.Write && m.Value == MachineSignature.MethodInfoIndex) is { } access
            && call.ArgumentIndex(access.Cell) is var cell and >= 0 && cell + 1 < operands.Count
            ? values.Syms.Slice(operands[1 + cell], access.CellBit, access.Width) : null;
        if (shape.Signature?.MethodInfo is { } info && (info.Register.Bank == Bank.Stack ? StackInfo() : Register(info.Register)) is { } infoSym
            && SymTable.Resolve(infoSym) is EntitySym { Symbol: { Kind: SymbolKind.Method, Value: MethodRef exact } }
            && candidates.Any(c => c.Method == exact.Method))
            return callees[call] = exact;
        var receiver = shape.Signature?.This is { } self && self.Pieces[0].Register.Bank == Bank.Gpr ? Register(self.Pieces[0].Register) : null;
        var receiverType = receiver is not null && call.Op?.Kind != OpKind.CallDelegate ? TypeOf(receiver) : null;
        if (receiverType is ByRefRef byRef) receiverType = byRef.Element;
        var arguments = shape.Signature?.Arguments.Select(a => a.Transfer == Transfer.Value && a.Pieces.Length == 1 && a.Pieces[0].Register.Bank != Bank.Stack
            ? Register(a.Pieces[0].Register) : null).ToArray() ?? [];
        // 兼容的候选中取声明类型离接收者最近的（折叠的候选机器码相同，最派生的声明对接收者一定可用）。
        var chosen = candidates.Count == 1 ? candidates[0]
            : candidates.Where(c => Compatible(c, receiverType, arguments)).OrderBy(c => Distance(receiverType, c.DeclaringType)).FirstOrDefault() ?? candidates[0];
        if (receiverType is DefinitionRef owner && !chosen.Method.IsStatic) chosen = Specialize(chosen, owner);
        return callees[call] = chosen;
    }

    /// <summary>接收者类型沿基类链到声明类型的距离；不在链上时为最大。</summary>
    private static int Distance(TypeRef? receiver, TypeRef owner)
    {
        var distance = 0;
        for (TypeRef? current = receiver; current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []), distance++)
            if (d.Definition == (owner as DefinitionRef)?.Definition) return distance;
        return int.MaxValue;
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
            case LocalSym local when memory.Find(local.Space, local.Offset, 1) is { Promoted: false } cell
                && cell.Start == local.Offset && CellType(cell) is { } cellType:
                return new ByRefRef(cellType);
            case EntitySym { Symbol: { Kind: SymbolKind.String } }:
                return types.String;
            case EntitySym { Symbol: { Kind: SymbolKind.Type } }:
                return types.RuntimeTypeHandle;
            case ResultSym result when result.Index == 0:
                return ResultType(result.Site);
            case OutSym output when output.Site.Op is null && Callee(output.Site) is { } callee:
                return output.Argument == MachineSignature.ReturnIndex ? Concrete(callee, callee.Method.ReturnType)
                    : output.Argument == -1 && callee.Method.Owner.IsValueType ? callee.DeclaringType
                    : (output.Argument < 0 ? null : Concrete(callee, callee.Method.Parameters[output.Argument].Type)) is ByRefRef byRef ? byRef.Element : null;
            case ReadSym read when Decompose(read.Address) is (ResultSym { Site.Op.Kind: OpKind.BeginCatch }, 0, null, _):
                return types.Corlib("System.Exception");
            case ReadSym read:
                return Locate(read.Address, read.Width)?.Type;
            case ConcatSym concat when CompositeRead(concat) is { } whole:
                return TypeOf(whole);
            case PhiSym phi:
                return solution.TryGetValue(phi, out var solved) ? solved : Lower(phi);
            case OpSym op:
                return OperatorType(op) ?? (op.Width is 8 or 16 or 32 or 64 && op.Op.Kind is OperatorKind.Select or OperatorKind.Binary or OperatorKind.Unary
                    ? types.Integer(op.Width, true) : null);
            case SliceSym { Base: ReadSym read } slice when Part(read, slice.Low, slice.Width) is { } part:
                return part.Type;
            case SliceSym slice when TypeOf(slice.Base) is { } baseType:
                return types.Kind(baseType) == TypeKind.Struct && FieldAt(baseType, slice.Low / 8 + RuntimeLayout.ObjectHeaderSize, slice.Width, false, false) is var (_, fieldType) ? fieldType
                    : slice.Width == 1 ? types.Boolean : slice.Width is 8 or 16 or 32 or 64 ? types.Integer(slice.Width, false) : null;
        }
        return null;
    }

    // ---- φ 的类型约束 ----

    private Dictionary<PhiSym, HashSet<TypeRef>> uses = [];
    private Dictionary<PhiSym, TypeRef?> solution = [];

    /// <summary>φ 在使用处被要求的类型（下降空跑时记录）。</summary>
    public void Use(PhiSym phi, TypeRef type)
    {
        if (!uses.TryGetValue(phi, out var set)) uses[phi] = set = [];
        set.Add(type);
    }

    /// <summary>
    /// 以记录的使用求解 φ 的类型：下界是来源定义类型的汇合；下界满足全部使用时取下界；
    /// 否则取能容纳全部定义、又满足全部使用的最具体的使用类型；没有定义时取满足全部使用的最具体者；
    /// 都不成立时保留下界，由使用处转换或报洞。求解后清除依赖类型的缓存，使用记录重新开始。
    /// </summary>
    public void Solve()
    {
        ClearCaches();
        var next = new Dictionary<PhiSym, TypeRef?>();
        foreach (var phi in uses.Keys.Concat(solution.Keys).Distinct().ToArray())
            next[phi] = Resolve(Lower(phi), uses.GetValueOrDefault(phi) ?? [], phi.Width);
        solution = next;
        uses = [];
        ClearCaches();
    }

    private void ClearCaches()
    {
        memo.Clear();
        callees.Clear();
        parts.Clear();
        storeGroups.Clear();
        cellTypes = null;
    }

    /// <summary>φ 的下界：来源（除自身、常量与未定义外）定义类型的汇合；来源之间没有公共类型时为 null。</summary>
    private TypeRef? Lower(PhiSym phi)
    {
        TypeRef? joined = null;
        foreach (var source in phi.Sources)
        {
            if (source is null || SymTable.Resolve(source) is var s && (ReferenceEquals(s, phi) || s is ConstSym or UndefSym)) continue;
            if (s is PhiSym && active.Contains(s)) continue;
            var t = TypeOf(source);
            if (t is null) continue;
            joined = joined is null ? t : Join(joined, t);
            if (joined is null) return null;
        }
        return joined;
    }

    private TypeRef? Resolve(TypeRef? lower, IReadOnlyCollection<TypeRef> used, int width)
    {
        if (used.Count == 0) return lower;
        if (lower is not null && used.All(u => Fits(lower, u))) return lower;
        var candidates = used.Where(u => (lower is null || Fits(lower, u)) && used.All(v => Fits(u, v))).ToArray();
        return candidates.FirstOrDefault(c => candidates.All(d => Fits(c, d))) ?? lower;
    }

    /// <summary>a 的值可直接用作 b：相同、可赋值，或同宽的整数类（IL 栈上 bool、整数、枚举与 char 同为整数）。</summary>
    private bool Fits(TypeRef a, TypeRef b) => a.Equals(b) || types.IsAssignable(a, b)
        || types.Kind(a) is TypeKind.Int or TypeKind.Bool && types.Kind(b) is TypeKind.Int or TypeKind.Bool && types.Bits(a) == types.Bits(b);

    /// <summary>定义与使用都不约束的值按 IL 栈语义解释为同宽整数，1 位为 bool。只在取值的类型时作缺省，不参与汇合。</summary>
    public TypeRef? Unconstrained(int width) => width == 1 ? types.Boolean : width is 8 or 16 or 32 or 64 ? types.Integer(width, true) : null;

    private TypeRef? ResultType(Call call)
    {
        if (call.Op is { } op && !shapes(call).IsDispatch)
            return Runtime.RuntimeOps.Of(op.Kind)?.ResultType?.Invoke(call, this);
        return Callee(call) is { } callee && Concrete(callee, callee.Method.ReturnType) is var ret && !ManagedTypes.IsVoid(ret) ? ret : null;
    }

    /// <summary>运行时操作的类操作数：L2 写入的 Operand，否则为实参符号值中的类实体。</summary>
    public TypeRef? ClassOperand(Call call) => call.Op?.Operand as TypeRef
        ?? values.Operands(call).Skip(1).Take(call.Arguments.Length).Select(SymTable.Resolve).OfType<EntitySym>()
            .FirstOrDefault(e => e.Symbol.Kind == SymbolKind.Class)?.Symbol.Value as TypeRef;

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
                return Defined(op.Args[1]) is { } a ? (Defined(op.Args[2]) is { } b ? Join(a, b) : a) : Defined(op.Args[2]);
            case OperatorKind.Binary when op.Op.Binary is BinOp.FAdd or BinOp.FSub or BinOp.FMul or BinOp.FDiv or BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber:
                return op.Width == 32 ? types.Single : types.Double;
            case OperatorKind.Unary when op.Op.Unary >= UnOp.FNeg:
                return op.Width == 32 ? types.Single : types.Double;
            case OperatorKind.Binary or OperatorKind.Unary:
                {
                    if (op.Width == 1 && op.Op.Kind == OperatorKind.Binary && op.Op.Binary is BinOp.And or BinOp.Or or BinOp.Xor) return types.Boolean;
                    // 补码的加减乘与按位运算不决定有无符号：操作数有同宽整数类型时沿用，否则不给定义类型，由使用处决定。
                    // 只有带符号或无符号语义的运算给出类型。
                    var operand = TypeOf(op.Args[0]);
                    if (operand is not null && types.Kind(operand) is TypeKind.Int && types.Bits(operand) == op.Width) return operand;
                    if (op.Width is not (8 or 16 or 32 or 64) || op.Op.Kind != OperatorKind.Binary) return null;
                    return op.Op.Binary switch
                    {
                        BinOp.SDiv or BinOp.SRem or BinOp.AShr => types.Integer(op.Width, true),
                        BinOp.UDiv or BinOp.URem or BinOp.LShr => types.Integer(op.Width, false),
                        _ => null,
                    };
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

    /// <summary>
    /// 选择的一路给出的定义类型：常量与未定义值不约束（同 φ 的下界）；运算只取由语义给出的类型，不取同宽整数的缺省。
    /// </summary>
    public TypeRef? Defined(Sym arm) => SymTable.Resolve(arm) switch
    {
        ConstSym or UndefSym => null,
        OpSym op => OperatorType(op),
        var other => TypeOf(other),
    };

    /// <summary>两个定义类型的汇合：相同取自身；引用类型沿基类链取最近公共超类；同宽整数取前者。</summary>
    public TypeRef? Join(TypeRef a, TypeRef b)
    {
        if (a.Equals(b)) return a;
        // 表示链上的两层是同一段位，合流处保留外层类型。
        if (Inside(a, b) is not null) return a;
        if (Inside(b, a) is not null) return b;
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

    // ---- 表示 ----

    private readonly Dictionary<TypeRef, IReadOnlyList<(IReadOnlyList<FieldRef> Path, TypeRef Type)>> representations = [];

    /// <summary>
    /// 类型的表示链：值类型恰由一个与自身同宽的实例字段组成（无填充、无其他字段）时，它与该字段的机器位型相同，
    /// 同一段位可在任一层读写。链从类型自身开始，逐层进入唯一字段，Path 为相对类型自身的字段链；引用类型字段按指针宽度计。
    /// </summary>
    public IReadOnlyList<(IReadOnlyList<FieldRef> Path, TypeRef Type)> Representation(TypeRef type)
    {
        if (representations.TryGetValue(type, out var known)) return known;
        var chain = new List<(IReadOnlyList<FieldRef> Path, TypeRef Type)> { ([], type) };
        var current = type;
        while (chain.Count < 16 && current is DefinitionRef definition && types.Kind(definition) == TypeKind.Struct
            && types.Layouts.Of(definition) is { Fields: [var slot] } && slot.Offset == RuntimeLayout.ObjectHeaderSize
            && types.Size(definition) == (ManagedTypes.IsReferenceType(slot.Type) ? 8 : types.Size(slot.Type)))
        {
            chain.Add(([.. chain[^1].Path, new FieldRef(slot.Field, definition)], slot.Type));
            current = slot.Type;
        }
        return representations[type] = chain;
    }

    /// <summary>inner 是 outer 表示链上更内的一层时，从 outer 到它的字段链。</summary>
    public (IReadOnlyList<FieldRef> Path, TypeRef Type)? Inside(TypeRef outer, TypeRef inner)
    {
        var chain = Representation(outer);
        for (var i = 1; i < chain.Count; i++)
            if (chain[i].Type.Equals(inner)) return chain[i];
        return null;
    }

    /// <summary>表示链的最内层：值类型最终包住的标量或非单字段类型。</summary>
    public (IReadOnlyList<FieldRef> Path, TypeRef Type) Innermost(TypeRef type) => Representation(type)[^1];

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
    private (Sym Index, int Factor)? Scaled(Sym term) => term switch
    {
        ConcatSym { Parts: [ConstSym { Value: 0 } zero, ..] } concat when zero.Width < 8
            => (values.Syms.Slice(concat, zero.Width, concat.Width - zero.Width), 1 << zero.Width),
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
                    if (size <= 0 || index is null && offset < RuntimeLayout.ArrayData || index is not null && scale != size) return null;
                    var within = offset - RuntimeLayout.ArrayData;
                    var inside = (int)((within % size + size) % size);
                    var constant = (within - inside) / size;
                    if (index is not null && constant != 0)
                    {
                        // 比例下标可能已包含数组头或若干元素的常量偏移。
                        while (index is SliceSym { Low: 0, Width: >= 32 } slice) index = SymTable.Resolve(slice.Base);
                        if (index is PhiSym { Projection: { Low: 0 } projection, Width: >= 32 }) index = projection.Whole;
                        index = values.Syms.Convert(ConvKind.SignExtend, index, 64);
                        index = values.Syms.Binary(BinOp.Add, index, values.Syms.Const(unchecked((ulong)constant), 64), 64);
                        constant = 0;
                    }
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

    private readonly Dictionary<ReadSym, IReadOnlyList<AccessPart>?> parts = [];

    /// <summary>不能整体定位的读取（相邻字段合并的读取）按布局拆成的整字段段；含部分段时不拆。</summary>
    public IReadOnlyList<AccessPart>? Parts(ReadSym read)
    {
        if (!parts.TryGetValue(read, out var known))
            parts[read] = known = Locate(read.Address, read.Width) is null && Split(read.Address, read.Width) is { } split
                && split.All(p => p.FieldBit == 0 && p.Width == (ManagedTypes.IsReferenceType(p.Leaf.Type) ? 64 : types.Size(p.Leaf.Type) * 8)) ? split : null;
        return known;
    }

    /// <summary>读取中恰为一个字段的一段。</summary>
    public Location? Part(ReadSym read, int bit, int width) => Parts(read)?.FirstOrDefault(p => p.Bit == bit && p.Width == width)?.Leaf;

    /// <summary>
    /// 跨越多个标量字段的访问按布局拆成的段：每段是一个标量字段 Leaf 的 [FieldBit, FieldBit+Width) 位，位于访问的第 Bit 位起。
    /// 段覆盖整个字段时 FieldBit 为 0 且 Width 为字段宽度；访问只覆盖字段一部分时为部分段。
    /// 不属于任何字段的字节是填充；不能定位又不是填充时拆分不成立，返回 null。
    /// </summary>
    public IReadOnlyList<AccessPart>? Split(Sym address, int width)
    {
        var bytes = width / 8;
        var parts = new List<AccessPart>();
        Sym At(long offset) => offset == 0 ? address : values.Syms.Binary(BinOp.Add, address, values.Syms.Const(unchecked((ulong)offset), 64), 64);
        int Bits(Location location) => ManagedTypes.IsReferenceType(location.Type) ? 64 : types.Size(location.Type) * 8;
        for (var at = 0; at < bytes;)
        {
            var piece = At(at);
            AccessPart? part = null;
            // 从此处开始的字段：整个落在访问内为整段，超出访问末尾为部分段。
            foreach (var w in new[] { 64, 32, 16, 8 })
                if (Locate(piece, w) is { } location && types.Kind(location.Type) != TypeKind.Struct && Bits(location) == w)
                {
                    part = new(location, at * 8, 0, Math.Min(w, (bytes - at) * 8));
                    break;
                }
            // 此处落在字段中间：从字段内的位置起的部分段。
            for (var k = 1; part is null && k < 8; k++)
                foreach (var w in new[] { 64, 32, 16 })
                    if (k < w / 8 && Locate(At(at - k), w) is { } containing && types.Kind(containing.Type) != TypeKind.Struct && Bits(containing) == w)
                    {
                        part = new(containing, at * 8, k * 8, Math.Min(w - k * 8, (bytes - at) * 8));
                        break;
                    }
            if (part is null)
            {
                // 只有布局中不属于任何字段的字节才是填充。
                if (!Padding(piece)) return null;
                at++;
                continue;
            }
            parts.Add(part);
            at += part.Width / 8;
        }
        return parts.Count > 0 ? parts : null;
    }

    /// <summary>地址处的字节在其容器类型的布局中不属于任何字段。容器不能确定时为 false。</summary>
    public bool Padding(Sym address)
    {
        var (root, offset, index, scale) = Decompose(address);
        (TypeRef Owner, long Offset, bool Statics, bool Thread)? container = null;
        if (root is LocalSym local && index is null && memory.Find(local.Space, local.Offset + offset, 1) is { Promoted: false } cell
            && CellType(cell) is { } cellType && types.Kind(cellType) == TypeKind.Struct)
            container = (cellType, local.Offset + offset - cell.Start + RuntimeLayout.ObjectHeaderSize, false, false);
        else if (root is EntitySym { Symbol: { Kind: SymbolKind.StaticFields or SymbolKind.ThreadStaticFields, Value: TypeRef owner } entity } && index is null)
            container = (owner, offset, true, entity.Kind == SymbolKind.ThreadStaticFields);
        else switch (TypeOf(root))
        {
            case ArrayRef array when types.Kind(array.Element) == TypeKind.Struct && ElementSize(array.Element) is var size and > 0 && offset >= RuntimeLayout.ArrayData
                && (index is null || scale == size && offset - RuntimeLayout.ArrayData < size):
                container = (array.Element, (offset - RuntimeLayout.ArrayData) % size + RuntimeLayout.ObjectHeaderSize, false, false);
                break;
            case DefinitionRef reference when ManagedTypes.IsReferenceType(reference) && index is null:
                container = (reference, offset, false, false);
                break;
            case ByRefRef { Element: var element } when types.Kind(element) == TypeKind.Struct && index is null:
                container = (element, offset + RuntimeLayout.ObjectHeaderSize, false, false);
                break;
        }
        return container is var (o, at, statics, thread) && !Covered(o, at, statics, thread);
    }

    /// <summary>布局中有字段覆盖该字节（对象头视为覆盖；值类型字段内部按其自身布局继续判断）。</summary>
    private bool Covered(TypeRef owner, long offset, bool statics, bool thread)
    {
        if (!statics && offset < RuntimeLayout.ObjectHeaderSize) return true;
        for (TypeRef? current = owner; current is DefinitionRef d; current = statics ? null : d.Definition.BaseType?.Substitute(d.Arguments, []))
        {
            if (types.Layouts.Of(d) is not { } layout) return true;
            foreach (var slot in thread ? layout.ThreadStatics : statics ? layout.Statics : layout.Fields)
            {
                var size = ManagedTypes.IsReferenceType(slot.Type) ? 8 : types.Size(slot.Type);
                if (size <= 0) return true;
                if (offset < slot.Offset || offset >= slot.Offset + size) continue;
                return types.Kind(slot.Type) != TypeKind.Struct || Covered(slot.Type, offset - slot.Offset + RuntimeLayout.ObjectHeaderSize, false, false);
            }
        }
        return false;
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
