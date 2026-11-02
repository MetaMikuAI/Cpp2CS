using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>调用的下降：按机器签名重组实参、构造与内联证明、运行时操作。</summary>
internal sealed partial class BodyBuilder
{
    private Terminator? LowerCall(Block block, int index, Call call, IReadOnlyList<Sym> operands, List<ManagedStatement> output)
    {
        var arguments = operands.Skip(1).Take(call.Arguments.Length).ToArray();
        var shape = analysis.Environment.Shape(call);
        if (call.Op is { } op && !shape.IsDispatch)
            return LowerRuntime(block, index, call, op, arguments, output);
        var signature = shape.Signature;
        if (signature is null)
        {
            output.Add(new ManagedHole(call.Address, "调用 目标或签名未知", false));
            holes.Add(new(call.Address, "调用 目标或签名未知"));
            return call.Kind is CallKind.Tail or CallKind.TailIndirect ? new Statement(new ManagedHole(call.Address, "调用 尾调用", true)) : null;
        }
        var contents = signature.Arguments.Select(v => Content(call, v, arguments)).ToArray();
        var callee = oracle.Callee(call);
        if (callee is null)
        {
            holes.Add(new(call.Address, "调用 目标未知"));
            return call.Kind is CallKind.Tail or CallKind.TailIndirect ? new Statement(new ManagedHole(call.Address, "调用 目标未知", true))
                : AddHole(output, new Statement(new ManagedHole(call.Address, "调用 目标未知", false)));
        }
        // 分配之后的实例构造：合为 newobj（委托为委托构造），接收者不作为值出现。
        var transparent = false;
        var construction = callee.Method.Name == ".ctor" && !callee.Method.IsStatic && contents.Length > 0
            && SymTable.Resolve(contents[0]) is ResultSym { Site.Op.Kind: OpKind.NewObject } allocated && constructions.ContainsKey(allocated) ? allocated : null;
        // newobj 必须指名分配类型自己的构造函数。调用的是基类构造时，原生代码内联了分配类型的构造函数：
        // 以该构造函数自身原生代码的恢复体为证据，证明它只把参数原样转给这个基类构造，则调用点即 newobj 它。
        if (construction is not null && oracle.ClassOperand(construction.Site) is DefinitionRef allocatedType && callee.DeclaringType is DefinitionRef declaring
            && allocatedType.Definition != declaring.Definition)
        {
            if (ConstructorWithStores(block, index, construction, allocatedType, callee) is { } rebuilt)
            {
                output.Add(new ManagedAssignment(call.Address, Local(construction, allocatedType), rebuilt));
                return null;
            }
            var (inlined, reason) = InlinedConstructor(allocatedType, callee);
            if (inlined is not null)
            {
                callee = inlined;
                transparent = true;
                goto Constructed;
            }
            holes.Add(new(call.Address, $"构造 {allocatedType} 的构造函数被内联为 {callee}：{reason}"));
            output.Add(new ManagedHole(call.Address, $"构造 {allocatedType} 的构造函数被内联", false));
            locals[construction] = NewLocal(allocatedType);
            return call.Kind == CallKind.Tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
        }
        Constructed:
        var managed = new List<ManagedValue>();
        ManagedValue? receiver = null;
        for (var i = 0; i < signature.Arguments.Length; i++)
        {
            var value = signature.Arguments[i];
            if (value.Index < 0 && construction is not null) continue;
            var type = value.Index < 0 ? (callee.Method.Owner.IsValueType ? new ByRefRef(callee.DeclaringType) : callee.DeclaringType)
                : TypeOracle.Concrete(callee, callee.Method.Parameters[value.Index].Type);
            if (construction is not null && DelegateFacts.IsDelegate(callee.DeclaringType) && value.Index == 1
                && SymTable.Resolve(contents[i]) is EntitySym { Symbol: { Kind: SymbolKind.Method, Value: MethodRef target } } && managed.Count == 1)
            {
                var created = new DelegateValue((DefinitionRef)callee.DeclaringType, managed[0], target, target.Method.IsStatic ? DelegateBinding.Static : DelegateBinding.ClosedInstance);
                output.Add(new ManagedAssignment(call.Address, Local(construction, callee.DeclaringType), created));
                return call.Kind == CallKind.Tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
            }
            var argument = value.Index < 0 && call.Op?.Kind == OpKind.CallDelegate && call.DelegateReceiver is not null
                ? View(operands[1 + call.Arguments.Length], type, call.Address)
                : Unconstrained(shape, value, type, contents[i]) ?? Argument(call, value, type, contents[i], arguments, output);
            if (value.Index < 0) receiver = argument;
            else managed.Add(argument);
        }
        if (construction is not null)
        {
            // 内联证明成立时标为透明：原生代码执行的是被内联的构造函数体。
            output.Add(new ManagedAssignment(call.Address, Local(construction, callee.DeclaringType), new NewObjectValue(callee, managed) { Transparent = transparent }));
            return call.Kind == CallKind.Tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
        }
        var dispatched = shape.IsDispatch || call.Resolved is not null && call.Kind is CallKind.Indirect or CallKind.TailIndirect;
        var invocation = new ManagedInvocation(callee, receiver, managed, Virtual: receiver is not null && (dispatched || absorbedChecks.Contains(contents[0])));
        LocalValue? result = null;
        var returnType = TypeOracle.Concrete(callee, callee.Method.ReturnType);
        if (!ManagedTypes.IsVoid(returnType))
            result = signature.Return?.Transfer == Transfer.ResultBuffer
                ? Local(values.Syms.Out(call, MachineSignature.ReturnIndex, MethodEnvironment.ValueWidth(signature.Return)), returnType)
                : Local(values.Syms.Result(call, 0, signature.Return is { } ret ? MethodEnvironment.ValueWidth(ret) : Width(returnType)), returnType);
        var tail = call.Kind is CallKind.Tail or CallKind.TailIndirect;
        // 尾调用原样返回被调用者的结果寄存器；两者的返回类型不同（如按值返回的单字段结构体与其字段）时，返回值是同一段位在调用方返回类型下的值。
        if (tail && result is not null && oracle.ReturnType is { } own && !ManagedTypes.IsVoid(own) && !own.Equals(returnType)
            && !(ManagedTypes.IsReferenceType(own) && ManagedTypes.IsReferenceType(returnType))
            && signature.Return is { Transfer: Transfer.Value } returned && analysis.Signature.Return is { Transfer: Transfer.Value } caller
            && MethodEnvironment.ValueWidth(caller) <= MethodEnvironment.ValueWidth(returned))
        {
            output.Add(new ManagedCall(call.Address, invocation, result, false));
            var bits = values.Syms.Result(call, 0, MethodEnvironment.ValueWidth(returned));
            return new Statement(new ManagedReturn(call.Address, View(values.Syms.Slice(bits, 0, MethodEnvironment.ValueWidth(caller)), own, call.Address)));
        }
        var lowered = new ManagedCall(call.Address, invocation, tail ? null : result, tail);
        if (tail) return new Statement(lowered);
        output.Add(lowered);
        return null;
    }

    /// <summary>
    /// 分配类型中与基类构造参数相同、且自身方法体只把参数原样转给该基类构造的构造函数（内联的逆：以被调方法的恢复体为证据）。
    /// </summary>
    private (MethodRef? Constructor, string Reason) InlinedConstructor(DefinitionRef allocated, MethodRef baseConstructor)
    {
        var reasons = new List<string>();
        foreach (var definition in allocated.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == baseConstructor.Method.Parameters.Count))
        {
            var candidate = new MethodRef(definition, allocated.Arguments, []);
            if (summaries(candidate) is not { Body: { } body })
            {
                reasons.Add(definition.Address == 0 ? "构造函数没有原生代码" : "构造函数自身未能恢复");
                continue;
            }
            var effects = body.Blocks.SelectMany(b => b.Statements).Where(s => s is not ManagedJump).ToArray();
            var forwarded = effects is [ManagedCall { Tail: true } only] || effects is [ManagedCall { Tail: false, Result: null } first, ManagedReturn { Value: null }]
                ? (ManagedCall)effects[0] : null;
            if (forwarded is { Invocation: { Receiver: ArgumentValue { Index: -1 } } invocation }
                && invocation.Method.Method == baseConstructor.Method
                && invocation.Arguments.Select((a, i) => a is ArgumentValue { Index: var k } && k == i).All(x => x))
                return (candidate, "");
            reasons.Add("构造函数体不只是转给基类构造");
        }
        return (null, reasons.Count == 0 ? "没有参数相同的构造函数" : string.Join("；", reasons.Distinct()));
    }

    /// <summary>
    /// 被调方不读取的按值实参：原生代码不维护这些寄存器，内容与参数类型不兼容时，接收者取类型兼容的 this，其他取默认值。
    /// 这是推断：被调方的行为与该实参无关，任何类型正确的值都等价。
    /// </summary>
    private ManagedValue? Unconstrained(Calls.CallShape shape, MachineValue value, TypeRef type, Sym content)
    {
        if (value.Transfer != Transfer.Value || value.Pieces.Length == 0 || !value.Pieces.All(p => shape.Unused.Contains(p.Register))) return null;
        if (oracle.TypeOf(content) is { } actual && (actual.Equals(type) || types.IsAssignable(actual, type))) return null;
        if (value.Index < 0 && oracle.Parameter(-1) is { } self && (self.Equals(type) || types.IsAssignable(self, type)))
            return new ArgumentValue(-1, self, Width(self));
        return ManagedTypes.IsReferenceType(type) || types.Kind(type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Pointer
            ? new ConstantValue(0, type, Width(type)) : null;
    }

    /// <summary>机器签名中一个值在调用处的内容：寄存器片与栈片按值中的位置拼接。</summary>
    private Sym Content(Call call, MachineValue value, IReadOnlyList<Sym> arguments)
    {
        var syms = values.Syms;
        var width = value.Transfer == Transfer.Value ? MethodEnvironment.ValueWidth(value) : 64;
        var parts = new SortedDictionary<int, Sym>();
        if (value.Transfer == Transfer.Value)
        {
            foreach (var piece in value.Pieces)
            {
                var position = call.ArgumentIndex(piece.Register);
                if (position >= 0) parts[piece.Offset * 8] = syms.Slice(arguments[position], 0, Math.Min(piece.Width, arguments[position].Width));
            }
            foreach (var access in call.Memory.Where(m => !m.Write && m.Value == value.Index))
                if (call.ArgumentIndex(access.Cell) is var cell and >= 0)
                    parts[access.ValueBit] = syms.Slice(arguments[cell], access.CellBit, access.Width);
        }
        else if (call.ArgumentIndex(value.Pieces[0].Register) is var pointer and >= 0)
            return arguments[pointer];
        if (parts.Count == 0) return syms.Unknown("实参缺失", width);
        var list = new List<Sym>();
        var at = 0;
        foreach (var (bit, part) in parts)
        {
            if (bit < at) continue;
            if (bit > at) list.Add(syms.Undef(bit - at));
            var size = Math.Min(part.Width, width - bit);
            if (size <= 0) break;
            list.Add(syms.Slice(part, 0, size));
            at = bit + size;
        }
        if (at < width) list.Add(syms.Undef(width - at));
        return syms.Concat(list);
    }

    /// <summary>
    /// 一个 IL 实参。按值传递时为内容的视图；按副本传递时为被指单元在调用前的内容；
    /// ref 实参指向已提升的单元时成为局部：调用前写入原内容，调用写出的值即该局部，再取其地址。
    /// </summary>
    private ManagedValue Argument(Call call, MachineValue value, TypeRef type, Sym content, IReadOnlyList<Sym> arguments, List<ManagedStatement> output)
    {
        switch (value.Transfer)
        {
            case Transfer.Value:
                return View(content, type, call.Address);
            case Transfer.Copy:
                {
                    var stored = CellContent(call, value, arguments, write: false);
                    if (stored is not null) return View(stored, type, call.Address);
                    return SymTable.Resolve(content) is var p && oracle.Locate(p, value.Size * 8) is { } location
                        ? LocationValue(location, call.Address) : Hole(call.Address, "调用 副本实参的内容未知", type);
                }
            case Transfer.Reference:
                {
                    var element = type is ByRefRef byRef ? byRef.Element : type;
                    var elementBits = types.Kind(element) == TypeKind.Struct ? types.Size(element) * 8 : Math.Max(8, Width(element));
                    if (SymTable.Resolve(content) is LocalSym escaped && analysis.Memory.Find(escaped.Space, escaped.Offset, 1) is { Promoted: false })
                        return oracle.Locate(escaped, elementBits) is { } escapedLocation
                            ? new AddressValue(LocationValue(escapedLocation, call.Address)) : Hole(call.Address, $"调用 ref 实参指向的可寻址局部 {escaped}", type);
                    if (SymTable.Resolve(content) is LocalSym)
                    {
                        var local = NewLocal(element);
                        if (CellContent(call, value, arguments, write: false) is { } before)
                            output.Add(new ManagedAssignment(call.Address, local, View(before, element, call.Address)));
                        if (call.Memory.Any(m => m.Write && m.Value == value.Index))
                            locals[values.Syms.Out(call, value.Index, value.Size * 8)] = local;
                        return new AddressValue(local);
                    }
                    if (oracle.TypeOf(content) is ByRefRef or PointerRef) return View(content, type, call.Address);
                    return oracle.Locate(content, Math.Max(8, value.Size * 8)) is { } target
                        ? new AddressValue(LocationValue(target, call.Address)) : Hole(call.Address, $"调用 ref 实参的位置 {content}", type);
                }
            default:
                return Hole(call.Address, $"调用 实参传递方式 {value.Transfer}", type);
        }
    }

    /// <summary>调用读取的单元中属于 value 的内容。</summary>
    private Sym? CellContent(Call call, MachineValue value, IReadOnlyList<Sym> arguments, bool write)
    {
        var accesses = call.Memory.Where(m => m.Write == write && m.Value == value.Index).OrderBy(m => m.ValueBit).ToArray();
        if (accesses.Length == 0) return null;
        var syms = values.Syms;
        var parts = new List<Sym>();
        var at = 0;
        var width = accesses[0].ValueWidth;
        foreach (var access in accesses)
        {
            if (access.ValueBit < at) continue;
            if (access.ValueBit > at) parts.Add(syms.Undef(access.ValueBit - at));
            var position = call.ArgumentIndex(access.Cell);
            if (position < 0) return null;
            parts.Add(syms.Slice(arguments[position], access.CellBit, access.Width));
            at = access.ValueBit + access.Width;
        }
        if (at < width) parts.Add(syms.Undef(width - at));
        return syms.Concat(parts);
    }

    private Terminator? LowerRuntime(Block block, int index, Call call, RuntimeOp op, IReadOnlyList<Sym> arguments, List<ManagedStatement> output)
    {
        var tail = call.Kind is CallKind.Tail or CallKind.TailIndirect;
        var context = new RuntimeContext(this, block, index, call, op, arguments, output);
        if (RuntimeOps.Of(op.Kind)?.Lower is { } lower && lower(context, out var terminal))
            return terminal is not null ? new Statement(terminal) : tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
        holes.Add(new(call.Address, $"运行时 {op.Kind}"));
        if (tail) return new Statement(new ManagedHole(call.Address, $"运行时 {op}", true));
        output.Add(new ManagedHole(call.Address, $"运行时 {op}", false));
        return null;
    }

    /// <summary>运行时操作下降的上下文。</summary>
    private sealed class RuntimeContext(BodyBuilder owner, Block block, int index, Call call, RuntimeOp op, IReadOnlyList<Sym> arguments, List<ManagedStatement> output) : IRuntimeLowering
    {
        public ManagedTypes Types => owner.types;
        public Call Call => call;
        public RuntimeOp Op => op;
        public TypeRef? ClassOperand => owner.oracle.ClassOperand(call);
        public IReadOnlyList<Sym> Arguments { get; } = arguments.Take(call.OriginalArgumentCount).ToArray();
        public Sym Result => owner.values.Syms.Result(call, 0, 64);
        public ManagedValue View(Sym sym, TypeRef? expected) => owner.View(sym, expected, call.Address);
        public TypeRef? TypeOf(Sym sym) => owner.oracle.TypeOf(sym);
        public LocalValue Local(Sym sym, TypeRef type) => owner.Local(sym, type);
        public void Emit(ManagedStatement statement) => output.Add(statement);
        public void AwaitConstruction() => owner.constructions[(ResultSym)Result] = call;
        public MethodRef? ExceptionConstructor(string fullName) => owner.Constructor(fullName);
        public ManagedValue Hole(string reason, TypeRef? type) => owner.Hole(call.Address, reason, type);

        public bool InFault => owner.regions.Any(r => !r.IsCatch && r.Handler.Contains(block));

        public Sym? ClassOwner(Sym klass) => owner.ClassOwner(klass);

        public bool InitializesNext(TypeRef type) => owner.Initializes(block, index + 1, type);

        public bool InCatchOf(Sym exception) => owner.regions.Any(r => r.IsCatch && r.Handler.Contains(block)
            && SymTable.Resolve(exception) is ReadSym read && owner.oracle.Decompose(read.Address) is (ResultSym { Site: var begin }, 0, null, _) && ReferenceEquals(begin, r.BeginCatch));

        public bool KnownNonNull(Sym target) => owner.KnownNonNull(block, index, target);

        public bool AbsorbBounds(Sym position, Sym length) => owner.BoundsAbsorbed(block, index + 1, position, length);

        public bool Absorb(Sym target)
        {
            if (!owner.Absorbed(block, index + 1, target)) return false;
            owner.absorbedChecks.Add(target);
            return true;
        }

        public Sym? Pointee(int value)
        {
            var reads = call.Memory.Where(m => !m.Write && m.Value == value).OrderBy(m => m.ValueBit).ToArray();
            if (reads.Length == 0) return null;
            var syms = owner.values.Syms;
            return syms.Concat(reads.Select(m => syms.Slice(arguments[call.ArgumentIndex(m.Cell)], m.CellBit, m.Width)));
        }

        public ManagedValue? Location(int argument, TypeRef type) =>
            argument < arguments.Count && owner.oracle.Locate(arguments[argument], owner.Width(type)) is { } location ? owner.LocationValue(location, call.Address) : null;

        public ManagedValue Field(Sym receiver, FieldRef field) => owner.FieldAccess(owner.View(receiver, owner.oracle.TypeOf(receiver), call.Address), field, owner.FieldType(field, null), true, call.Address);
    }

    private MethodRef? Constructor(string exception) => oracle.ExceptionType(exception) is { } type
        ? type.Definition.Methods.FirstOrDefault(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 0) is { } ctor ? new MethodRef(ctor, [], []) : null
        : null;
}
