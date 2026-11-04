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
        if (call.Op is { } op && shape.IsRuntime)
            return LowerRuntime(block, index, call, op, arguments, output);
        var signature = shape.Signature;
        if (signature is null)
        {
            // 共享空函数没有可区分的机器签名：构造函数入口的第一条调用按基类无参构造函数恢复。
            if (block == analysis.Function.Blocks[0] && !block.Statements.Take(index).Any(s => s is Call)
                && oracle.BaseConstructor(call) is { } baseCtor)
            {
                var self = oracle.Parameter(-1)!;
                output.Add(new ManagedCall(call.Address,
                    new ManagedInvocation(baseCtor, new ArgumentValue(-1, self, Width(self)), [], false), null, false));
                // 共享空构造函数以尾调用进入基类构造函数；托管体还需要同位置的 ret 结束块。
                return call.Kind is CallKind.Tail or CallKind.TailIndirect
                    ? new Statement(new ManagedReturn(call.Address, null)) : null;
            }
            output.Add(new ManagedHole(call.Address, "调用 目标或签名未知", false));
            holes.Add(new(call.Address, "调用 目标或签名未知"));
            return call.Kind is CallKind.Tail or CallKind.TailIndirect ? new Statement(new ManagedHole(call.Address, "调用 尾调用", true)) : null;
        }
        var contents = signature.Arguments.Select(v => values.ArgumentContent(call, v, arguments)).ToArray();
        var callee = oracle.Callee(call);
        if (callee is null)
        {
            holes.Add(new(call.Address, "调用 目标未知"));
            return call.Kind is CallKind.Tail or CallKind.TailIndirect ? new Statement(new ManagedHole(call.Address, "调用 目标未知", true))
                : AddHole(output, new Statement(new ManagedHole(call.Address, "调用 目标未知", false)));
        }
        // 分配之后的实例构造：合为 newobj（委托为委托构造），接收者不作为值出现。
        var construction = callee.Method.Name == ".ctor" && !callee.Method.IsStatic && contents.Length > 0
            && SymTable.Resolve(contents[0]) is ResultSym { Site.Op.Kind: OpKind.NewObject } allocated && constructions.ContainsKey(allocated) ? allocated : null;
        // newobj 必须指名分配类型自己的构造函数。调用的是基类构造时，原生代码内联了分配类型的构造函数：
        // 先写成新对象上的基类构造调用，由内联的逆以分配类型的构造函数为模板证明（InlineConstructions）。
        LocalValue? pendingReceiver = null;
        if (construction is not null && oracle.ClassOperand(construction.Site) is DefinitionRef allocatedType && callee.DeclaringType is DefinitionRef declaring
            && allocatedType.Definition != declaring.Definition)
        {
            pendingReceiver = Local(construction, allocatedType);
            pendingConstructions[pendingReceiver.Variable] = new(call.Address, allocatedType, callee);
            construction = null;
        }
        var managed = new List<ManagedValue>();
        ManagedValue? receiver = null;
        for (var i = 0; i < signature.Arguments.Length; i++)
        {
            var value = signature.Arguments[i];
            if (value.Index < 0 && construction is not null) continue;
            if (value.Index < 0 && pendingReceiver is not null) { receiver = pendingReceiver; continue; }
            var type = TypeOracle.ArgumentType(callee, value.Index);
            if (construction is not null && DelegateFacts.IsDelegate(callee.DeclaringType) && value.Index == 1 && managed.Count == 1)
            {
                if (oracle.DelegateTargetOf(contents[i], contents[Array.FindIndex(signature.Arguments, a => a.Index == 0)]) is { } target)
                {
                    var instance = managed[0];
                    if (target is SelectedDelegateTarget && instance is not (LocalValue or ArgumentValue or ConstantValue))
                    {
                        var saved = NewLocal(instance.Type);
                        output.Add(new ManagedAssignment(call.Address, saved, instance));
                        instance = saved;
                    }
                    ManagedValue Create(DelegateTarget binding) => binding switch
                    {
                        BoundDelegateTarget bound => new DelegateValue((DefinitionRef)callee.DeclaringType, instance, bound.Method, bound.Binding),
                        SelectedDelegateTarget selected => new ChoiceValue(View(selected.Condition, types.Boolean, call.Address),
                            Create(selected.True), Create(selected.False), callee.DeclaringType, 64),
                        _ => throw new NotSupportedException(binding.ToString()),
                    };
                    var created = Create(target);
                    output.Add(new ManagedAssignment(call.Address, Local(construction, callee.DeclaringType), created));
                    return call.Kind == CallKind.Tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
                }
            }
            var argument = value.Index < 0 && call.Op?.Kind == OpKind.CallDelegate && call.DelegateReceiver is not null
                ? View(operands[1 + call.Arguments.Length], type, call.Address)
                : Unconstrained(shape, value, type, contents[i]) ?? Argument(call, value, type, contents[i], arguments, output);
            if (value.Index < 0) receiver = argument;
            else managed.Add(argument);
        }
        if (construction is not null)
        {
            output.Add(new ManagedAssignment(call.Address, Local(construction, callee.DeclaringType), new NewObjectValue(callee, managed)));
            return call.Kind == CallKind.Tail ? new Statement(new ManagedReturn(call.Address, null)) : null;
        }
        var dispatched = shape.IsDispatch || call.Resolved is not null && call.Kind is CallKind.Indirect or CallKind.TailIndirect;
        var invocation = new ManagedInvocation(callee, receiver, managed, Virtual: receiver is not null
            && (dispatched || !callee.Method.IsVirtual && absorbedChecks.Contains(contents[0])));
        LocalValue? result = null;
        var returnType = callee.Concrete(callee.Method.ReturnType);
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
        var lowered = new ManagedCall(call.Address, invocation, tail ? null : result, tail) { Inlined = call.Inlined };
        if (tail) return new Statement(lowered);
        output.Add(lowered);
        if (call.DoesNotReturn && ManagedTypes.IsVoid(oracle.ReturnType))
            return new Statement(new ManagedReturn(call.Address, null));
        return null;
    }

    /// <summary>
    /// 被调方不读取的按值实参：原生代码不维护这些寄存器，内容与参数类型不兼容时，接收者取类型兼容的 this，其他取默认值。
    /// 这是推断：被调方的行为与该实参无关，任何类型正确的值都等价。
    /// </summary>
    private ManagedValue? Unconstrained(Calls.CallShape shape, MachineValue value, TypeRef type, Sym content)
        => oracle.Supply(shape, value, type, content) switch
        {
            ArgumentSupply.This => new ArgumentValue(-1, oracle.Parameter(-1)!, Width(oracle.Parameter(-1)!)),
            ArgumentSupply.Default => new ConstantValue(0, type, Width(type)),
            _ => null,
        };

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
                    var stored = values.CellContent(call, value, arguments, write: false);
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
                        if (values.CellContent(call, value, arguments, write: false) is { } before)
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

    private Terminator? LowerRuntime(Block block, int index, Call call, RuntimeOp op, IReadOnlyList<Sym> arguments, List<ManagedStatement> output)
    {
        var tail = call.Kind is CallKind.Tail or CallKind.TailIndirect;
        var context = new RuntimeContext(this, block, index, call, op, arguments, output);
        if (RuntimeOps.Of(op.Kind)?.Lower is { } lower && lower(context, out var terminal))
        {
            if (terminal is not null) return new Statement(terminal);
            if (!tail) return null;
            // 运行时尾调用与普通尾调用相同：结果寄存器按当前方法的返回类型解释。
            var returned = oracle.ReturnType is { } type && !ManagedTypes.IsVoid(type) ? View(context.Result, type, call.Address) : null;
            return new Statement(new ManagedReturn(call.Address, returned));
        }
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
        public Sym Result => owner.values.Syms.Result(call, 0, RuntimeOps.Of(op.Kind)?.ResultWidths?.Invoke(call) is [var width] ? width : 64);
        public Sym ResultAt(int result) => owner.values.Syms.Result(call, result + 1, RuntimeOps.Of(op.Kind)!.ResultWidths!(call)[result]);
        public ManagedValue Input(int index)
        {
            var input = RuntimeOps.Of(op.Kind)!.Inputs!(call, Arguments, owner.oracle)[index];
            if (input.Kind == RuntimeInputKind.Value) return owner.View(input.Value, input.Type, call.Address);
            if (input.Kind == RuntimeInputKind.Pointee && owner.values.CellContent(call, input.Pointee, arguments, false) is { } content)
                return owner.View(content, input.Type, call.Address);
            return input.Type is { } type && owner.oracle.Locate(input.Value, owner.types.StorageBits(type)) is { } location
                ? owner.LocationValue(location, call.Address) : owner.Hole(call.Address, "运行时 输入位置未知", input.Type);
        }
        public TypeRef? TypeOf(Sym sym) => owner.oracle.TypeOf(sym);
        public LocalValue Local(Sym sym, TypeRef type) => owner.Local(sym, type);
        public LocalValue Temporary(TypeRef type) => owner.NewLocal(type);
        public void Emit(ManagedStatement statement) => output.Add(statement);
        public void AwaitConstruction()
        {
            owner.constructions[(ResultSym)Result] = call;
            if (Cpp2CS.Recovery.Effects.ConstructionPrelude.Find(owner.analysis, owner.oracle, owner.effects, call) is { } prelude)
            {
                var local = owner.Local(Result, prelude.Type);
                owner.pendingConstructions[local.Variable] = new(prelude.Address, prelude.Type, prelude.Base);
            }
        }
        public MethodRef? ExceptionConstructor(string fullName) => owner.Constructor(fullName);
        public ManagedValue Hole(string reason, TypeRef? type) => owner.Hole(call.Address, reason, type);

        public bool InFault => owner.regions.Any(r => !r.IsCatch && r.Handler.Contains(block));

        public Sym? ClassOwner(Sym klass) => owner.oracle.ClassOwner(klass);

        public bool InitializesNext(TypeRef type) => owner.effects.Initializes(block, index + 1, type);

        public bool InCatchOf(Sym exception) => owner.regions.Any(r => r.IsCatch && r.Handler.Contains(block)
            && SymTable.Resolve(exception) is ReadSym read && owner.oracle.Decompose(read.Address) is (ResultSym { Site: var begin }, 0, null, _) && ReferenceEquals(begin, r.BeginCatch));

        public bool KnownNonNull(Sym target) => owner.effects.KnownNonNull(block, index, target);

        public bool AbsorbBounds(Sym position, Sym length) => owner.effects.BoundsAbsorbed(block, index + 1, position, length);

        public bool Absorb(Sym target)
        {
            if (!owner.effects.Absorbed(block, index + 1, target)) return false;
            owner.absorbedChecks.Add(target);
            return true;
        }

        public ManagedValue Field(ManagedValue receiver, FieldRef field) => owner.FieldAccess(receiver, field, owner.FieldType(field, null), true, call.Address);
    }

    private MethodRef? Constructor(string exception) => oracle.ExceptionType(exception) is { } type
        ? type.Definition.Methods.FirstOrDefault(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 0) is { } ctor ? new MethodRef(ctor, [], []) : null
        : null;
}
