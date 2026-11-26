using System.Collections.Immutable;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.IL;

namespace Cpp2CS.Kernel.Forward;

/// <summary>展开的结果：模板一侧的效果图，以及每条指令用到的目录项、每个块对应的 IL 偏移。</summary>
public sealed record Expansion(FlowGraph<TemplateEffect> Graph, ImmutableArray<(int Offset, string Entry)> Entries,
    ImmutableArray<int> BlockOffsets);

/// <summary>
/// 把一个方法体的 IL 按操作目录展开成模板一侧的效果图（6.2 的“展开”）。
///
/// 图的约定：入口块声明各形参（槽位类别为 Managed），把局部变量清零，转到偏移 0 处的块。
/// 局部变量从零开始只在方法头设置了 InitLocals 时成立（ECMA-335 II.25.4.4、I.12.3.2.2）；有局部变量而没有设置时不展开。
/// 其余每个块对应 IL 的一个基本块，参数依次是各形参、各局部变量、进入时求值栈上的各项，都按栈上的位宽。
/// 每个块只用自己的参数，所以每个基本块只翻译一次；不同入边带来的栈的形状必须相同。
/// </summary>
public sealed class IlExpander
{
    private readonly record struct StackValue(Term Value, StackKind Kind);

    private sealed class State
    {
        public required Term[] Arguments;
        public required Term[] Locals;
        public required List<StackValue> Stack;
    }

    private readonly MethodBody body;
    private readonly IMetadataView metadata;
    private readonly ITokenResolver tokens;
    private readonly TermPool terms;
    private readonly int pointerBits;
    private readonly FlowBuilder<TemplateEffect> flow;
    private readonly ImmutableArray<Instruction> instructions;
    private readonly Dictionary<int, int> indexAt = [];
    private readonly HashSet<int> leaders = [];
    private readonly Dictionary<int, (BlockId Block, ImmutableArray<StackKind> Stack)> blocks = [];
    private readonly Queue<int> pending = new();
    private readonly List<(int Offset, string Entry)> used = [];
    private readonly List<int> blockOffsets = [-1];

    private IlExpander(MethodBody body, IMetadataView metadata, ITokenResolver tokens, TermPool terms, int graph, int pointerBits)
    {
        this.body = body;
        this.metadata = metadata;
        this.tokens = tokens;
        this.terms = terms;
        this.pointerBits = pointerBits;
        flow = new FlowBuilder<TemplateEffect>(terms, graph);
        instructions = IlDecoder.Decode(body.Code.AsSpan());
        for (int i = 0; i < instructions.Length; i++) indexAt[instructions[i].Offset] = i;
    }

    /// <summary>展开一个方法体。不能展开时抛出 <see cref="ExpansionException"/>，写明原因。</summary>
    public static Expansion Expand(MethodBody body, IMetadataView metadata, ITokenResolver tokens, TermPool terms, int graph, int pointerBits)
    {
        if (graph <= 0) throw new ArgumentException("模板一侧的图号须大于 0");
        if (body.ExceptionRegions > 0) throw new ExpansionException("异常处理区域不在首批范围内", $"{body.ExceptionRegions} 个区域");
        var expander = new IlExpander(body, metadata, tokens, terms, graph, pointerBits);
        return expander.Run();
    }

    private Expansion Run()
    {
        if (instructions.Length == 0) throw new ExpansionException("方法体为空", "");
        // 基本块的起点：偏移 0、各转移目标、转移与返回之后的指令。
        leaders.Add(0);
        foreach (var instruction in instructions)
        {
            var flowKind = instruction.Opcode.Flow;
            if (flowKind is FlowKind.Branch or FlowKind.ConditionalBranch) Leader((int)instruction.Operand, instruction);
            foreach (int target in instruction.Targets) Leader(target, instruction);
            if (flowKind is not (FlowKind.Next or FlowKind.Prefix) && instruction.Next < body.Code.Length) Leader(instruction.Next, instruction);
        }

        // 入口块：形参按存储位宽进入，扩到栈上的位宽；局部变量清零。
        var method = body.Method;
        if (body.Locals.Length > 0 && !body.InitLocals)
            throw new ExpansionException("局部变量没有初始化的保证", "方法头没有设置 InitLocals，局部变量的初值没有依据");
        var arguments = new Term[method.Parameters.Length];
        for (int i = 0; i < arguments.Length; i++)
        {
            var type = method.Parameters[i];
            arguments[i] = Widen(flow.EntryParameter(new Slot(SlotKind.Managed, i), type.StorageBits), type);
        }
        var locals = new Term[body.Locals.Length];
        for (int i = 0; i < locals.Length; i++) locals[i] = Zeros(body.Locals[i].StackBits);
        flow.SetReturnWidths(method.Return is { } returned ? [returned.StorageBits] : []);
        var initial = new State { Arguments = arguments, Locals = locals, Stack = [] };
        flow.Terminate(flow.Entry, Terminator.Single(Edge(0, initial, instructions[0])));

        while (pending.Count > 0) Translate(pending.Dequeue());
        return new Expansion(flow.Build(), [.. used], [.. blockOffsets]);
    }

    private void Leader(int offset, Instruction from)
    {
        if (!indexAt.ContainsKey(offset)) throw new ExpansionException("IL 无法解码", $"{from} 的目标 {offset:x4} 不在指令边界上", from.Offset);
        leaders.Add(offset);
    }

    private Term Zeros(int width)
    {
        if (width <= 128) return terms.Zero(width);
        var parts = new List<Term>();
        for (int left = width; left > 0; left -= 128) parts.Add(terms.Zero(Math.Min(left, 128)));
        return terms.Concat(parts);
    }

    private int StackBits(StackKind kind, Term value) => kind switch
    {
        StackKind.Int32 or StackKind.Float32 => 32,
        StackKind.Int64 or StackKind.Float64 => 64,
        StackKind.Value => value.Width,
        _ => pointerBits,
    };

    /// <summary>去往某个偏移处的块的出口：整行实参是当前的形参、局部变量与栈。</summary>
    private Exit Edge(int offset, State state, Instruction from)
    {
        ImmutableArray<StackKind> stack = [.. state.Stack.Select(v => v.Kind)];
        if (!blocks.TryGetValue(offset, out var known))
        {
            var widths = new List<int>();
            for (int i = 0; i < state.Arguments.Length; i++) widths.Add(body.Method.Parameters[i].StackBits);
            for (int i = 0; i < state.Locals.Length; i++) widths.Add(body.Locals[i].StackBits);
            foreach (var value in state.Stack) widths.Add(value.Value.Width);
            known = (flow.Block(System.Runtime.InteropServices.CollectionsMarshal.AsSpan(widths)), stack);
            blocks.Add(offset, known);
            blockOffsets.Add(offset);
            pending.Enqueue(offset);
        }
        else if (!known.Stack.SequenceEqual(stack))
            throw new ExpansionException("合流处栈的形状不一致", $"偏移 {offset:x4}", from.Offset);
        var row = new List<Term>(state.Arguments.Length + state.Locals.Length + state.Stack.Count);
        row.AddRange(state.Arguments);
        row.AddRange(state.Locals);
        foreach (var value in state.Stack) row.Add(value.Value);
        var parameters = flow.Parameters(known.Block);
        for (int i = 0; i < row.Count; i++)
            if (row[i].Width != parameters[i].Width)
                throw new ExpansionException("合流处栈的形状不一致", $"偏移 {offset:x4} 的第 {i} 项位宽不同", from.Offset);
        return Exit.To(known.Block, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(row));
    }

    private void Translate(int start)
    {
        var (block, stackKinds) = blocks[start];
        var parameters = flow.Parameters(block);
        int argumentCount = body.Method.Parameters.Length, localCount = body.Locals.Length;
        var state = new State
        {
            Arguments = [.. parameters.AsSpan(0, argumentCount)],
            Locals = [.. parameters.AsSpan(argumentCount, localCount)],
            Stack = [],
        };
        for (int i = 0; i < stackKinds.Length; i++) state.Stack.Add(new(parameters[argumentCount + localCount + i], stackKinds[i]));

        for (int index = indexAt[start]; ; index++)
        {
            var instruction = instructions[index];
            if (Apply(block, state, instruction)) return;
            if (index + 1 >= instructions.Length)
                throw new ExpansionException("IL 无法解码", "方法体在没有返回的地方结束", instruction.Offset);
            if (leaders.Contains(instruction.Next))
            {
                flow.Terminate(block, Terminator.Single(Edge(instruction.Next, state, instruction)));
                return;
            }
        }
    }

    private static bool Matches(StackClass required, StackKind kind, Context context) => required switch
    {
        StackClass.Int32 => kind == StackKind.Int32,
        StackClass.Int64 => kind == StackKind.Int64,
        StackClass.NativeInt => kind == StackKind.NativeInt,
        StackClass.Integer => kind is StackKind.Int32 or StackKind.Int64 or StackKind.NativeInt,
        StackClass.Float32 => kind == StackKind.Float32,
        StackClass.Float64 => kind == StackKind.Float64,
        StackClass.Float => kind is StackKind.Float32 or StackKind.Float64,
        StackClass.Object => kind == StackKind.Object,
        StackClass.ByRef => kind == StackKind.ByRef,
        StackClass.Value => kind == StackKind.Value,
        StackClass.Scalar => kind is StackKind.Int32 or StackKind.Int64 or StackKind.NativeInt or StackKind.Object or StackKind.ByRef,
        StackClass.Assignable => context.Subject is { } subject && Assignable(kind, subject),
        _ => true,
    };

    /// <summary>栈上一个类别的值能否存入一个类型，按 ECMA-335 III.1.6 表 III.9。值类型只能核对大小：栈上不记录值类型的身份。</summary>
    private static bool Assignable(StackKind kind, TypeShape type) => type.Kind switch
    {
        StackKind.Int32 => kind is StackKind.Int32 or StackKind.NativeInt,
        StackKind.Int64 => kind == StackKind.Int64,
        StackKind.NativeInt => kind is StackKind.Int32 or StackKind.NativeInt,
        StackKind.Float32 or StackKind.Float64 => kind is StackKind.Float32 or StackKind.Float64,
        StackKind.Object => kind == StackKind.Object,
        StackKind.ByRef => kind is StackKind.ByRef or StackKind.NativeInt,
        _ => kind == StackKind.Value,
    };

    /// <summary>一条指令的上下文：元数据操作数，以及“指令涉及的类型”。</summary>
    private sealed class Context
    {
        public required Instruction Instruction;
        public MethodShape? Method;
        public FieldShape? Field;
        public TypeShape? Type;
        public TypeShape? Subject;
        /// <summary>ldstr 的字面量。</summary>
        public EntityRef? Literal;
        public StackValue[] Operands = [];
        public Term?[] Steps = [];
        public BlockId Block;
        /// <summary>这条指令已经产生的“结果未规定”的个数：任意值按产生的位置区分（设计 7.2）。</summary>
        public int Unspecified;
    }

    /// <summary>应用一条指令。返回真表示块已经终结。</summary>
    private bool Apply(BlockId block, State state, Instruction instruction)
    {
        var opcode = instruction.Opcode;
        if (opcode.Flow == FlowKind.Prefix)
            throw new ExpansionException("前缀指令不在首批范围内", opcode.Name, instruction.Offset);
        var candidates = OperationCatalog.ForInstruction(opcode.Canonical).ToList();
        if (candidates.Count == 0)
            throw new ExpansionException("目录里没有这条指令", opcode.Canonical, instruction.Offset);

        var context = new Context { Instruction = instruction, Block = block };
        int token = unchecked((int)instruction.Operand);
        switch (opcode.Operand)
        {
            case OperandKind.Method: context.Method = metadata.Method(tokens.Method(token)); context.Subject = context.Method.Return; break;
            case OperandKind.Field: context.Field = metadata.Field(tokens.Field(token)); context.Subject = context.Field.Type; break;
            case OperandKind.Type: context.Type = metadata.Type(tokens.Type(token)); break;
            case OperandKind.String: context.Literal = tokens.String(token); break;
        }
        if (opcode.Canonical is "ldarg" or "starg")
            context.Subject = Indexed(body.Method.Parameters, instruction, "形参");
        else if (opcode.Canonical is "ldloc" or "stloc")
            context.Subject = Indexed(body.Locals, instruction, "局部变量");
        else if (opcode.Canonical == "ret")
            context.Subject = body.Method.Return;

        // 适用的目录项必须恰好一个。
        CatalogEntry? chosen = null;
        foreach (var candidate in candidates)
        {
            if (!Holds(candidate.Condition, context)) continue;
            // 构造函数的 this 由模板给出，不在栈上。
            int skip = candidate.Constructs ? 1 : 0;
            int count = candidate.OperandsFromSignature ? context.Method!.Parameters.Length - skip : candidate.Operands.Length;
            if (state.Stack.Count < count) continue;
            bool fits = true;
            for (int i = 0; i < count && fits; i++)
            {
                var kind = state.Stack[state.Stack.Count - count + i].Kind;
                if (candidate.OperandsFromSignature) fits = kind == context.Method!.Parameters[skip + i].Kind;
                else fits = Matches(candidate.Operands[i], kind, context) && (!candidate.SameKind || kind == state.Stack[^count].Kind)
                    // 值类型的值只能核对大小：与要存入的类型同宽。
                    && (candidate.Operands[i] != StackClass.Assignable || kind != StackKind.Value
                        || state.Stack[state.Stack.Count - count + i].Value.Width == context.Subject!.StorageBits);
            }
            if (!fits) continue;
            if (chosen is not null)
                throw new InvalidOperationException($"目录项 {chosen.Id} 与 {candidate.Id} 的适用条件重叠");
            chosen = candidate;
        }
        if (chosen is null)
        {
            string stack = string.Join(", ", state.Stack.TakeLast(3).Select(v => v.Kind));
            throw new ExpansionException("目录里没有适用的变体", $"{opcode.Canonical}，栈顶 [{stack}]", instruction.Offset);
        }
        used.Add((instruction.Offset, chosen.Id));

        int operandCount = chosen.OperandsFromSignature ? context.Method!.Parameters.Length - (chosen.Constructs ? 1 : 0) : chosen.Operands.Length;
        context.Operands = [.. state.Stack.Skip(state.Stack.Count - operandCount)];
        state.Stack.RemoveRange(state.Stack.Count - operandCount, operandCount);
        if (chosen.ImpliedBits > 0) context.Subject = new TypeShape(StackKind.Int32, chosen.ImpliedBits, true, default);
        if (chosen.ImpliedReference) context.Subject = new TypeShape(StackKind.Object, pointerBits, false, default);
        context.Steps = new Term?[chosen.Steps.Length];

        for (int s = 0; s < chosen.Steps.Length; s++)
        {
            var step = chosen.Steps[s];
            var values = new Term[step.Values.Length];
            for (int i = 0; i < values.Length; i++) values[i] = Value(step.Values[i], context, state);
            switch (step.Kind)
            {
                case StepKind.ThrowIf:
                    Emit(block, new(EffectKind.ThrowIf, [values[0]], [], chosen.Id, instruction.Offset) { Exception = step.Exception });
                    break;
                case StepKind.Read:
                {
                    int width = context.Subject?.StorageBits ?? throw Missing(instruction, "被读位置的类型");
                    context.Steps[s] = Emit(block, new(EffectKind.Read, [.. values], [width], chosen.Id, instruction.Offset)
                        { Location = step.Location, Entity = context.Field?.Entity, Owner = context.Field?.DeclaringType })[0];
                    break;
                }
                case StepKind.Write:
                    Emit(block, new(EffectKind.Write, [.. values], [], chosen.Id, instruction.Offset)
                        { Location = step.Location, Entity = context.Field?.Entity, Owner = context.Field?.DeclaringType });
                    break;
                case StepKind.Call:
                {
                    var method = context.Method ?? throw Missing(instruction, "被调方法");
                    // 模板写出的值在前（间接调用的目标，或构造函数的 this），栈上的实参对应其后的形参。
                    var operands = new List<Term>(values);
                    int first = method.Parameters.Length - context.Operands.Length;
                    for (int i = 0; i < context.Operands.Length; i++) operands.Add(Store(context.Operands[i].Value, method.Parameters[first + i], instruction));
                    ImmutableArray<int> results = method.Return is { } returned ? [returned.StorageBits] : [];
                    var produced = Emit(block, new(EffectKind.Call, [.. operands], results, chosen.Id, instruction.Offset)
                        { Entity = method.Entity, Indirect = step.Indirect, Signature = method });
                    if (produced.Length > 0) context.Steps[s] = produced[0];
                    break;
                }
                case StepKind.RuntimeCall:
                    context.Steps[s] = Emit(block, new(EffectKind.RuntimeCall, [.. values], [pointerBits], chosen.Id, instruction.Offset)
                        { Function = step.Function, Entity = context.Method?.Entity })[0];
                    break;
                case StepKind.ClassInitialize:
                {
                    // 被初始化的类：字段所属的类，或被调方法所属的类。
                    if (context.Field is null && context.Method is null) throw Missing(instruction, "字段或方法");
                    Emit(block, new(EffectKind.ClassInitialize, [], [], chosen.Id, instruction.Offset)
                    {
                        Entity = context.Field?.DeclaringType ?? context.Method!.DeclaringType,
                        Precise = context.Field?.PreciseInitialization ?? context.Method!.PreciseInitialization,
                    });
                    break;
                }
                case StepKind.NewObject:
                {
                    // 被分配的类是构造函数所属的类；类初始化分量的时机取自元数据。
                    var method = context.Method ?? throw Missing(instruction, "构造函数");
                    context.Steps[s] = Emit(block, new(EffectKind.NewObject, [], [pointerBits], chosen.Id, instruction.Offset)
                        { Entity = method.DeclaringType, Precise = method.HasInitializer && method.PreciseInitialization })[0];
                    break;
                }
                case StepKind.Throw:
                    Emit(block, new(EffectKind.Throw, [values[0]], [], chosen.Id, instruction.Offset));
                    flow.Terminate(block, Terminator.Single(Exit.NoReturn));
                    return true;
                case StepKind.Require:
                    Emit(block, new(EffectKind.Require, [values[0]], [], chosen.Id, instruction.Offset));
                    break;
                case StepKind.StoreLocal: state.Locals[instruction.Operand] = values[0]; break;
                case StepKind.StoreArgument: state.Arguments[instruction.Operand] = values[0]; break;
                case StepKind.Jump:
                    flow.Terminate(block, Terminator.Single(Edge((int)instruction.Operand, state, instruction)));
                    return true;
                case StepKind.Branch:
                    flow.Terminate(block, Terminator.Branch(values[0], Edge((int)instruction.Operand, state, instruction),
                        Edge(Fallthrough(instruction), state, instruction)));
                    return true;
                case StepKind.Switch:
                {
                    var exits = ImmutableArray.CreateBuilder<Exit>(instruction.Targets.Length + 1);
                    foreach (int target in instruction.Targets) exits.Add(Edge(target, state, instruction));
                    exits.Add(Edge(Fallthrough(instruction), state, instruction));
                    flow.Terminate(block, Terminator.Switch(values[0], exits.MoveToImmutable()));
                    return true;
                }
                case StepKind.Return:
                    if (state.Stack.Count != 0) throw new ExpansionException("返回时栈不为空", "", instruction.Offset);
                    flow.Terminate(block, Terminator.Single(Exit.Return(values)));
                    return true;
            }
        }

        if (chosen.Result is not null && !(chosen.OperandsFromSignature && !chosen.Constructs && context.Method!.Return is null))
        {
            var value = Value(chosen.Result, context, state);
            var kind = chosen.ResultKind switch
            {
                ResultKind.Int32 => StackKind.Int32,
                ResultKind.Int64 => StackKind.Int64,
                ResultKind.NativeInt => StackKind.NativeInt,
                ResultKind.Float32 => StackKind.Float32,
                ResultKind.Float64 => StackKind.Float64,
                ResultKind.Object => StackKind.Object,
                ResultKind.ByRef => StackKind.ByRef,
                ResultKind.SameAsOperand => context.Operands[0].Kind,
                ResultKind.Subject => (context.Subject ?? throw Missing(instruction, "结果的类型")).Kind,
                _ => throw new InvalidOperationException($"目录项 {chosen.Id} 有结果但没有写明类别"),
            };
            if (value.Width != StackBits(kind, value))
                throw new InvalidOperationException($"目录项 {chosen.Id} 的结果是 {value.Width} 位，与类别 {kind} 不符");
            state.Stack.Add(new(value, kind));
        }
        return false;
    }

    private ImmutableArray<Term> Emit(BlockId block, TemplateEffect effect) => flow.Append(block, effect);

    private int Fallthrough(Instruction instruction) =>
        indexAt.ContainsKey(instruction.Next) ? instruction.Next
            : throw new ExpansionException("IL 无法解码", "条件转移之后没有指令", instruction.Offset);

    private static TypeShape Indexed(ImmutableArray<TypeShape> list, Instruction instruction, string what) =>
        instruction.Operand >= 0 && instruction.Operand < list.Length ? list[(int)instruction.Operand]
            : throw new ExpansionException("IL 无法解码", $"{what}序号 {instruction.Operand} 越界", instruction.Offset);

    private static ExpansionException Missing(Instruction instruction, string what) =>
        new("目录项与指令不相称", $"{instruction.Opcode.Name} 没有{what}", instruction.Offset);

    private static bool Holds(VariantCondition condition, Context context) => condition switch
    {
        VariantCondition.None => true,
        VariantCondition.StaticWithoutInitializer => context.Field is { IsStatic: true, HasInitializer: false },
        VariantCondition.StaticWithInitializer => context.Field is { IsStatic: true, HasInitializer: true },
        VariantCondition.InstanceField => context.Field is { IsStatic: false },
        VariantCondition.ReturnsVoid => context.Subject is null,
        VariantCondition.ReturnsValue => context.Subject is not null,
        VariantCondition.StaticMethod => context.Method is { Dispatch: VariantCondition.StaticMethod, HasInitializer: false },
        VariantCondition.StaticMethodWithInitializer => context.Method is { Dispatch: VariantCondition.StaticMethod, HasInitializer: true },
        VariantCondition.ReferenceTypeConstructor => context.Method is { HasThis: true, Parameters: [{ Kind: StackKind.Object }, ..] },
        _ => context.Method?.Dispatch == condition,
    };

    private Term Widen(Term value, TypeShape type)
    {
        if (type.Kind != StackKind.Int32 || value.Width >= 32) return value;
        return type.Signed ? terms.SignExtend(value, 32) : terms.ZeroExtend(value, 32);
    }

    /// <summary>
    /// 把栈上的值转成类型的存储表示（ECMA-335 III.1.6 的隐式转换）：浮点按存储格式转换（I.12.1.3、III.3.63），
    /// 整数截到存储位宽，本机整数接受 int32 时按类型的符号扩展；其余不变。
    /// </summary>
    private Term Store(Term value, TypeShape type, Instruction instruction)
    {
        int bits = type.StorageBits;
        if (value.Width == bits) return value;
        if (type.Kind is StackKind.Float32 or StackKind.Float64) return terms.Operation(Op.FConvert, bits, value);
        if (type.Kind == StackKind.Int32 && value.Width > bits) return terms.Truncate(value, bits);
        if (type.Kind == StackKind.NativeInt && value.Width < bits) return type.Signed ? terms.SignExtend(value, bits) : terms.ZeroExtend(value, bits);
        throw new ExpansionException("类型不相容", $"{value.Width} 位的值不能存入 {bits} 位的 {type.Kind}", instruction.Offset);
    }

    private Term Resized(Term amount, int width) =>
        amount.Width == width ? amount : amount.Width > width ? terms.Truncate(amount, width) : terms.ZeroExtend(amount, width);

    private Term Value(TemplateValue template, Context context, State state)
    {
        var instruction = context.Instruction;
        var a = template.Arguments;
        Term X(int i) => Value(a[i], context, state);
        switch (template.Op)
        {
            case ValueOp.Operand: return context.Operands[template.A].Value;
            case ValueOp.Step:
                return context.Steps[template.A] ?? throw new InvalidOperationException($"模板引用了没有结果的第 {template.A} 步");
            case ValueOp.Immediate: return terms.Constant(instruction.Operand, template.A);
            case ValueOp.Argument: return state.Arguments[instruction.Operand];
            case ValueOp.Local: return state.Locals[instruction.Operand];
            case ValueOp.Null: return terms.Zero(pointerBits);
            case ValueOp.Literal: return terms.Entity(context.Literal ?? throw Missing(instruction, "字面量"), pointerBits);
            // 结果未规定：在产生它的这一步取得身份（图，块，指令偏移，第几个）。
            case ValueOp.Undefined: return terms.Arbitrary(flow.Graph, context.Block, instruction.Offset, 0, context.Unspecified++, X(0).Width);
            case ValueOp.Add: return terms.Add(X(0), X(1));
            case ValueOp.Sub: return terms.Sub(X(0), X(1));
            case ValueOp.Mul: return terms.Mul(X(0), X(1));
            case ValueOp.SignedDivide: return terms.Divide(Op.SDiv, X(0), X(1));
            case ValueOp.SignedRemainder: return terms.Divide(Op.SRem, X(0), X(1));
            case ValueOp.And: return terms.And(X(0), X(1));
            case ValueOp.Xor: return terms.Xor(X(0), X(1));
            case ValueOp.Negate: return terms.Neg(X(0));
            case ValueOp.ShiftLeft: { var x = X(0); return terms.Shl(x, Resized(X(1), x.Width)); }
            case ValueOp.ShiftRightSigned: { var x = X(0); return terms.AShr(x, Resized(X(1), x.Width)); }
            case ValueOp.ShiftRightUnsigned: { var x = X(0); return terms.LShr(x, Resized(X(1), x.Width)); }
            case ValueOp.Equal: return terms.Eq(X(0), X(1));
            case ValueOp.SignedLess: return terms.Slt(X(0), X(1));
            case ValueOp.UnsignedLess: return terms.Ult(X(0), X(1));
            case ValueOp.IsZero: { var x = X(0); return terms.Eq(x, Zeros(x.Width)); }
            case ValueOp.IsMinimum: { var x = X(0); return terms.Eq(x, terms.Bits(UInt128.One << (x.Width - 1), x.Width)); }
            case ValueOp.IsAllOnes: { var x = X(0); return terms.Eq(x, terms.Bits(UInt128.MaxValue, x.Width)); }
            case ValueOp.ShiftInRange: { var amount = X(0); return terms.Ult(amount, terms.Constant(X(1).Width, amount.Width)); }
            case ValueOp.Both: return terms.And(X(0), X(1));
            case ValueOp.Not: return terms.Not(X(0));
            case ValueOp.Flag: return terms.ZeroExtend(X(0), 32);
            case ValueOp.Resize:
            {
                var x = X(0);
                if (template.A >= template.B || x.Width <= template.A) return x.Width > template.B ? terms.Truncate(x, template.B) : x;
                var low = terms.Truncate(x, template.A);
                return template.C != 0 ? terms.SignExtend(low, template.B) : terms.ZeroExtend(low, template.B);
            }
            case ValueOp.FromStorage: return Widen(X(0), context.Subject ?? throw Missing(instruction, "涉及的类型"));
            case ValueOp.ToStorage: return Store(X(0), context.Subject ?? throw Missing(instruction, "涉及的类型"), instruction);
            case ValueOp.FieldOfValue:
            {
                var field = context.Field ?? throw Missing(instruction, "字段");
                var x = X(0);
                if (field.OffsetBits < 0 || field.OffsetBits + field.Type.StorageBits > x.Width)
                    throw new ExpansionException("值类型的布局未知", $"字段 {field.Entity}", instruction.Offset);
                return terms.Slice(x, field.OffsetBits, field.Type.StorageBits);
            }
            case ValueOp.FloatAdd: { var x = X(0); return terms.Operation(Op.FAdd, x.Width, x, X(1)); }
            case ValueOp.FloatSubtract: { var x = X(0); return terms.Operation(Op.FSub, x.Width, x, X(1)); }
            case ValueOp.FloatMultiply: { var x = X(0); return terms.Operation(Op.FMul, x.Width, x, X(1)); }
            case ValueOp.FloatDivide: { var x = X(0); return terms.Operation(Op.FDiv, x.Width, x, X(1)); }
            case ValueOp.FloatToDouble: { var x = X(0); return x.Width == 64 ? x : terms.Operation(Op.FConvert, 64, x); }
            case ValueOp.SignedToDouble: return terms.Operation(Op.SToF, 64, X(0));
            case ValueOp.UnsignedToDouble: return terms.Operation(Op.UToF, 64, X(0));
            case ValueOp.Select: return terms.Select(X(0), X(1), X(2));
            case ValueOp.Named:
            {
                var arguments = new List<Term>(a.Length + 1);
                for (int i = 0; i < a.Length; i++) arguments.Add(X(i));
                // 带实体操作数的函数：实体取自指令的元数据操作数。
                EntityRef? entity = template.Function switch
                {
                    // 类没有由模板写出时取自指令的类型操作数。
                    RuntimeFunction.IsInstance when a.Length == 1 => (context.Type ?? throw Missing(instruction, "类型")).Entity,
                    RuntimeFunction.FieldAddress => (context.Field ?? throw Missing(instruction, "字段")).Entity,
                    RuntimeFunction.VirtualInvokeData => (context.Method ?? throw Missing(instruction, "方法")).Entity,
                    _ => null,
                };
                if (entity is { } operand) arguments.Add(terms.Entity(operand, pointerBits));
                int width = template.Function is RuntimeFunction.ArrayLength or RuntimeFunction.CastDoubleToInt32 ? 32 : pointerBits;
                return terms.Attribute(new AttributeId((int)template.Function), width, System.Runtime.InteropServices.CollectionsMarshal.AsSpan(arguments));
            }
            default:
                throw new InvalidOperationException($"模板里的值 {template.Op} 没有求值规则");
        }
    }
}
