using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

[ShapeModel("访问器认回", Basis = "F9：访问器方法体由执行对照单独验证并以方法体指纹登记；认回的调用与原生内联的字段访问在两侧的可观察事件相同")]
internal sealed partial class CilInterpreter
{
    private IReadOnlyDictionary<Instruction, FieldAccessor> accessorSites = new Dictionary<Instruction, FieldAccessor>();
    public Dictionary<MethodDef, MethodDefinition> TransparentAccessors { get; } = [];
    public int NullAccessorCalls { get; private set; }
    public int AccessorCalls { get; private set; }

    private IReadOnlyDictionary<Instruction, MethodRef> inlineSites = new Dictionary<Instruction, MethodRef>();
    private readonly Dictionary<MethodDef, MethodDefinition> transparentInline = [];

    public void SetAccessors(BodyEmitter emitter, Skeleton skeleton)
    {
        accessorSites = emitter.AccessorCalls;
        TransparentAccessors.Clear();
        // 集合只取最终写出的认回点；原有普通调用即使指向同一个方法也不变透明。
        foreach (var accessor in accessorSites.Values)
            TransparentAccessors[accessor.Method.Method] = skeleton.Method(accessor.Method.Method);
        inlineSites = emitter.InlineCalls;
        transparentInline.Clear();
        foreach (var method in inlineSites.Values) transparentInline[method.Method] = skeleton.Method(method.Method);
    }

    public bool IsAccessorCall(Instruction instruction) => accessorSites.ContainsKey(instruction);

    private StackValue? InvokeAt(CilSide side, Instruction instruction, MethodRef callee, StackValue[] values)
    {
        // 内联的 builder.Start<TStateMachine>(ref stateMachine)：二进制中具体类型的 Start<T> 实例都只尾调用 TStateMachine.MoveNext(stateMachine)（start-census），
        // 原生代码在此内联了它，所以这里是一次对 MoveNext 的调用。只用于认回的调用点；真正调用 Start<T> 的地方仍是对它的调用。
        if (inlineSites.ContainsKey(instruction) && StartCensus.IsStart(callee) && callee.MethodArguments is [DefinitionRef machine]
            && machine.Definition.Methods.FirstOrDefault(m => m is { Name: "MoveNext", IsStatic: false, Parameters.Count: 0 }) is { } moveNext)
            return Invoke(side, new MethodRef(moveNext, machine.Arguments, []), [values[1]]);
        // 内联的 task.GetAwaiter()（UniTask<T>）：二进制中它的全部实例的结果都是 *this 的逐字节拷贝（awaiter-census），Awaiter<T> 与 UniTask<T> 同布局。
        if (inlineSites.ContainsKey(instruction) && AwaiterCensus.IsGetAwaiter(callee))
            return ReadValue(side, callee.Method.ReturnType.Substitute(callee.TypeArguments, []), values[0].Bits);
        // 内联的 awaiter.IsCompleted（UniTask<T>.Awaiter）：二进制中它的全部实例都是 source == null || source.GetStatus(token) != Pending（awaiter-census）。
        if (inlineSites.ContainsKey(instruction) && GenericInline.IsModeled(callee.Method))
            return callee.Method.Name == "GetResult" ? AwaiterGetResult(side, callee, values[0]) : AwaiterIsCompleted(side, callee, values[0]);
        // 内联认回的调用点：原生代码在此内联了被调方法，按被调方法（已独立 verified）的方法体透明执行，不产生调用与返回事件。
        if (inlineSites.ContainsKey(instruction) && transparentInline.TryGetValue(callee.Method, out var inlined))
            return Execute(side, inlined, callee, values, transparent: true);
        if (!IsAccessorCall(instruction)) return Invoke(side, callee, values);
        // 认回的 Array.Empty<T>()：二进制中它的全部实例都只返回 EmptyArray<T>.Value（empty-census），按该静态字段的读取执行（ECMA-335 III.4.15）。
        if (accessorSites[instruction] is { } empty && EmptyArrayCensus.IsEmpty(empty.Method))
        {
            AccessorCalls++;
            side.RunClassConstructor(empty.Field.DeclaringType);
            return ReadValue(side, side.World.FieldType(empty.Field), side.World.StaticAddress(empty.Field));
        }
        if (accessorSites[instruction] is { Method.TypeArguments.Count: > 0 } generic) return GenericAccessor(side, generic, callee, values);
        if (!TransparentAccessors.TryGetValue(callee.Method, out var definition)) throw new Unsupported($"非透明访问器 {callee}");
        AccessorCalls++;
        if (!callee.Method.IsStatic && values[0].Bits == 0) NullAccessorCalls++;
        // ECMA-335 III.3.19/3.57、III.4.10/4.28：call 建立帧，ldfld/stfld 判空，ret 返回到调用者。
        // 只解释已独立 verified 或无原生代码且具有语言定义证据的访问器体；共享当前内存与异常路径，不制造调用或内部返回事件。
        return Execute(side, definition, callee, values, transparent: true);
    }

    /// <summary>
    /// 泛型类型封闭实例上的 getter（F9 泛型访问器）：核对该实例的原生代码就是一条从接收者（x0）读出该字段的指令加 ret，
    /// 偏移取自字段布局（值类型的 this 指向未装箱数据，扣除对象头）。核对通过才按字段读取执行；不读取恢复路径的方法体。
    /// </summary>
    private StackValue GenericAccessor(CilSide side, FieldAccessor accessor, MethodRef callee, StackValue[] values)
    {
        var world = side.World;
        var entry = world.Index.CodeAddress(callee);
        var owner = (DefinitionRef)accessor.Field.DeclaringType;
        var expected = world.FieldOffset(accessor.Field) - (owner.Definition.IsValueType ? RuntimeLayout.ObjectHeaderSize : 0);
        var type = world.FieldType(accessor.Field);
        if (index.Facts.Code.Word(entry) is not { } load || index.Facts.Code.Word(entry + 4) is not { } ret
            || (load & 0x3B000000) != 0x39000000 || ((load >> 22) & 3) == 0 || (load & 31) != 0 || ((load >> 5) & 31) != 0
            || ((load >> 10) & 0xFFF) * (ulong)(1 << (int)(load >> 30)) != (ulong)expected || (1 << (int)(load >> 30)) != world.StorageSize(type)
            || (ret & 0xFFFFFC1F) != 0xD65F0000)
            throw new Unsupported($"泛型访问器 {callee} 的原生代码不是单字段读取");
        AccessorCalls++;
        return ReadValue(side, type, FieldAddress(world, accessor.Field, values[0]));
    }

    /// <summary>awaiter-census 的 IsCompleted 形态：读 this.task.source，非 null 时以 this.task.token 调用 IUniTaskSource.GetStatus（接口分派，与 callvirt 相同）。</summary>
    private StackValue AwaiterIsCompleted(CilSide side, MethodRef callee, StackValue receiver)
    {
        var world = side.World;
        var awaiter = (DefinitionRef)callee.DeclaringType;
        var task = new FieldRef(awaiter.Definition.Fields.Single(f => f.Name == "task" && !f.IsStatic), awaiter);
        var unitask = (DefinitionRef)world.FieldType(task);
        FieldRef Of(string name) => new(unitask.Definition.Fields.Single(f => f.Name == name && !f.IsStatic), unitask);
        // 值类型字段的布局偏移含对象头；this 指向未装箱数据。
        var header = (ulong)RuntimeLayout.ObjectHeaderSize;
        var data = receiver.Bits + (ulong)world.FieldOffset(task) - header;
        var source = ReadValue(side, world.FieldType(Of("source")), data + (ulong)world.FieldOffset(Of("source")) - header);
        if (source.Bits == 0) return StackValue.I4(1);
        var token = ReadValue(side, world.FieldType(Of("token")), data + (ulong)world.FieldOffset(Of("token")) - header);
        var getStatus = index.Facts.Model.Types.Single(t => t.FullName == "Cysharp.Threading.Tasks.IUniTaskSource" && t.GenericParameters.Count == 0).Methods.Single(m => m.Name == "GetStatus");
        var status = Invoke(side, Dispatch(side, source.Bits, new MethodRef(getStatus, [], [])), [source, token]) ?? throw new Unsupported("GetStatus 没有返回值");
        return StackValue.I4(status.Int32 != 0 ? 1 : 0);
    }

    /// <summary>awaiter-census 的 GetResult 形态：this.task.source 为 null 时返回 this.task.result，否则以 this.task.token 调用 IUniTaskSource&lt;T&gt;.GetResult（接口分派）。</summary>
    private StackValue? AwaiterGetResult(CilSide side, MethodRef callee, StackValue receiver)
    {
        var world = side.World;
        var awaiter = (DefinitionRef)callee.DeclaringType;
        var task = new FieldRef(awaiter.Definition.Fields.Single(f => f.Name == "task" && !f.IsStatic), awaiter);
        var unitask = (DefinitionRef)world.FieldType(task);
        FieldRef Of(string name) => new(unitask.Definition.Fields.Single(f => f.Name == name && !f.IsStatic), unitask);
        var header = (ulong)RuntimeLayout.ObjectHeaderSize;
        var data = receiver.Bits + (ulong)world.FieldOffset(task) - header;
        if (!ManagedTypes.IsReferenceType(unitask.Arguments[0]) && world.StorageSize(unitask.Arguments[0]) > GenericInline.ResultLimit)
            throw new Unsupported($"{callee} 的结果超过 GetResult 模型的范围");
        var source = ReadValue(side, world.FieldType(Of("source")), data + (ulong)world.FieldOffset(Of("source")) - header);
        if (source.Bits == 0) return ReadValue(side, world.FieldType(Of("result")), data + (ulong)world.FieldOffset(Of("result")) - header);
        var token = ReadValue(side, world.FieldType(Of("token")), data + (ulong)world.FieldOffset(Of("token")) - header);
        var definition = index.Facts.Model.Types.Single(t => t.FullName == "Cysharp.Threading.Tasks.IUniTaskSource" && t.GenericParameters.Count == 1);
        var getResult = new MethodRef(definition.Methods.Single(m => m.Name == "GetResult"), unitask.Arguments, []);
        return Invoke(side, Dispatch(side, source.Bits, getResult), [source, token]);
    }

    /// <summary>按普查建模的访问器读写的静态字段（Array.Empty&lt;T&gt; 的 EmptyArray&lt;T&gt;.Value）：执行前须与 ldsfld 一样准备。</summary>
    public IEnumerable<FieldRef> IntrinsicStatics(MethodDefinition method) => method.Body.Instructions.Where(IsAccessorCall)
        .Select(i => accessorSites[i]).Where(a => EmptyArrayCensus.IsEmpty(a.Method)).Select(a => a.Field).Distinct();

    public IEnumerable<Instruction> ExpandedInstructions(MethodDefinition method) => method.Body.Instructions.Concat(
        method.Body.Instructions.Where(IsAccessorCall).Select(i => model.Method((MethodReference)i.Operand).Method).Distinct()
            .Where(TransparentAccessors.ContainsKey).SelectMany(m => TransparentAccessors[m].Body.Instructions)).Concat(
        method.Body.Instructions.Where(inlineSites.ContainsKey).Select(i => inlineSites[i].Method).Distinct()
            .Where(transparentInline.ContainsKey).SelectMany(m => transparentInline[m].Body.Instructions));
}

internal static partial class ExecutionCheck
{
    private static Dictionary<MethodDef, FieldAccessor> EvidenceCandidates(string directory, ProgramFacts facts, ManagedTypes types,
        MethodRecoveryResult[] results, Skeleton skeleton)
    {
        var output = new Dictionary<MethodDef, FieldAccessor>();
        var path = Path.Combine(directory, "accessor-candidates.tsv");
        if (!File.Exists(path)) return output;
        var descriptions = File.ReadLines(path).ToHashSet(StringComparer.Ordinal);
        var wanted = descriptions.Select(l => l.Split('\t')).Select(f => (Convert.ToUInt64(f[0], 16), f[1])).ToHashSet();
        var properties = facts.Model.Types.SelectMany(t => t.Properties.SelectMany(p => new[] { (Method: p.Getter, Write: false), (Method: p.Setter, Write: true) }))
            .Where(p => p.Method is not null).ToLookup(p => p.Method!);
        var automatic = AutoPropertyAccessor.Candidates(types);
        foreach (var result in results.Where(r => wanted.Contains((r.Entry, r.Method.ToString()))))
        {
            var accessor = (result.Entry == 0 ? automatic.GetValueOrDefault(result.Method.Method) : null) ?? properties[result.Method.Method].Select(p => result.Body is { } b ? FieldAccessor.Recognize(b, p.Write, types) : null)
                .OfType<FieldAccessor>().SingleOrDefault() ?? automatic.GetValueOrDefault(result.Method.Method) ?? throw new InvalidDataException($"访问器候选不再满足严格形态：{result.Method}");
            if (!descriptions.Contains(AccessorEvidence.Describe(facts, skeleton, accessor)))
                throw new InvalidDataException($"访问器候选 CIL 或原生字节已变：{result.Method}");
            output[result.Method.Method] = accessor;
        }
        if (wanted.Count != output.Count) throw new InvalidDataException("访问器候选必须全部在本次写出集合内");
        return output;
    }
}
