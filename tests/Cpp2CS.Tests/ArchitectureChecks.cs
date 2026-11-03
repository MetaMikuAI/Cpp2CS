using System.Reflection;
using Cpp2CS.Calls;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;
using Cpp2CS.Tests.Execution;
using Cecil = Mono.Cecil;
using Cil = Mono.Cecil.Cil;

namespace Cpp2CS.Tests;

/// <summary>用匹配输入提供类型与运行时定义；证明边界使用独立的小型托管方法体。</summary>
internal static class ArchitectureChecks
{
    public static int Run(string binary, string metadata, string cache)
    {
        var facts = FactsBuilder.Build(binary, metadata, options: new RecoveryOptions { FactCacheFile = Path.GetFullPath(cache) });
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var checks = new Assertions();
        Convergence(checks, types);
        Identities(checks, types);
        EntryKinds(checks, facts, types);
        Templates(checks, types);
        NestedEnumStack(checks);
        InterfaceSlots(checks, types);
        RepresentationCopies(checks, facts, types);
        LowBitArithmetic(checks);
        Barriers(checks, types);
        PhiLoadWidths(checks, facts);
        FloatingOperands(checks, facts, types);
        Verdicts(checks);
        return checks.Finish("架构边界");
    }

    private static void PhiLoadWidths(Assertions check, ProgramFacts facts)
    {
        foreach (var pass in new[] { "static", "address", "guarded" })
        {
            var first = new Block(0);
            var second = new Block(4);
            var merge = new Block(8);
            var pointer = new Variable(Storage.Gpr(0), 1);
            var result = new Variable(Storage.Vec(0), 1);
            first.Statements = [new Jump(0, 8)];
            second.Statements = [new Jump(4, 8)];
            merge.Statements = [new Phi(8, pointer, [new(Storage.Gpr(1), 0), new(Storage.Gpr(2), 0)])];
            if (pass == "guarded")
                merge.Statements.Add(new Call(8, CallKind.Direct, Expr.C(0, 64))
                { Op = new RuntimeOp(OpKind.NullCheck, null), Arguments = [new Use(pointer, 64)] });
            merge.Statements.Add(new Define(12, result, new Load(new Use(pointer, 64), 128)));
            var function = new MachineFunction
            { Entry = 0, Range = new(0, 16, CodeRegion.Managed, default), Blocks = [first, second, merge] };
            MachineFunction.AddEdge(first, merge);
            MachineFunction.AddEdge(second, merge);
            var state = new IdiomState(new IdiomRewriter(facts), function);
            var changed = pass == "static" ? state.StaticFieldPhiLoads() : AddressPhiLoads.Run(function, state.Fresh);
            check.True(changed, $"{pass} 拆分向量读取");
            var reads = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().Where(d => d.Value is Load).ToArray();
            check.True(reads.Length == 2 && reads.All(d => d.Target.Width == 128 && d.Value.Width == 128), $"{pass} 入边保留完整向量");
            var phi = merge.Statements.OfType<Phi>().Single(p => p.Target.Width == 128);
            check.True(phi.Sources.All(s => s.Width == phi.Target.Width), $"{pass} 合流来源位宽一致");
        }
    }

    private static void FloatingOperands(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var owner = Type("Numeric", 20);
        var definition = Method(owner, "Convert", 20);
        definition.Parameters = [new ParameterDef("value", types.Single, 0, null, false)];
        var method = new MethodRef(definition, [], []);
        var structure = new DefinitionRef(new TypeDef { Index = 22, Name = "FloatStorage", Namespace = "Tests", Assembly = "Tests.dll",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        EmissionProblem? Validate(ManagedValue value)
        {
            var body = new ManagedBody(method, [new(0, [new ManagedReturn(0, value)])]);
            return new BodyValidation(types, EmissionPolicy.Recovered, method).Check(body, true, out _);
        }
        var unresolved = new ArgumentValue(0, structure, 0);
        check.True(Validate(new ConversionValue(ConvKind.FloatToFloat, unresolved, types.Double, 64)) is
            { Kind: EmissionProblemKind.Unsupported, Address: 0 }, "未解析结构体的浮点转换在写出前报错");
        var wrongScalar = new ArgumentValue(0, structure, 32);
        check.True(Validate(new UnaryValue(UnOp.FNeg, wrongScalar, types.Single, 32)) is not null, "相同位宽不能把结构体当作浮点标量");
        check.True(Validate(new ComparisonValue(Cond.FEq, wrongScalar, wrongScalar, types.Boolean)) is not null, "浮点比较检查隐含位重解释");
        check.True(Validate(new ConversionValue(ConvKind.FloatToFloat, new ArgumentValue(0, types.Int32, 32), types.Double, 64)) is null,
            "同宽整数可经核心库位重解释后转换浮点");
        check.True(Validate(new ConversionValue(ConvKind.FloatToFloat, new ArgumentValue(0, types.Single, 32), types.Double, 64)) is null,
            "合法浮点扩展保留");
        var integer = new ArgumentValue(0, types.UInt64, 64);
        check.True(Validate(new BinaryValue(BinOp.MulHighU, integer, integer, types.UInt64, 64)) is
            { Kind: EmissionProblemKind.Unsupported }, "未实现的高位乘法在写出前报错");
        check.True(Validate(new UnaryValue(UnOp.Clz, integer, types.UInt64, 64)) is
            { Kind: EmissionProblemKind.Unsupported }, "未实现的一元运算不能被写成取负");
        check.True(Validate(new UnaryValue(UnOp.Neg, integer, types.UInt64, 64)) is null, "合法一元运算保留");
        check.True(Validate(new ArgumentValue(1, types.Single, 32)) is not null, "不存在的参数在写出前报错");
        var staticDefinition = new MethodDef
        {
            Index = 21, Owner = owner, Name = "Static", Token = 0, Attributes = MethodAttributes.Public | MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1,
        };
        var staticMethod = new MethodRef(staticDefinition, [], []);
        var invalidThis = new ManagedBody(staticMethod, [new(0, [new ManagedReturn(0, new ArgumentValue(-1, types.Object, 64))])]);
        check.True(new BodyValidation(types, EmissionPolicy.Partial, staticMethod).Check(invalidThis, true, out _) is
            { Kind: EmissionProblemKind.Unsupported }, "静态方法的部分恢复体不能引用 this");
    }

    private static void Convergence(Assertions check, ManagedTypes types)
    {
        var phi = new PhiSym(new Block(0), new object(), 32);
        var solution = new TypeSolution();
        check.Equal(TypeSolveState.Changed, solution.Accept(new() { [phi] = types.Int32 }), "第一次类型解");
        check.Equal(TypeSolveState.Stable, solution.Accept(new() { [phi] = types.Int32 }), "相同类型解收敛");
        check.Equal(TypeSolveState.Changed, solution.Accept(new() { [phi] = types.Int64 }), "类型变化继续求解");
        check.Equal(TypeSolveState.Cycle, solution.Accept(new() { [phi] = types.Int32 }), "类型循环不能当成稳定");
        var growing = new TypeSolution();
        var state = new Dictionary<PhiSym, TypeRef?>();
        TypeSolveState result = default;
        for (var i = 0; i < 65; i++)
        {
            state[new PhiSym(new Block((ulong)i), new object(), 32)] = types.Int32;
            result = growing.Accept(state);
            if (i == 3) check.Equal(TypeSolveState.Changed, result, "超过两轮仍继续求解");
        }
        check.Equal(TypeSolveState.BudgetExceeded, result, "预算耗尽不能当成收敛");
    }

    private static void Identities(Assertions check, ManagedTypes types)
    {
        var owner = Type("Generic", 1);
        owner.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        var definition = Method(owner, ".ctor", 1);
        var reference = new GenericParameterRef("T", false, 0) { Binding = new(NativeBindingKind.Reference, types.Object, 1) };
        var scalar = reference with { Binding = new(NativeBindingKind.Scalar, types.Int32, 1) };
        var a = new MethodRef(definition, [reference], []);
        var b = new MethodRef(definition, [scalar], []);
        check.Equal(a, b, "托管泛型身份不包含原生布局");
        check.True(new MethodRequest(a, 1) != new MethodRequest(b, 1), "分析缓存区分原生布局");
        var entries = new NativeMethodEntry[]
        {
            new(new(definition, [types.Int32], []), 1),
            new(new(definition, [types.String], []), 3),
            new(new(definition, [types.Object], []), 2),
        };
        check.Equal(entries[2], MethodEntries.SelectDefinition(entries), "定义选择引用共享见证");
        check.Equal(MethodEntries.SelectDefinition(entries), MethodEntries.SelectDefinition(entries.Reverse()), "定义选择不受枚举顺序影响");
        var local = new LocalValue(new Variable(Storage.Temp(1), 1), types.Object, 64);
        var rootMethod = new MethodRef(Method(Type("Caller", 2), "Run", 2), [], []);
        var edge = new ManagedEdge(4, [new(local, new NewObjectValue(entries[0].Instance, []) { Transparent = true })]);
        var body = new ManagedBody(rootMethod, [new(0, [new ManagedJump(0, edge)]), new(4, [new ManagedReturn(4, null)])]);
        var root = new MethodRecoveryResult(rootMethod, 0, body, []);
        var dependencies = new List<MethodRecoveryResult>();
        var provider = new MissingDefinitions();
        DependencyClosure.Complete([root], dependencies, new() { [rootMethod.Method] = root }, provider);
        check.Equal(definition, provider.Requests.Single(), "边复制中的实例依赖转为定义请求");
        var problems = new Dictionary<ManagedBody, EmissionProblem>();
        DependencyClosure.Validate([root, .. dependencies], problems);
        check.True(problems.ContainsKey(body), "未写出的透明依赖阻止调用方发布");
    }

    private static void Templates(Assertions check, ManagedTypes types)
    {
        var owner = Type("Storage", 10);
        var ownerRef = new DefinitionRef(owner, []);
        var first = new FieldDef { Index = 10, Owner = owner, Name = "first", Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 16 };
        var second = new FieldDef { Index = 11, Owner = owner, Name = "second", Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 20 };
        owner.Fields = [first, second];
        var definition = Method(owner, "Set", 10);
        definition.Parameters = [new ParameterDef("value", types.Int32, 0, null, false)];
        owner.Methods = [definition];
        var method = new MethodRef(definition, [], []);
        var self = new ArgumentValue(-1, ownerRef, 64);
        FieldValue Field(ManagedValue receiver, FieldDef field) => new(receiver, new FieldRef(field, ownerRef), types.Int32, 32);
        var input = new ArgumentValue(0, types.Int32, 32);
        var template = new ManagedBody(method, [new(0, [new ManagedStore(0, Field(self, first), input),
            new ManagedStore(4, Field(self, second), input), new ManagedReturn(8, null)])]);
        MethodRecoveryResult? Summary(MethodRef requested) => requested.Method == definition ? new(method, 0, template, []) : null;
        var caller = new MethodRef(Method(Type("Consumer", 11), "Write", 11), [], []);
        var receiver = new ArgumentValue(0, ownerRef, 64);
        var value = new ArgumentValue(1, types.Int32, 32);
        ManagedBody Body(ManagedValue last) => new(caller, [new(0,
        [
            new ManagedStore(0, Field(receiver, first) with { Pending = (0, "待证字段") }, value),
            new ManagedStore(4, Field(receiver, second) with { Pending = (4, "待证字段") }, last),
            new ManagedReturn(8, null),
        ])]);
        var fields = new FieldAccessModel(types, caller, Summary);
        var recovery = new TemplateRecovery(types, caller, Summary, fields);
        var success = recovery.Run(Body(value), new Dictionary<Variable, PendingConstruction>(), 0);
        check.Equal(0, success.Holes.Count, "两次字段写入的模板证明成功");
        check.True(success.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined && c.Invocation.Method == method), "证明区域被替换成调用");
        var failure = recovery.Run(Body(new ConstantValue(7, types.Int32, 32)), new Dictionary<Variable, PendingConstruction>(), 0);
        check.True(failure.Holes.Count > 0, "写入不一致时保留缺口");
        check.True(!failure.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined), "失败的证明不改写成调用");
        var inaccessible = new TypeDef { Index = 12, Name = "Hidden", Namespace = "Tests", Assembly = "Other.dll", Token = 0,
            Attributes = TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var exposed = new FieldDef { Index = 12, Owner = inaccessible, Name = "value", Type = types.Int32, Offset = 16, Attributes = FieldAttributes.Public };
        check.True(!fields.Accessible(new(exposed, new DefinitionRef(inaccessible, [])), null), "公共字段不能绕过声明类型的权限");
    }

    private static void LowBitArithmetic(Assertions check)
    {
        var syms = new SymTable();
        var a = syms.Arg(0, 32);
        var b = syms.Arg(1, 32);
        foreach (var (operation, expected) in new[] { (BinOp.Add, BinOp.Xor), (BinOp.Sub, BinOp.Xor), (BinOp.Mul, BinOp.And) })
        {
            var low = syms.Slice(syms.Binary(operation, a, b, 32), 0, 1);
            check.True(low is OpSym { Width: 1 } op && op.Op.Binary == expected && op.Args.All(v => v.Width == 1),
                $"{operation} 的低位保留模 2 运算与操作数宽度");
        }
    }

    private static void RepresentationCopies(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        DefinitionRef Structure(string name, int index, int size, bool explicitLayout, params (TypeRef Type, int Offset)[] fields)
        {
            var owner = new TypeDef { Index = index, Name = name, Namespace = "Tests", Assembly = "Tests.dll", Token = 0,
                Attributes = TypeAttributes.Public | (explicitLayout ? TypeAttributes.ExplicitLayout : TypeAttributes.SequentialLayout),
                IsValueType = true, IsEnum = false, Size = size };
            owner.Fields = fields.Select((f, i) => new FieldDef { Index = index * 10 + i, Owner = owner, Name = $"f{i}",
                Type = f.Type, Offset = f.Offset, Attributes = FieldAttributes.Public }).ToArray();
            return new(owner, []);
        }
        var function = new MachineFunction { Entry = 0, Range = new(0, 4, CodeRegion.Managed, default), Blocks = [new(0) { Statements = [new Return(0)] }] };
        var values = ValueModel.Build(function, new EmptyEnvironment());
        var method = new MethodRef(Method(Type("RepresentationConsumer", 60), "Run", 60), [], []);
        var oracle = new TypeOracle(types, facts, method, _ => throw new NotSupportedException(), values);
        var pair = Structure("Pair", 61, 8, false, (types.Single, 0), (types.Single, 4));
        var target = Structure("Coordinates", 62, 8, false, (types.Single, 0), (types.Single, 4));
        check.True(oracle.FieldCopy(pair, target)?.Count == 2, "完整同宽字段可复制到另一值类型");
        var overlap = Structure("Overlap", 63, 8, true, (types.Single, 0), (types.Single, 0));
        check.True(oracle.FieldCopy(pair, overlap) is null, "重叠字段不能冒充逐字段复制");
        var padded = Structure("Padded", 64, 8, false, (types.Single, 0));
        check.True(oracle.FieldCopy(padded, padded) is null, "复制证明不猜测尾部填充");
        var reference = Structure("Reference", 65, 8, false, (types.Object, 0));
        var integer = Structure("Integer", 66, 8, false, (types.Int64, 0));
        check.True(oracle.FieldCopy(reference, integer) is null, "引用与整数不能按字段重解释");
        var union = Structure("FloatUnion", 67, 4, true, (types.Single, 0), (types.Byte, 0));
        check.True(oracle.Inside(union, types.Single) is not null && oracle.Inside(union, types.Byte) is null,
            "显式布局只将覆盖全部位的字段视为整体表示");
    }

    private sealed class EmptyEnvironment : IValueEnvironment
    {
        public Sym? Entry(SymTable syms, Storage storage) => null;
        public Sym? CallResult(SymTable syms, Call call, int index, IReadOnlyList<Sym> arguments) => null;
        public Sym? MetadataRead(SymTable syms, Sym address, int width) => null;
    }

    private static void NestedEnumStack(Assertions check)
    {
        using var module = Cecil.ModuleDefinition.CreateModule("EnumStack", Cecil.ModuleKind.Dll);
        var owner = new Cecil.TypeDefinition("Tests", "Container`1", Cecil.TypeAttributes.Public, module.TypeSystem.Object);
        owner.GenericParameters.Add(new Cecil.GenericParameter("T", owner));
        module.Types.Add(owner);
        var enumeration = new Cecil.TypeDefinition("", "State", Cecil.TypeAttributes.NestedPublic | Cecil.TypeAttributes.Sealed,
            new Cecil.TypeReference("System", "Enum", module, module.TypeSystem.CoreLibrary));
        enumeration.GenericParameters.Add(new Cecil.GenericParameter("T", enumeration));
        enumeration.Fields.Add(new Cecil.FieldDefinition("value__", Cecil.FieldAttributes.Public | Cecil.FieldAttributes.SpecialName | Cecil.FieldAttributes.RTSpecialName, module.TypeSystem.Int32));
        owner.NestedTypes.Add(enumeration);
        var instance = new Cecil.GenericInstanceType(enumeration);
        instance.GenericArguments.Add(module.TypeSystem.Int32);
        var method = new Cecil.MethodDefinition("Read", Cecil.MethodAttributes.Public | Cecil.MethodAttributes.Static, instance);
        owner.Methods.Add(method);
        method.Body.Instructions.Add(Cil.Instruction.Create(Cil.OpCodes.Ldc_I4_0));
        method.Body.Instructions.Add(Cil.Instruction.Create(Cil.OpCodes.Ret));
        check.True(CilStackTypes.Check(method, method.Body) is null, "泛型声明中的嵌套枚举按底层整数检查栈");
        method.Body.Instructions[0] = Cil.Instruction.Create(Cil.OpCodes.Ldc_I8, 0L);
        check.True(CilStackTypes.Check(method, method.Body) is not null, "嵌套枚举仍拒绝错误位宽的返回值");
    }

    private static void InterfaceSlots(Assertions check, ManagedTypes types)
    {
        var owner = new TypeDef { Index = 50, Name = "ISignal", Namespace = "Tests", Assembly = "Tests.dll", Token = 0,
            Attributes = TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract, IsValueType = false, IsEnum = false };
        var method = new MethodDef { Index = 50, Owner = owner, Name = "Notify", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Abstract | MethodAttributes.Virtual, ImplAttributes = 0, Slot = 0 };
        owner.Methods = [method];
        var reference = new DefinitionRef(owner, []);
        check.Equal(Cpp2CS.Recovery.Calls.DispatchResolution.VirtualSlot(types.Object, 0, types)!,
            Cpp2CS.Recovery.Calls.DispatchResolution.VirtualSlot(reference, 0, types)!, "接口引用上的对象虚表槽解析到 Object");
        check.Equal(method, Cpp2CS.Recovery.Calls.DispatchResolution.Slot(reference, 0, true)!.Method,
            "interface offset 分派继续使用接口自身槽号");
    }

    private static void EntryKinds(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var entries = new MethodEntries(facts, types);
        var thunks = facts.Registrations.Entries.Where(e => e.Kind == EntryKind.AdjustorThunk
            && e.Method is { Method.Address: not 0 } && e.Address != e.Method.Method.Address).ToArray();
        check.True(thunks.Length > 0, "输入包含可检查的值类型调整桩");
        check.True(thunks.All(e => entries.Of(e.Method!) == e.Method!.Method.Address), "普通方法索引始终指向本体，不受调整桩地址影响");
        var generic = facts.Registrations.Entries.Where(e => e.Kind == EntryKind.GenericMethod && e.Method is not null)
            .GroupBy(e => e.Method!).ToDictionary(g => g.Key, g => g.Select(e => e.Address).ToHashSet());
        check.True(entries.Definitions.Where(e => e.Instance.Method.Address == 0)
            .All(e => generic.TryGetValue(e.Instance, out var bodies) && bodies.Contains(e.Address)), "泛型定义见证来自方法本体注册");
    }

    private static void Barriers(Assertions check, ManagedTypes types)
    {
        var context = new BarrierContext(types);
        check.True(RuntimeOps.Of(OpKind.MemoryBarrier)!.Lower!(context, out var terminal), "内存屏障可下降");
        check.True(terminal is null && context.Statements is [ManagedCall { Invocation.Method.Method.Name: "MemoryBarrier" }], "内存屏障保留为托管调用");
        context.Statements.Clear();
        check.True(RuntimeOps.Of(OpKind.WriteBarrier)!.Lower!(context, out _) && context.Statements.Count == 0, "GC 写屏障由托管存储承担");
    }

    private static void Verdicts(Assertions check)
    {
        check.Equal(ExecutionVerdict.Partial, ExecutionVerdicts.Classify(32, 30, 0), "部分种子通过不能称为完整验证");
        check.Equal(3, ExecutionVerdicts.ExitCode([]), "空清单不能成功");
        check.Equal(3, ExecutionVerdicts.ExitCode([ExecutionVerdict.NotWritten]), "没有写出不能成功");
        check.Equal(3, ExecutionVerdicts.ExitCode([ExecutionVerdict.Verified, ExecutionVerdict.NotCheckable]), "不支持的用例使验证不完整");
        check.Equal(1, ExecutionVerdicts.ExitCode([ExecutionVerdict.Mismatch, ExecutionVerdict.Partial]), "差异优先报告失败");
        check.Equal(0, ExecutionVerdicts.ExitCode([ExecutionVerdict.Verified]), "全部请求用例通过才成功");
    }

    private static TypeDef Type(string name, int index) => new()
    {
        Index = index, Name = name, Namespace = "Tests", Assembly = "Tests.dll", Token = 0,
        Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false,
    };

    private static MethodDef Method(TypeDef owner, string name, int index) => new()
    {
        Index = index, Owner = owner, Name = name, Token = 0, Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1,
    };

    private sealed class MissingDefinitions : IMethodResults
    {
        public List<MethodDef> Requests { get; } = [];
        public MethodRecoveryResult RecoverDefinition(MethodDef method)
        {
            Requests.Add(method);
            return new(MethodRef.Open(method), 0, null, [new(0, "无定义体")]);
        }
        public MethodRecoveryResult Recover(MethodRef method, ulong entry) => throw new NotSupportedException();
        public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => throw new NotSupportedException();
    }

    private sealed class BarrierContext(ManagedTypes types) : IRuntimeLowering
    {
        public ManagedTypes Types => types;
        public Call Call { get; } = new(0, CallKind.Direct, new Const(0, 64));
        public List<ManagedStatement> Statements { get; } = [];
        public void Emit(ManagedStatement statement) => Statements.Add(statement);
        public RuntimeOp Op => new(OpKind.MemoryBarrier, null);
        public IReadOnlyList<Sym> Arguments => [];
        public TypeRef? ClassOperand => throw new NotSupportedException();
        public Sym Result => throw new NotSupportedException();
        public bool InFault => throw new NotSupportedException();
        public ManagedValue View(Sym sym, TypeRef? expected) => throw new NotSupportedException();
        public TypeRef? TypeOf(Sym sym) => throw new NotSupportedException();
        public LocalValue Local(Sym sym, TypeRef type) => throw new NotSupportedException();
        public Sym? Pointee(int value) => throw new NotSupportedException();
        public ManagedValue? Location(int argument, TypeRef type) => throw new NotSupportedException();
        public ManagedValue Field(Sym receiver, FieldRef field) => throw new NotSupportedException();
        public void AwaitConstruction() => throw new NotSupportedException();
        public bool Absorb(Sym target) => throw new NotSupportedException();
        public bool KnownNonNull(Sym target) => throw new NotSupportedException();
        public bool AbsorbBounds(Sym index, Sym length) => throw new NotSupportedException();
        public bool InCatchOf(Sym exception) => throw new NotSupportedException();
        public MethodRef? ExceptionConstructor(string fullName) => throw new NotSupportedException();
        public ManagedValue Hole(string reason, TypeRef? type) => throw new NotSupportedException();
        public Sym? ClassOwner(Sym klass) => throw new NotSupportedException();
        public bool InitializesNext(TypeRef owner) => throw new NotSupportedException();
    }
}
