using System.Reflection;
using Cpp2CS.Calls;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Algebra;
using Cpp2CS.Machine.Storage;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Effects;
using Cpp2CS.Recovery.Calls;
using Cpp2CS.Recovery.Memory;
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
        var sharedReference = facts.Model.RuntimeTypes.OfType<DefinitionRef>().First(d => !d.Definition.IsValueType && FieldLayouts.IsFullyShared(d));
        var referenceShape = new Aapcs64Classifier(facts.Layouts).Describe(sharedReference);
        checks.True(referenceShape.Kind == Aapcs64Classifier.Kind.Pointer && referenceShape.Size == 8,
            "含共享类型参数的引用仍按 AAPCS64 指针传递");
        Convergence(checks, types);
        Identities(checks, types);
        CallIdentities(checks);
        TailCallIdentities(checks, facts, types);
        MethodPointers(checks, facts, types);
        SharedInterfacePartitions(checks);
        InvokerArguments(checks, facts, types);
        SharedValueModel(checks, facts, types);
        FrameForwards(checks, facts);
        StackBoxes(checks, facts, types);
        PartialScalarCells(checks, facts, types);
        UnusedCallStacks(checks, facts, types);
        EntryKinds(checks, facts, types);
        Templates(checks, types);
        RepeatedExitCopies(checks, types);
        Accessors(checks, types);
        ClosedGenericAccess(checks, types);
        StaticAccessorReferences(checks, types);
        StaticGenericLocations(checks, facts, types);
        ReturnedTemplates(checks, types);
        ReturnedPredicates(checks, types);
        ReturnedFields(checks, types);
        NestedEnumStack(checks);
        InterfaceSlots(checks, types);
        RepresentationCopies(checks, facts, types);
        ConstructorStoreOrder(checks, types);
        ConstructorPreludeStores(checks, types);
        ConstructorContracts(checks, types);
        Effects(checks, types);
        TypeUses(checks, facts, types);
        LowBitArithmetic(checks);
        PackedPhiSlices(checks);
        JoinedPhiSlices(checks);
        AssembledPieces(checks);
        CleanupDispatch(checks);
        PromotedDelegates(checks, facts, types);
        MathImports(checks, types);
        ConstantMemoryCopies(checks, facts, types);
        ArrayIndices(checks);
        Barriers(checks, types);
        UnchangedBarriers(checks, facts);
        CardMarkingBarriers(checks);
        CheckedByteArrays(checks);
        AffineInductions(checks);
        ArrayOffsetInductions(checks);
        ArrayElementTypes(checks, facts, types);
        PhiLoadWidths(checks, facts);
        FloatingOperands(checks, facts, types);
        StackGuards(checks, facts);
        InitializationSnapshots(checks);
        LayoutReloads(checks);
        Verdicts(checks);
        return checks.Finish("架构边界");
    }

    private static void MethodPointers(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var owner = Type("PointerTargets", 820);
        var first = MethodRef.Open(Method(owner, "First", 820));
        var second = MethodRef.Open(Method(owner, "Second", 821));
        Call Pointer(MethodRef method, int width = 64, int offset = 0) => new(4, CallKind.Indirect,
            new Load(offset == 0 ? new Symbol(SymbolKind.Method, method)
                : new Binary(BinOp.Add, new Symbol(SymbolKind.Method, method), Expr.C((ulong)offset, 64), 64), width))
            { Op = new(OpKind.CallMethodPointer, null) };
        var a = Pointer(first);
        var b = Pointer(second);
        var narrow = Pointer(first, 32);
        var invoker = Pointer(first, 64, RuntimeLayout.MethodInvoker);
        var block = new Block(0) { Statements = [a, b, narrow, invoker, new Return(8)] };
        var function = new MachineFunction { Entry = 0, Range = new(0, 12, CodeRegion.Managed, default), Blocks = [block] };
        var values = ValueModel.Build(function, new EmptyEnvironment());
        var oracle = new TypeOracle(types, facts, first, c => new(c, [], null), values);
        var targets = DispatchResolution.Find(function, values, oracle);
        check.True(targets.GetValueOrDefault(a.Site) == first && targets.GetValueOrDefault(b.Site) == second,
            "符号求值后的同地址调用按各自 MethodInfo 解析");
        check.True(!targets.ContainsKey(narrow.Site) && !targets.ContainsKey(invoker.Site),
            "非完整方法指针与 invoker 入口不使用普通调用签名");
    }

    private static void PartialScalarCells(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var owner = Type("ScalarStorage", 810);
        var method = MethodRef.Open(Method(owner, "Fill", 810, MethodAttributes.Public | MethodAttributes.Static));
        method.Method.ReturnType = types.Int32;
        var sink = MethodRef.Open(Method(owner, "Consume", 811, MethodAttributes.Public | MethodAttributes.Static));
        sink.Method.Parameters = [new("bytes", new PointerRef(types.Byte), 0, null, false)];
        sink.Method.ReturnType = types.Int32;
        var abi = new ManagedAbi(facts.Layouts);
        var shapes = new CallShapes(facts, abi, (_, _) => false);
        var cell = new Cell(0, LocalSpace.Frame, -8, 8, "调用实参");
        TypeOracle Analyze(bool initialize, bool late = false)
        {
            var store = new Store(4, new FrameAddress(-7), Expr.C(0xab, 8));
            var call = new Call(12, CallKind.Direct, Expr.C(1, 64))
                { Resolved = sink, Arguments = [new FrameAddress(-8)], Sources = [Storage.Gpr(0)] };
            var block = new Block(0) { Statements = [store, call, new Return(16)] };
            if (initialize) block.Statements.Insert(late ? 1 : 0, new Store(0, new FrameAddress(-8), Expr.C(0, 64)));
            var function = new MachineFunction { Entry = 0, Range = new(0, 20, CodeRegion.Managed, default), Blocks = [block] };
            function.Renumber();
            var environment = new MethodEnvironment(method, abi.Machine(method, out _)!, shapes);
            return new(types, facts, method, environment.Shape, ValueModel.Build(function, environment), new([cell]));
        }
        var initialized = Analyze(true);
        var start = new LocalSym(LocalSpace.Frame, -8);
        check.True(initialized.CellType(cell) == types.UInt64, "完整初始化后的字节写入保留共同标量存储");
        check.True(initialized.Locate(start, 8) is null && initialized.Split(start, 8) is [{ FieldBit: 0, Width: 8 }],
            "首字节写入仍是部分更新，不能覆盖整个标量");
        check.True(initialized.Split(new LocalSym(LocalSpace.Frame, -7), 8) is [{ FieldBit: 8, Width: 8 }],
            "内部字节更新保留相邻位");
        check.True(Analyze(false).CellType(cell) is null && Analyze(true, true).CellType(cell) is null,
            "部分写入前没有完整初始化时不引入读改写");
    }

    private static void StackBoxes(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var definition = new TypeDef { Index = 800, Assembly = "Tests.dll", Namespace = "Tests", Name = "State", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = true, BaseType = new DefinitionRef(types.CorlibDefinition("System.Enum")!, []) };
        var type = new DefinitionRef(definition, []);
        var method = new MethodRef(types.CorlibDefinition("System.Enum")!.Methods.Single(m => m.Name == "ToString" && m.Parameters.Count == 0), [], []);
        var abi = new ManagedAbi(facts.Layouts);
        bool Run(string? variant = null)
        {
            var entry = new Block(0) { Statements = [new Branch(0, Expr.C(1, 1), 4, 8)] };
            var left = new Block(4) { Statements = [new Store(4, new FrameAddress(-16), Expr.C(1, 32)), new Jump(4, 12)] };
            var right = new Block(8) { Statements = variant == "missing" ? [new Jump(8, 12)]
                : [new Store(8, new FrameAddress(-16), Expr.C(2, 32)), new Jump(8, 12)] };
            var call = new Call(24, CallKind.Direct, Expr.C(1, 64))
                { Arguments = [new FrameAddress(-32), Expr.C(0, 64)], Sources = [Storage.Gpr(0), Storage.Gpr(1)] };
            var last = new Block(12) { Statements = [
                new Store(12, new FrameAddress(-32), new Symbol(SymbolKind.Class, type)),
                new Store(16, new FrameAddress(-24), Expr.C(variant == "monitor" ? 0 : ulong.MaxValue, 64)), call, new Return(28)] };
            if (variant is "alias" or "unrelated") last.Statements.Insert(2, new Call(20, CallKind.Indirect, Expr.C(2, 64))
                { Arguments = variant == "alias" ? [new FrameAddress(-32)] : [], Sources = variant == "alias" ? [Storage.Gpr(0)] : [] });
            if (variant == "partial") last.Statements.Insert(2, new Store(20, new FrameAddress(-15), Expr.C(0, 8)));
            MachineFunction.AddEdge(entry, left); MachineFunction.AddEdge(entry, right);
            MachineFunction.AddEdge(left, last); MachineFunction.AddEdge(right, last);
            var function = new MachineFunction { Entry = 0, Range = new(0, 32, CodeRegion.Managed, default), Blocks = [entry, left, right, last] };
            CallShape Shape(Call c) => new(c, ReferenceEquals(c, call) ? [method] : [], ReferenceEquals(c, call) ? abi.Machine(method, out _) : null);
            var changed = StackBoxingPass.Run(function, new CallMemoryEffects(Shape, abi), Shape, _ => 4, () => new(Storage.Temp(800), 1));
            return changed && last.Statements.OfType<Call>().Any(c => c.Op?.Kind == OpKind.Box
                && c.Arguments[1] == new FrameAddress(-16)) && last.Statements.OfType<Store>().Count() >= 2;
        }
        check.True(Run(), "栈上枚举装箱保留两条路径的有效载荷，以原存储作为装箱来源");
        check.True(Run("unrelated"), "未取得栈对象地址的调用不破坏对象头证明");
        check.True(!Run("monitor"), "栈对象标志不匹配时拒绝装箱归一");
        check.True(!Run("missing"), "任一路径缺少有效载荷写入时拒绝装箱归一");
        check.True(!Run("alias"), "取得栈对象地址的未知调用阻断装箱证明");
        check.True(!Run("partial"), "部分覆盖不能充当完整枚举载荷");
    }

    private static void CallIdentities(Assertions check)
    {
        var call = new Call(0, CallKind.Direct, Expr.C(4, 64));
        var other = new Call(0, CallKind.Direct, Expr.C(4, 64));
        check.True(!ReferenceEquals(call.Site, other.Site), "来源地址和操作数相同不代表同一次调用");
        check.True(ReferenceEquals(call.Site, (call with { Kind = CallKind.Indirect }).Site), "原调用的改写保留调用点身份");
        var copy = call.Duplicate();
        check.True(!ReferenceEquals(call.Site, copy.Site) && ReferenceEquals(copy.Site.Origin, call.Site),
            "路径复制有独立身份并保留来源");
        var syms = new SymTable();
        check.True(!ReferenceEquals(syms.Result(call, 0, 64), syms.Result(other, 0, 64)),
            "同地址的不同调用不能共享结果原子");
        var first = new Block(0) { Statements = [call, new Jump(0, 4)] };
        var variable = new Variable(Storage.Gpr(0), 1);
        var last = new Block(4) { Statements = [new Phi(4, variable, [variable]), new Return(4)] };
        MachineFunction.AddEdge(first, last);
        var original = new MachineFunction { Entry = 0, Range = new(0, 8, CodeRegion.Managed, default), Blocks = [first, last] };
        var analysis = original.Copy();
        ((Phi)analysis.Blocks[1].Statements[0]).Sources[0] = new(Storage.Gpr(1), 0);
        analysis.Blocks[0].Statements.RemoveAt(0);
        check.True(first.Statements[0] == call && ((Phi)last.Statements[0]).Sources[0] == variable,
            "分析副本的语句和合流来源不修改稳定输入");
        check.True(analysis.Blocks[0].Successors[0] == analysis.Blocks[1] && analysis.Blocks[1].Predecessors[0] == analysis.Blocks[0],
            "分析副本的控制边只引用副本块");
        check.True(ReferenceEquals(((Call)original.Copy().Blocks[0].Statements[0]).Site, call.Site),
            "同一调用在不同分析版本中保留逻辑身份");
    }

    private static void TailCallIdentities(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var owner = Type("TailTargets", 700);
        var first = new MethodRef(Method(owner, "First", 700), [], []);
        var second = new MethodRef(Method(owner, "Second", 701), [], []);
        foreach (var tail in new[] { false, true })
        foreach (var sameTarget in new[] { false, true })
        {
            var leftTarget = new Variable(Storage.Gpr(9), 1);
            var rightTarget = new Variable(Storage.Gpr(9), 2);
            var mergedTarget = new Variable(Storage.Gpr(9), 3);
            var head = new Block(0) { Statements = [new Branch(0, Expr.C(1, 1), 4, 8)] };
            var left = new Block(4) { Statements = [new Define(4, leftTarget, new Symbol(SymbolKind.Method, first)), new Jump(4, 12)] };
            var right = new Block(8) { Statements = [new Define(8, rightTarget, new Symbol(SymbolKind.Method, sameTarget ? first : second)), new Jump(8, 12)] };
            var call = new Call(12, tail ? CallKind.TailIndirect : CallKind.Indirect, new Use(mergedTarget, 64));
            var merge = new Block(12) { Statements = [new Phi(12, mergedTarget, [leftTarget, rightTarget]), call] };
            if (!tail) merge.Statements.Add(new Return(16));
            MachineFunction.AddEdge(head, left);
            MachineFunction.AddEdge(head, right);
            MachineFunction.AddEdge(left, merge);
            MachineFunction.AddEdge(right, merge);
            var function = new MachineFunction { Entry = 0, Range = new(0, 20, CodeRegion.Managed, default), Blocks = [head, left, right, merge] };
            check.True(tail ? MergedIndirectTails.Run(function) : Cpp2CS.Machine.Ssa.TailDuplication.Run(function, b => b == merge),
                "共享调用尾部可拆回两条入边");
            var copies = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().ToArray();
            check.True(copies.Length == 2 && copies.Select(c => c.Site).Distinct().Count() == 2,
                "尾部拆分后的调用点身份互不相同");
            check.True(copies.All(c => ReferenceEquals(c.Site.Origin, call.Site)), "尾部调用副本保留来源身份");
            if (copies.Select(c => c.Site).Distinct().Count() != 2) continue;
            var values = ValueModel.Build(function, new EmptyEnvironment());
            var oracle = new TypeOracle(types, facts, first, _ => throw new NotSupportedException(), values);
            var targets = DispatchResolution.Find(function, values, oracle);
            check.Equal(first, targets[left.Statements.OfType<Call>().Single().Site], "左路径保留自身分派目标");
            check.Equal(sameTarget ? first : second, targets[right.Statements.OfType<Call>().Single().Site],
                "相同或不同的分派目标均按各自调用点登记");
        }
    }

    private static void InvokerArguments(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var owner = Type("InvokerOwner", 770);
        var definition = Method(owner, "Invoke", 770, MethodAttributes.Public | MethodAttributes.Static);
        definition.Parameters = [new("number", types.Int32, 0, null, false), new("reference", types.Object, 0, null, false), new("output", new ByRefRef(types.Single), ParameterAttributes.Out, null, false)];
        definition.ReturnType = types.String;
        var method = new MethodRef(definition, [], []);
        var abi = new ManagedAbi(facts.Layouts);
        var signature = abi.Invoker(method);
        check.True(signature.Arguments[0] is { Transfer: Transfer.Copy, Size: 4, Access: MemoryAccess.Read }
            && signature.Arguments[1] is { Transfer: Transfer.Value, Size: 8 }
            && signature.Arguments[2] is { Transfer: Transfer.Reference, Size: 4, Access: MemoryAccess.Write },
            "invoker 分别保留标量指针、对象引用和 out 存储");
        check.True(signature.Return is { Transfer: Transfer.ResultBuffer, Size: 8, Access: MemoryAccess.Write },
            "invoker 的引用返回值同样写入返回存储");
        var entity = new Symbol(SymbolKind.Method, method);
        foreach (var samePointer in new[] { true, false })
        {
            var call = new Call(0, CallKind.Indirect, new Load(new Binary(BinOp.Add, entity, Expr.C(RuntimeLayout.MethodInvoker, 64), 64), 64))
            {
                Arguments = [samePointer ? new Load(entity, 64) : Expr.C(16, 64), entity, Expr.C(0, 64), new FrameAddress(-32), new FrameAddress(-8)],
                Sources = Enumerable.Range(0, 5).Select(Storage.Gpr).ToArray(),
                Defines = [new(Storage.Gpr(0), 1)], Results = [Storage.Gpr(0)],
            };
            var block = new Block(0) { End = 4, Statements = [call, new Return(4)] };
            var function = new MachineFunction { Entry = 0, Range = new(0, 8, CodeRegion.Managed, default), Blocks = [block] };
            var state = new IdiomState(new IdiomRewriter(facts), function);
            check.Equal(samePointer, state.InvokerCalls(), "invoker 入口、MethodInfo 与实际方法指针须同源");
            if (!samePointer) continue;
            var normalized = block.Statements.OfType<Call>().Single();
            check.True(normalized.Op is { Kind: OpKind.InvokeGeneric, Operand: MethodRef } && normalized.Defines.Length == 0
                && normalized.Arguments.Take(3).All(a => a is Load { Width: 64 }), "拆包读取参数槽，不提前读取标量内容或伪造返回寄存器");
        }
        var instance = MethodRef.Open(Method(owner, "Instance", 772));
        instance.Method.Parameters = definition.Parameters;
        instance.Method.ReturnType = definition.ReturnType;
        var instanceEntity = new Symbol(SymbolKind.Method, instance);
        var receiver = new Variable(Storage.Gpr(20), 1);
        var invocation = new Call(8, CallKind.Indirect, new Load(new Binary(BinOp.Add, instanceEntity, Expr.C(RuntimeLayout.MethodInvoker, 64), 64), 64))
        {
            Arguments = [new Load(instanceEntity, 64), instanceEntity, new Use(receiver, 64), new FrameAddress(-32), new FrameAddress(-8)],
            Sources = Enumerable.Range(0, 5).Select(Storage.Gpr).ToArray(),
        };
        var retained = new Block(0) { Statements = [new Define(0, receiver, new Load(Expr.C(128, 64), 64)),
            new Call(4, CallKind.Direct, Expr.C(256, 64)), invocation, new Return(12)] };
        var receiverFunction = new MachineFunction { Entry = 0, Range = new(0, 16, CodeRegion.Managed, default), Blocks = [retained] };
        var receiverState = new IdiomState(new IdiomRewriter(facts), receiverFunction);
        check.True(receiverState.InvokerCalls() && retained.Statements.OfType<Call>().Single(c => c.Op?.Kind == OpKind.InvokeGeneric)
            .Arguments[0] == new Use(receiver, 64), "invoker 接收者保留原值，不能跨调用重新读取字段");
    }

    /// <summary>完全共享泛型的不透明值：表示转换归一为句柄，按 sizeof(T) 的复制成为位置操作。</summary>
    private static void SharedValueModel(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var type = new GenericParameterRef("T", false, 0);
        var klass = new Symbol(SymbolKind.Class, type);
        Expr Field(int offset, int width) => new Load(new Binary(BinOp.Add, klass, Expr.C((ulong)offset, 64), 64), width);
        var flag = new Compare(Cond.Slt, Field(RuntimeLayout.ClassByvalArg + 8, 32), Expr.C(0, 32));
        var input = new Use(new Variable(Storage.Gpr(1), 0), 64);
        var size = new Variable(Storage.Temp(900), 1);
        var aligned = new Variable(Storage.Temp(901), 1);
        var local = new Variable(Storage.Temp(902), 1);
        var picked = new Variable(Storage.Temp(903), 1);
        (Block Block, MachineFunction Function) Build(string variant)
        {
            Expr saved = new FrameAddress(-16);
            var other = new Use(new Variable(Storage.Gpr(2), 0), 64);
            var block = new Block(0) { Statements = [
                new Store(0, saved, variant == "other-saved" ? other : input),
                new Define(4, size, new Ir.Convert(ConvKind.ZeroExtend, Field(RuntimeLayout.ClassStackSlotSize, 32), 64)),
                new Define(8, aligned, new Binary(BinOp.And, new Binary(BinOp.Add, new Use(size, 64), Expr.C(15, 64), 64), Expr.C(0x1fffffff0, 64), 64)),
                new Define(12, local, new Binary(BinOp.Sub, new FrameAddress(-64), new Use(aligned, 64), 64)),
                new Define(16, picked, new Select(flag, input, saved, 64)),
                new Call(20, CallKind.Direct, Expr.C(128, 64)) { Op = new(OpKind.Import, "memcpy"),
                    Arguments = [new Use(local, 64), new Use(picked, 64), variant == "wrong-size" ? Expr.C(8, 64) : new Use(size, 64)] },
                new Return(24)] };
            return (block, new MachineFunction { Entry = 0, Range = new(0, 28, CodeRegion.Managed, default), Blocks = [block] });
        }
        foreach (var variant in new[] { "copy", "other-saved", "wrong-size" })
        {
            var (block, function) = Build(variant);
            var state = new IdiomState(new IdiomRewriter(facts), function);
            check.True(state.SharedValues(), $"不透明值归一 {variant}");
            var copy = block.Statements.OfType<Call>().Single();
            check.Equal(variant != "wrong-size", copy.Op?.Kind == OpKind.CopyGenericValue, $"按 sizeof(T) 的复制成为位置操作 {variant}");
            check.True(block.Statements.OfType<Define>().Any(d => d.Target == local && d.Value is StackAllocation), $"T 大小的动态分配是 T 的局部 {variant}");
            var selection = block.Statements.OfType<Define>().Single(d => d.Target == picked).Value;
            check.Equal(variant != "other-saved", selection == input, $"形参地址归一为句柄 {variant}");
        }
        // invoker 槽的两种表示合流：isValue(T) ? a : *a。
        foreach (var variant in new[] { "repr", "different" })
        {
            var head = new Block(0);
            var arm = new Block(4);
            var join = new Block(8);
            var loaded = new Variable(Storage.Temp(910), 1);
            var slot = new Variable(Storage.Temp(911), 1);
            head.Statements = [new Branch(0, flag, 8, 4)];
            arm.Statements = [new Define(4, loaded, variant == "repr" ? new Load(input, 64) : new Load(new Binary(BinOp.Add, input, Expr.C(8, 64), 64), 64)), new Jump(4, 8)];
            join.Statements = [new Phi(8, slot, [input.Variable, loaded]), new Return(12) { Pieces = [new(0, new Use(slot, 64))] }];
            var function = new MachineFunction { Entry = 0, Range = new(0, 16, CodeRegion.Managed, default), Blocks = [head, arm, join] };
            MachineFunction.AddEdge(head, join);
            MachineFunction.AddEdge(head, arm);
            MachineFunction.AddEdge(arm, join);
            function.Renumber();
            var state = new IdiomState(new IdiomRewriter(facts), function);
            state.SharedValues();
            check.Equal(variant == "repr", head.Statements[^1] is Jump, $"值类型分支的两种表示 {variant}");
        }
    }

    /// <summary>私有栈槽的保存与读回：每条路径都到达同值的完整写入才转发。</summary>
    private static void FrameForwards(Assertions check, ProgramFacts facts)
    {
        var effects = new CallMemoryEffects(new CallShapes(facts, new ManagedAbi(facts.Layouts), (_, _) => false).Of, new ManagedAbi(facts.Layouts));
        foreach (var variant in new[] { "private", "mutable-field", "overwritten", "escaped", "before-save" })
        {
            var input = new Use(new Variable(Storage.Gpr(3), 0), 64);
            var slot = new FrameAddress(-16);
            var loaded = new Variable(Storage.Temp(870), 1);
            Expr initial = variant == "mutable-field" ? new Load(new Binary(BinOp.Add, input, Expr.C(16, 64), 64), 64) : input;
            var saved = new Store(0, slot, initial);
            var read = new Define(8, loaded, new Load(slot, 64));
            var statements = new List<Stmt> { saved, read, new Return(12) { Pieces = [new(0, new Use(loaded, 64))] } };
            if (variant == "overwritten") statements.Insert(1, new Store(4, slot, Expr.C(0, 64)));
            if (variant == "escaped") statements.Insert(1, new Store(4, new Use(new Variable(Storage.Gpr(1), 0), 64), slot));
            if (variant == "before-save") (statements[0], statements[1]) = (read, saved);
            var function = new MachineFunction { Entry = 0, Range = new(0, 16, CodeRegion.Managed, default), Blocks = [new(0) { Statements = statements }] };
            var forwarded = FrameForwarding.Run(function, effects)
                && function.Blocks[0].Statements.OfType<Define>().Any(d => d.Target == loaded && d.Value is not Load);
            check.Equal(variant is "private" or "overwritten" ? 1 : 0, forwarded ? 1 : 0, $"私有栈槽转发 {variant}");
            if (variant == "overwritten")
                check.True(function.Blocks[0].Statements.OfType<Define>().Any(d => d.Target == loaded && d.Value is Const { Value: 0 }), "转发取到达读取的写入");
        }
        foreach (var variant in new[] { "conditional", "unknown-call", "escaped" })
        {
            var head = new Block(0);
            var initialize = new Block(8);
            var merge = new Block(16);
            var input = new Variable(Storage.Vec(0), 0);
            var result = new Variable(Storage.Vec(1), 1);
            var frame = new FrameAddress(-32);
            head.Statements = [new Store(0, frame, new Use(input, 128)), new Branch(4, Expr.C(1, 1), 8, 16)];
            initialize.Statements = [new Call(8, CallKind.Direct, Expr.C(64, 64))
            { Op = variant == "unknown-call" ? null : new(OpKind.RunClassConstructor, null), StackPointer = frame,
                Arguments = variant == "escaped" ? [frame] : [] }, new Jump(12, 16)];
            merge.Statements = [new Define(16, result, new Ir.Convert(ConvKind.ZeroExtend, new Load(frame, 32), 128)),
                new Return(20) { Value = new Use(result, 32) }];
            var function = new MachineFunction { Entry = 0, Range = new(0, 24, CodeRegion.Managed, default), Blocks = [head, initialize, merge] };
            MachineFunction.AddEdge(head, initialize);
            MachineFunction.AddEdge(head, merge);
            MachineFunction.AddEdge(initialize, merge);
            function.Renumber();
            var forwarded = FrameForwarding.Run(function, effects);
            // 栈地址没有传给调用时，未解析的调用也看不到私有槽。
            check.Equal(variant != "escaped", forwarded, $"私有向量保存跨调用 {variant}");
        }
    }

    private static void SharedInterfacePartitions(Assertions check)
    {
        foreach (var count in new[] { 2, 4 })
        foreach (var consistent in new[] { true, false })
        foreach (var withResult in new[] { true, false })
        {
            var version = 0;
            Variable Fresh(int width = 64) => new(Storage.Gpr(20), ++version);
            var receiver = new Use(new(Storage.Gpr(0), 0), 64);
            var head = new Block(0);
            var slow = new Block(1000) { End = 1008 };
            var hit = new Block(1020) { End = 1028 };
            var merge = new Block(1040) { End = 1048 };
            var function = new MachineFunction { Entry = 0, Range = new(0, 1052, CodeRegion.Managed, default), Blocks = [head, slow, hit, merge] };
            var slots = new List<Variable>();
            var offsets = new List<Variable>();
            for (var i = 0; i < count; i++)
            {
                var slot = Fresh(); slots.Add(slot);
                var offset = Fresh(); offsets.Add(offset);
                var branch = new Block((ulong)(4 + i * 12));
                var left = new Block(branch.Start + 4) { Statements = [new Define(0, slot, Expr.C((ulong)i + 1, 64)), new Jump(0, slow.Start)] };
                var right = new Block(branch.Start + 8) { Statements = [new Define(0, offset,
                    new Ir.Convert(ConvKind.ZeroExtend, new Binary(BinOp.Add, new Use(new(Storage.Gpr(1), 0), 32), Expr.C((ulong)(consistent || i != count - 1 ? i + 1 : count + 1), 32), 32), 64)), new Jump(0, hit.Start)] };
                branch.Statements.Add(new Branch(0, Expr.C(1, 1), left.Start, right.Start));
                MachineFunction.AddEdge(head, branch);
                MachineFunction.AddEdge(branch, left); MachineFunction.AddEdge(branch, right);
                MachineFunction.AddEdge(left, slow); MachineFunction.AddEdge(right, hit);
                function.Blocks.AddRange([branch, left, right]);
            }
            var slotPhi = Fresh();
            var offsetPhi = Fresh();
            var slowResult = Fresh();
            var fastResult = Fresh();
            var mergedResult = Fresh();
            var lookup = new Call(1004, CallKind.Direct, Expr.C(2000, 64))
                { Arguments = [receiver, Expr.C(3000, 64), new Use(slotPhi, 64)], Defines = [slowResult], Results = [Storage.Gpr(0)] };
            slow.Statements = [new Phi(1000, slotPhi, slots.ToArray()), lookup, new Jump(1008, merge.Start)];
            hit.Statements = [new Phi(1020, offsetPhi, offsets.ToArray()), new Define(1024, fastResult, new Use(offsetPhi, 64)), new Jump(1028, merge.Start)];
            var callResult = Fresh();
            var invocation = new Call(1044, withResult ? CallKind.Indirect : CallKind.TailIndirect, new Use(mergedResult, 64))
                { Defines = withResult ? [callResult] : [], Results = withResult ? [Storage.Gpr(0)] : [] };
            merge.Statements = [new Phi(1040, mergedResult, [slowResult, fastResult]), invocation];
            MachineFunction.AddEdge(slow, merge); MachineFunction.AddEdge(hit, merge);
            if (withResult)
            {
                var returned = Fresh();
                var exit = new Block(1060) { End = 1064, Statements = [new Phi(1060, returned, [callResult]), new Return(1064) { Value = new Use(returned, 64) }] };
                merge.Statements.Add(new Jump(1048, exit.Start));
                MachineFunction.AddEdge(merge, exit);
                function.Blocks.Add(exit);
            }
            function.Renumber();
            var changed = SharedInterfaceTails.Run(function, c => ReferenceEquals(c, lookup), Fresh);
            check.Equal(consistent, changed, "接口尾部逐一配对所有快慢路径槽位，缺少对应槽时拒绝拆分");
            if (changed) check.Equal(count, function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Count(c => c.Kind is CallKind.Indirect or CallKind.TailIndirect),
                "每个接口槽保留一个独立调用");
            if (changed && withResult)
            {
                var results = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Kind == CallKind.Indirect).SelectMany(c => c.Defines).ToHashSet();
                var exit = function.Blocks.Single(b => b.Start == 1060);
                check.True(exit.Statements.OfType<Phi>().Single().Sources.All(results.Contains) && exit.Predecessors.Count == count,
                    "各分支调用结果经新入边汇合，出口不引用被删除的调用结果");
            }
        }
    }

    private static void AssembledPieces(Assertions check)
    {
        var syms = new SymTable();
        var whole = syms.Arg(0, 64);
        check.True(ReferenceEquals(whole, syms.Assemble(64, [(32, syms.Slice(whole, 32, 32)), (0, syms.Slice(whole, 0, 32))])),
            "ABI 位片按偏移重组，与枚举次序无关");
        check.True(ReferenceEquals(whole, syms.Assemble(64, [(0, syms.Slice(whole, 0, 48)), (32, syms.Slice(whole, 32, 32))])),
            "一致的重叠来源可以组成完整值");
        check.True(syms.Assemble(64, [(0, whole), (32, syms.Arg(1, 32))]) is UnknownSym,
            "重叠来源不一致时拒绝按次序覆盖");
        var missing = syms.Assemble(64, [(32, syms.Slice(whole, 32, 32))]);
        check.True(syms.Slice(missing, 0, 32) is UndefSym, "缺少的 ABI 位片保留未定义");
        check.True(ReferenceEquals(syms.Slice(whole, 16, 32), syms.Assemble(32, [(-16, whole)])),
            "组成值只观察目标范围内的位");
    }

    private static void LayoutReloads(Assertions check)
    {
        foreach (var variant in new[] { "diamond", "triangle", "different-size", "side-effect" })
        {
            var head = new Block(0);
            var initialize = new Block(16);
            var skip = new Block(32);
            var merge = new Block(48);
            var triangle = variant != "diamond";
            var type = new GenericParameterRef("T", true, 0);
            var klass = new Symbol(SymbolKind.Class, type);
            var before = new Variable(Storage.Gpr(20), 1);
            var result = new Variable(Storage.Gpr(0), 1);
            var after = new Variable(Storage.Gpr(21), 1);
            var joined = new Variable(Storage.Gpr(22), 1);
            Expr Size(Expr subject, int offset = RuntimeLayout.ClassStackSlotSize) => new Ir.Convert(ConvKind.ZeroExtend,
                new Load(new Binary(BinOp.Add, subject, Expr.C((ulong)offset, 64), 64), 32), 64);
            var read = new Define(0, before, Size(klass, variant == "different-size" ? RuntimeLayout.ClassStackSlotSize + 4 : RuntimeLayout.ClassStackSlotSize));
            var flag = new Binary(BinOp.And, new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassBitflags1, 64), 64), 8), Expr.C(1, 8), 8);
            head.Statements = [new Branch(4, new Compare(Cond.Ne, flag, Expr.C(0, 8)), triangle ? merge.Start : skip.Start, initialize.Start)];
            if (triangle) head.Statements.Insert(0, read);
            else skip.Statements = [read, new Jump(36, merge.Start)];
            initialize.Statements = [new Call(16, CallKind.Direct, Expr.C(128, 64))
                { Op = new(OpKind.InitClass, type), Arguments = [klass], Defines = [result], Results = [Storage.Gpr(0)] },
                new Define(20, after, Size(new Use(result, 64))), new Jump(24, merge.Start)];
            if (variant == "side-effect") initialize.Statements.Insert(2, new Store(22, new FrameAddress(-8), Expr.C(1, 64)));
            merge.Statements = [new Phi(48, joined, [before, after]), new Return(52) { Value = new Use(joined, 64) }];
            MachineFunction.AddEdge(head, triangle ? merge : skip);
            MachineFunction.AddEdge(head, initialize);
            if (!triangle) MachineFunction.AddEdge(skip, merge);
            MachineFunction.AddEdge(initialize, merge);
            var function = new MachineFunction { Entry = 0, Range = new(0, 56, CodeRegion.Managed, default),
                Blocks = triangle ? [head, initialize, merge] : [head, initialize, skip, merge] };
            check.Equal(variant is "diamond" or "triangle", ClassLayoutReloads.Run(function), $"类布局重读的合流路径 {variant}");
        }
    }

    private static void InitializationSnapshots(Assertions check)
    {
        foreach (var variant in new[] { "low", "whole", "overwritten", "stale-alias" })
        {
            var head = new Block(0);
            var fast = new Block(8);
            var slow = new Block(16);
            var merge = new Block(24);
            var input = new Variable(Storage.Vec(0), 0);
            var saved = new Variable(Storage.Vec(1), 1);
            var reloaded = new Variable(Storage.Vec(2), 1);
            var joined = new Variable(Storage.Vec(3), 1);
            var field = new Binary(BinOp.Add, new Use(new(Storage.Gpr(0), 0), 64), Expr.C(16, 64), 64);
            head.Statements = [new Store(0, field, new Use(input, 128))];
            if (variant == "overwritten") head.Statements.Add(new Store(2, field, Expr.C(1, 32)));
            var fastValue = new Use(input, 128);
            if (variant == "stale-alias")
            {
                var old = new Variable(Storage.Vec(4), 1);
                var alias = new Variable(Storage.Vec(5), 1);
                head.Statements.Insert(0, new Define(0, old, new Ir.Convert(ConvKind.ZeroExtend, new Load(field, 32), 128)));
                head.Statements.Add(new Define(2, alias, new Use(old, 128)));
                fastValue = new Use(alias, 128);
            }
            head.Statements.Add(new Branch(4, Expr.C(1, 1), 8, 16));
            fast.Statements = [new Define(8, saved, fastValue), new Jump(12, 24)];
            slow.Statements = [new Define(16, reloaded, new Ir.Convert(ConvKind.ZeroExtend, new Load(field, 32), 128)), new Jump(20, 24)];
            merge.Statements = [new Phi(24, joined, [saved, reloaded]), new Return(28) { Value = new Use(joined, variant == "whole" ? 128 : 32) }];
            var function = new MachineFunction { Entry = 0, Range = new(0, 32, CodeRegion.Managed, default), Blocks = [head, fast, slow, merge] };
            MachineFunction.AddEdge(head, fast);
            MachineFunction.AddEdge(head, slow);
            MachineFunction.AddEdge(fast, merge);
            MachineFunction.AddEdge(slow, merge);
            check.Equal(variant == "low", MetadataGuardSnapshots.Equivalent(function, head, [slow], [fast], merge), $"初始化重读的观察位 {variant}");
        }
    }

    private static void StackGuards(Assertions check, ProgramFacts facts)
    {
        foreach (var variant in new[] { "paired", "different-slot", "modified-save", "other-failure" })
        {
            Expr Guard(ulong slot) => new Load(new Binary(BinOp.Add,
                new Intrinsic("sysreg_tpidr_el0", [], 64), Expr.C(slot, 64), 64), 64);
            var saved = variant == "modified-save" ? new Binary(BinOp.Add, Guard(40), Expr.C(1, 64), 64) : Guard(40);
            var test = new Block(0);
            var normal = new Block(4);
            var failure = new Block(8);
            test.Statements = [new Branch(0, new Compare(Cond.Ne, Guard(variant == "different-slot" ? 48UL : 40UL), saved), 8, 4)];
            normal.Statements = [new Return(4)];
            failure.Statements = [new Call(8, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.Import, variant == "other-failure" ? "abort" : "__stack_chk_fail") }];
            var function = new MachineFunction { Entry = 0, Range = new(0, 12, CodeRegion.Managed, default), Blocks = [test, normal, failure] };
            MachineFunction.AddEdge(test, failure);
            MachineFunction.AddEdge(test, normal);
            check.Equal(variant == "paired", StackGuardNormalizer.Run(function), $"栈保护配对 {variant}");
        }
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
            if (pass == "guarded")
            {
                var checks = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().ToArray();
                check.True(checks.Length == 2 && checks.Select(c => c.Site).Distinct().Count() == 2,
                    "检查随读取拆到入边后，各路径拥有独立调用点身份");
            }
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
            return new BodyValidation(types, EmissionPolicy.Recovered, method).Check(body, true);
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
        check.True(new BodyValidation(types, EmissionPolicy.Partial, staticMethod).Check(invalidThis, true) is
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

    private static void RepeatedExitCopies(Assertions check, ManagedTypes types)
    {
        var owner = Type("ExitStorage", 840);
        var ownerRef = new DefinitionRef(owner, []);
        var field = new FieldDef { Index = 840, Owner = owner, Name = "value", Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 16 };
        owner.Fields = [field];
        var definition = Method(owner, "Set", 840);
        definition.Parameters = [new("value", types.Int32, 0, null, false)];
        owner.Methods = [definition];
        var method = new MethodRef(definition, [], []);
        var input = new ArgumentValue(0, types.Int32, 32);
        var zero = new ConstantValue(0, types.Int32, 32);
        FieldValue Field(ManagedValue receiver) => new(receiver, new(field, ownerRef), types.Int32, 32);
        var self = new ArgumentValue(-1, ownerRef, 64);
        ManagedBranch Branch(ManagedValue value) => new(4, new ComparisonValue(Cond.Eq, value, zero, types.Boolean), new(16, []), new(32, []));
        var template = new ManagedBody(method, [new(0, [new ManagedStore(0, Field(self), input), Branch(input)]),
            new(16, [new ManagedStore(16, Field(self), zero), new ManagedReturn(20, null)]),
            new(32, [new ManagedStore(32, Field(self), input), new ManagedReturn(36, null)])]);
        MethodRecoveryResult? Summary(MethodRef requested) => requested.Method == definition ? new(method, 0, template, []) : null;
        var callerDefinition = Method(Type("ExitConsumer", 841), "Run", 841);
        callerDefinition.ReturnType = types.Int32;
        var caller = new MethodRef(callerDefinition, [], []);
        var receiver = new ArgumentValue(0, ownerRef, 64);
        var argument = new ArgumentValue(1, types.Int32, 32);
        var saved = new LocalValue(new(Storage.Temp(840), 1), types.Int32, 32);
        foreach (var variant in new[] { "same", "different", "addressed", "shared" })
        {
            var start = new List<ManagedStatement> { new ManagedAssignment(0, saved, argument) };
            if (variant == "addressed") start.Add(new ManagedAssignment(0,
                new(new(Storage.Temp(841), 1), new ByRefRef(types.Int32), 64), new AddressValue(saved)));
            start.Add(new ManagedStore(0, Field(receiver) with { Pending = new(0, "待证字段", true) }, argument));
            start.Add(Branch(argument));
            var body = new ManagedBody(caller, [new(0, start),
                new(16, [new ManagedStore(16, Field(receiver) with { Pending = new(16, "待证字段", true) }, zero), new ManagedJump(20, new(48, []))]),
                new(32, variant == "shared"
                    ? [new ManagedAssignment(32, saved, zero), new ManagedStore(32, Field(receiver) with { Pending = new(32, "待证字段", true) }, argument), new ManagedJump(36, new(48, []))]
                    : [new ManagedStore(32, Field(receiver) with { Pending = new(32, "待证字段", true) }, argument), new ManagedJump(36, new(64, []))]),
                new(48, [new ManagedAssignment(48, saved, variant == "different" ? zero : argument), new ManagedJump(52, new(64, []))]),
                new(64, [new ManagedReturn(64, saved)])]);
            var evidence = new InlineEvidence(types, caller, Summary);
            var recovered = new TemplateRecovery(types, caller, Summary, evidence).Run(body, new Dictionary<Variable, PendingConstruction>(), 0);
            check.Equal(variant is "same" or "shared", recovered.Holes.Count == 0, $"出口重复局部赋值 {variant}");
        }
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
            new ManagedStore(0, Field(receiver, first) with { Pending = new(0, "待证字段", true) }, value),
            new ManagedStore(4, Field(receiver, second) with { Pending = new(4, "待证字段", true) }, last),
            new ManagedReturn(8, null),
        ])]);
        var fields = new InlineEvidence(types, caller, Summary);
        var recovery = new TemplateRecovery(types, caller, Summary, fields);
        var success = recovery.Run(Body(value), new Dictionary<Variable, PendingConstruction>(), 0);
        check.Equal(0, success.Holes.Count, "两次字段写入的模板证明成功");
        check.True(success.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined && c.Invocation.Method == method), "证明区域被替换成调用");
        var failure = recovery.Run(Body(new ConstantValue(7, types.Int32, 32)), new Dictionary<Variable, PendingConstruction>(), 0);
        check.True(failure.Holes.Count > 0, "写入不一致时保留缺口");
        check.True(!failure.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined), "失败的证明不改写成调用");
        var prepare = Method(Type("Preparation", 13), "Run", 13, MethodAttributes.Public | MethodAttributes.Static);
        var prelude = new ManagedCall(0, new(new(prepare, [], []), null, [], false), null, false);
        template = template with { Blocks = [new(0, new ManagedStatement[] { prelude }.Concat(template.Blocks[0].Statements).ToArray())] };
        ManagedBody Split(bool changed) => new(caller,
        [
            new(0, [changed ? new ManagedCall(0, prelude.Invocation with { Arguments = [value] }, null, false) : prelude,
                new ManagedJump(0, new(4, []))]),
            new(4, [new ManagedJump(4, new(8, []))]),
            new(8, Body(value).Blocks[0].Statements),
        ]);
        var split = new TemplateRecovery(types, caller, Summary, fields).Run(Split(false), new Dictionary<Variable, PendingConstruction>(), 0);
        check.Equal(0, split.Holes.Count, "沿唯一前驱纳入模板的前导调用");
        var changedPrelude = new TemplateRecovery(types, caller, Summary, fields).Run(Split(true), new Dictionary<Variable, PendingConstruction>(), 0);
        check.True(changedPrelude.Holes.Count > 0, "前导调用不一致时不能跳过该效果");
        var inaccessible = new TypeDef { Index = 12, Name = "Hidden", Namespace = "Tests", Assembly = "Other.dll", Token = 0,
            Attributes = TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var exposed = new FieldDef { Index = 12, Owner = inaccessible, Name = "value", Type = types.Int32, Offset = 16, Attributes = FieldAttributes.Public };
        check.True(!fields.Accessible(new(exposed, new DefinitionRef(inaccessible, [])), null), "公共字段不能绕过声明类型的权限");
    }

    /// <summary>访问器证明在模板层进行；每次以给定依据新建模板层。</summary>
    private static FieldAccessor? Prove(InlineEvidence evidence, FieldRef field, TypeRef type, bool write, TypeRef? receiver) =>
        new TemplateRecovery(evidence.Types, evidence.Caller, evidence.Summary, evidence).Accessor(field, type, write, receiver);

    private static void Accessors(Assertions check, ManagedTypes types)
    {
        var owner = Type("AccessStorage", 30);
        var ownerRef = new DefinitionRef(owner, []);
        var field = new FieldDef { Index = 30, Owner = owner, Name = "value", Type = types.Int32,
            Attributes = FieldAttributes.Private, Offset = 16 };
        owner.Fields = [field];
        var fieldRef = new FieldRef(field, ownerRef);
        var hidden = Method(owner, "HiddenRead", 30, MethodAttributes.Private);
        var visible = Method(owner, "Read", 31);
        var inherited = Method(owner, "InheritedRead", 32, MethodAttributes.Family);
        hidden.ReturnType = visible.ReturnType = inherited.ReturnType = types.Int32;
        MethodRecoveryResult Summary(MethodRef method) => new(method, 0, new ManagedBody(method,
            [new(0, [new ManagedReturn(0, new FieldValue(new ArgumentValue(-1, ownerRef, 64), fieldRef, types.Int32, 32))])]), []);
        var caller = new MethodRef(Method(Type("AccessConsumer", 31), "Run", 33), [], []);
        owner.Methods = [hidden];
        var privateOnly = new InlineEvidence(types, caller, Summary);
        check.True(Prove(privateOnly, fieldRef, types.Int32, false, ownerRef) is null, "私有访问器不能证明外部字段读取");
        var receiver = new ArgumentValue(0, ownerRef, 64);
        var pendingRead = new ManagedBody(caller, [new(0, [new ManagedReturn(0,
            new FieldValue(receiver, fieldRef, types.Int32, 32) { Pending = new(0, "待证字段", false) })])]);
        var privateTemplate = new TemplateRecovery(types, caller, Summary, privateOnly)
            .Run(pendingRead, new Dictionary<Variable, PendingConstruction>(), 0);
        check.True(privateTemplate.Holes.Count > 0, "多语句模板不能重新引入被拒绝的私有访问器");
        var privateCall = new ManagedBody(caller, [new(0, [new ManagedCall(0,
            new ManagedInvocation(new MethodRef(hidden, [], []), receiver, [], false), null, false) { Inlined = true }, new ManagedReturn(4, null)])]);
        check.True(new BodyValidation(types, EmissionPolicy.Recovered, caller).Check(privateCall, true) is
            { Kind: EmissionProblemKind.AccessDenied }, "内联证明调用在写出策略下仍须满足权限");
        owner.Methods = [hidden, visible];
        var accessible = new InlineEvidence(types, caller, Summary);
        check.True(Prove(accessible, fieldRef, types.Int64, false, ownerRef) is null, "访问器的字段值类型必须相符");
        check.Equal(visible, Prove(accessible, fieldRef, types.Int32, false, ownerRef)!.Method.Method,
            "跳过私有候选并继续寻找公共访问器，类型不匹配缓存不干扰合法证明");
        var derived = Type("DerivedStorage", 32);
        derived.BaseType = ownerRef;
        var derivedRef = new DefinitionRef(derived, []);
        owner.Methods = [inherited];
        var protectedAccess = new InlineEvidence(types, new MethodRef(Method(derived, "Run", 34), [], []), Summary);
        check.True(Prove(protectedAccess, fieldRef, types.Int32, false, ownerRef) is null, "派生类不能通过基类接收者调用受保护访问器");
        check.True(Prove(protectedAccess, fieldRef, types.Int32, false, derivedRef) is not null,
            "相同字段的派生类接收者独立证明受保护访问器");
        var referenceField = new FieldDef { Index = 33, Owner = owner, Name = "text", Type = types.String, Attributes = FieldAttributes.Private, Offset = 24 };
        var reference = new FieldRef(referenceField, ownerRef);
        visible.ReturnType = types.Object;
        owner.Methods = [visible];
        MethodRecoveryResult Upcast(MethodRef method) => new(method, 0, new(method,
            [new(0, [new ManagedReturn(0, new FieldValue(new ArgumentValue(-1, ownerRef, 64), reference, types.String, 64))])]), []);
        var covariance = new InlineEvidence(types, caller, Upcast);
        check.True(Prove(covariance, reference, types.String, false, ownerRef) is not null, "直接返回字段的引用上转型可证明");
        check.True(Prove(covariance, reference, types.Int64, false, ownerRef) is null, "上转型不能把引用解释成整数");
    }

    private static void ClosedGenericAccess(Assertions check, ManagedTypes types)
    {
        var storage = Type("GenericStorage", 120);
        storage.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        var hidden = new TypeDef { Index = 121, Name = "Hidden", Namespace = "Tests", Assembly = "Other.dll", Token = 0,
            Attributes = TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var instance = new DefinitionRef(storage, [new DefinitionRef(hidden, [])]);
        var field = new FieldRef(new FieldDef { Index = 120, Owner = storage, Name = "count", Type = types.Int32,
            Attributes = FieldAttributes.Private, Offset = 16 }, instance);
        var caller = new MethodRef(Method(storage, "Read", 120), instance.Arguments, []);
        var outsider = new MethodRef(Method(Type("External", 122), "Read", 122), [], []);
        check.True(!ManagedAccess.Type(types, storage, instance), "封闭实参在声明程序集外不可见");
        check.True(ManagedAccess.Field(types, caller, field, instance), "封闭证据体保留定义内的字段权限");
        check.True(!ManagedAccess.Field(types, outsider, field, instance), "外部调用方仍不能访问私有字段");
    }

    private static void StaticAccessorReferences(Assertions check, ManagedTypes types)
    {
        var storage = Type("CacheStorage", 80);
        storage.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        var owner = new DefinitionRef(storage, [types.Int32]);
        var field = new FieldDef { Index = 80, Owner = storage, Name = "value", Type = types.Object,
            Attributes = FieldAttributes.Private | FieldAttributes.Static, Offset = 0 };
        storage.Fields = [field];
        var factory = Type("CacheAccess", 81);
        var getter = Method(factory, "Read", 80, MethodAttributes.Public | MethodAttributes.Static);
        getter.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        getter.ReturnType = types.Object;
        var hidden = Method(factory, "Hidden", 81, MethodAttributes.Private | MethodAttributes.Static);
        hidden.GenericParameters = getter.GenericParameters;
        hidden.ReturnType = types.Object;
        var caller = new MethodRef(Method(Type("CacheConsumer", 82), "Run", 82), [], []);
        var referenced = new MethodRef(getter, [], [types.Int32]);
        var target = new FieldRef(field, owner);
        var extraRead = false;
        MethodRecoveryResult Summary(MethodRef method)
        {
            var value = new StaticFieldValue(new(field, new DefinitionRef(storage, method.MethodArguments)), types.Object, 64);
            var statements = new List<ManagedStatement>();
            if (extraRead) statements.Add(new ManagedAssignment(0, new(new Variable(Storage.Temp(80), 1), types.Object, 64), value));
            statements.Add(new ManagedReturn(4, value));
            return new(method, 0, new(method, [new(0, statements)]), []);
        }
        FieldAccessor? Find(MethodRef[] references, bool write = false) => Prove(new InlineEvidence(types, caller, Summary, references),
            target, types.Object, write, null);
        check.True(Find([]) is null, "没有方法元数据证据时不猜测外部静态入口");
        check.Equal(referenced, Find([referenced])!.Method, "已引用的泛型入口可证明另一类型的静态字段读取");
        check.True(Find([new(getter, [], [types.String])]) is null, "泛型字段定义相同也不能混用不同实例的缓存");
        check.True(Find([new(hidden, [], [types.Int32])]) is null, "外部静态入口仍须满足调用权限");
        check.True(Find([referenced], true) is null, "静态 getter 不能证明字段写入");
        extraRead = true;
        check.True(Find([referenced]) is null, "不能吞掉访问器中未用于返回值的额外读取");
        extraRead = false;
        factory.Methods = [getter, Method(factory, ".cctor", 83, MethodAttributes.Private | MethodAttributes.Static)];
        check.True(Find([referenced]) is null, "纯字段读取体不能证明另一类型的精确静态初始化");
    }

    private static void StaticGenericLocations(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var storage = Type("GenericStatics", 83);
        storage.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        storage.Fields = [new() { Index = 83, Owner = storage, Name = "items",
            Type = new ArrayRef(new GenericParameterRef("T", false, 0), 1),
            Attributes = FieldAttributes.Public | FieldAttributes.Static, Offset = 0 }];
        var definition = Method(Type("StaticConsumer", 84), "Read", 84, MethodAttributes.Public | MethodAttributes.Static);
        definition.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        var method = new MethodRef(definition, [], [types.Int32]);
        var function = new MachineFunction { Entry = 0, Range = new(0, 4, CodeRegion.Managed, default), Blocks = [new(0) { Statements = [new Return(0)] }] };
        var values = ValueModel.Build(function, new EmptyEnvironment());
        var oracle = new TypeOracle(types, facts, method, _ => throw new NotSupportedException(), values);
        // 元数据实体以定义的类型参数表达，L2 之后由泛型上下文代入当前实例。
        var symbol = values.Syms.Entity(new Symbol(SymbolKind.StaticFields,
            GenericContext.Instantiate(new DefinitionRef(storage, [new GenericParameterRef("T", true, 0)]), method)!));
        var location = oracle.Locate(symbol, 64);
        check.True(location?.Owner?.Equals(new DefinitionRef(storage, [types.Int32])) == true,
            "静态字段的元数据类型代入当前方法实参");
        check.True(location?.Type.Equals(new ArrayRef(types.Int32, 1)) == true,
            "封闭静态字段读取保留数组元素类型");
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

    private static void PackedPhiSlices(Assertions check)
    {
        var syms = new SymTable();
        var merge = new Block(8);
        MachineFunction.AddEdge(new Block(0), merge);
        MachineFunction.AddEdge(new Block(4), merge);
        var first = syms.Arg(0, 96);
        var second = syms.Arg(1, 96);
        var phi = syms.Phi(merge, "packed", 128);
        syms.SetSource(phi, 0, syms.Widen(syms.Slice(first, 32, 32), 128));
        syms.SetSource(phi, 1, syms.Widen(syms.Slice(second, 32, 32), 128));
        var projected = syms.Slice(phi, 0, 32);
        check.True(projected is PhiSym { Width: 32 } p && p.Sources.SequenceEqual(new[] { syms.Slice(first, 32, 32), syms.Slice(second, 32, 32) }),
            "合流的寄存器片还原为原结构体字段的同宽合流");
        syms.SetSource(phi, 1, syms.Widen(syms.Slice(second, 64, 32), 128));
        check.True(projected is PhiSym updated && updated.Sources[1] == syms.Slice(second, 64, 32), "后填入的合流来源同步更新片投影");
        var scalar = syms.Phi(merge, "scalar", 64);
        syms.SetSource(scalar, 0, syms.Arg(2, 64));
        syms.SetSource(scalar, 1, syms.Arg(3, 64));
        check.True(syms.Slice(scalar, 0, 16) is SliceSym, "没有搬运片证据时不额外拆分标量合流");
    }

    private static void JoinedPhiSlices(Assertions check)
    {
        foreach (var crossed in new[] { false, true })
        {
            var syms = new SymTable();
            var merge = new Block(8);
            MachineFunction.AddEdge(new Block(0), merge);
            MachineFunction.AddEdge(new Block(4), merge);
            var a = syms.Arg(0, 128);
            var b = syms.Arg(1, 128);
            var low = syms.Phi(merge, "low", 64);
            var high = syms.Phi(merge, "high", 64);
            syms.SetSource(low, 0, syms.Slice(a, 0, 64));
            syms.SetSource(low, 1, syms.Slice(b, 0, 64));
            syms.SetSource(high, 0, syms.Slice(crossed ? b : a, 64, 64));
            syms.SetSource(high, 1, syms.Slice(crossed ? a : b, 64, 64));
            var result = syms.Concat(low, high);
            check.True(crossed ? result is ConcatSym : result is PhiSym phi && phi.Sources.SequenceEqual(new[] { a, b }),
                crossed ? "不同入边的片不能冒充完整返回值" : "分段返回在对应入边上还原为整体合流");
            if (!crossed)
            {
                syms.SetSource(high, 1, syms.Slice(a, 64, 64));
                check.True(result is PhiSym changed && changed.Sources[1] is ConcatSym,
                    "来源变化后整体合流保留真实拼接，不沿用失效的完整值证据");
            }
        }
    }

    private static void MathImports(Assertions check, ManagedTypes types)
    {
        var sine = types.MathImport("sinf")!;
        check.True(sine.Method.NativeImport?.EntryPoint == "sinf" && sine.Method.ReturnType == types.Single
            && sine.Method.Parameters.Select(p => p.Type).SequenceEqual([types.Single]), "单精度导入保留精确入口与签名");
        check.True(ReferenceEquals(sine, types.MathImport("sinf")), "同一数学导入共享方法身份");
        check.True(types.MathImport("atan2")!.Method.Parameters.Select(p => p.Type).SequenceEqual([types.Double, types.Double]), "双精度二元导入不改变精度");
        check.True(types.MathImport("ldexpf")!.Method.Parameters.Select(p => p.Type).SequenceEqual([types.Single, types.Int32]), "整数指数保留独立寄存器类型");
        check.True(types.MathImport("unknown") is null && types.MathImport("sincosf") is null, "未知签名与指针出参不当作标量导入");
        var pair = types.SinCosImport()!;
        check.True(ManagedTypes.IsVoid(pair.Method.ReturnType) && pair.Method.NativeImport?.EntryPoint == "sincosf"
            && pair.Method.Parameters.Select(p => p.Type).SequenceEqual([types.Single, new ByRefRef(types.Single), new ByRefRef(types.Single)]),
            "正余弦保留一个浮点输入和两个独立出参");
        check.True(RuntimeOps.Of(OpKind.ImportOutPair)!.ResultWidths!(new Call(0, CallKind.Direct, Expr.C(0, 64))).SequenceEqual([32, 32]),
            "正余弦结果各占 32 位，不读取寄存器未定义高位");
        var call = new Call(0, CallKind.Direct, Expr.C(100, 64))
        {
            Op = new(OpKind.Import, "ldexpf"), Sources = [Storage.Gpr(0), Storage.Vec(0)],
            Arguments = [new Use(new Variable(Storage.Gpr(0), 0), 64), new Use(new Variable(Storage.Vec(0), 0), 128)],
        };
        var block = new Block(0) { Statements = [call, new Return(4)] };
        var function = new MachineFunction { Entry = 0, Range = new(0, 8, CodeRegion.Managed, default), Blocks = [block] };
        MathImportNormalizer.Run(function, () => new Variable(Storage.Temp(0), 1));
        var normalized = block.Statements.OfType<Call>().Single();
        check.True(RuntimeOps.Of(OpKind.Import)!.ResultWidths!(normalized).SequenceEqual([32]), "单精度数学调用的结果只有低 32 位有效");
        check.True(normalized.Sources.SequenceEqual([Storage.Vec(0), Storage.Gpr(0)]) && normalized.Arguments.All(a => a.Width == 32),
            "浮点与整数参数按各自寄存器取有效位并恢复声明次序");
    }

    private static void PromotedDelegates(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var type = new DefinitionRef(types.CorlibDefinition("System.Action")!, []);
        var root = new Use(new Variable(Storage.Local(0, 64), 1), 64);
        var other = new Use(new Variable(Storage.Local(1, 64), 1), 64);
        Expr Field(Expr receiver, ulong offset) => new Load(new Binary(BinOp.Add, receiver, Expr.C(offset, 64), 64), 64);
        foreach (var variant in new[] { "proven", "unknown-type", "different-receiver", "different-method", "memory-effects" })
        {
            var call = new Call(4, CallKind.Indirect, Field(root, 0x18))
            {
                Op = new(OpKind.CallDelegate, null),
                Sources = [Storage.Gpr(0), Storage.Gpr(1)],
                Arguments = [Field(variant == "different-receiver" ? other : root, 0x40), Field(variant == "different-method" ? other : root, 0x28)],
                Memory = variant == "memory-effects" ? [new CellAccess(Storage.Local(0, 64), 0, 64, 0, 0, 64, true)] : [],
            };
            var block = new Block(0) { Statements = [call, new Return(8)] };
            var function = new MachineFunction { Entry = 0, Range = new(0, 12, CodeRegion.Managed, default), Blocks = [block] };
            var report = new IdiomResult();
            report.Hit(Template.DelegateCall);
            DelegateCallNormalizer.Run(facts, function, report, e => variant != "unknown-type" && e == root ? type : null);
            var result = block.Statements.OfType<Call>().Single();
            check.Equal(variant == "proven", result.Resolved is not null && result.DelegateReceiver == root,
                $"提升后委托类型仍须满足同根调用证据 {variant}");
        }
    }

    private static void CleanupDispatch(Assertions check)
    {
        StateDispatch? Read(Cond comparison, ulong bound, ulong target = 100)
        {
            var receiver = new Use(new Variable(Storage.Gpr(0), 0), 64);
            var state = new Load(new Binary(BinOp.Add, receiver, Expr.C(16, 64), 64), 32);
            var condition = new Logical(true,
                new Compare(comparison, new Binary(BinOp.Sub, state, Expr.C(1, 32), 32), Expr.C(bound, 32)),
                new Compare(Cond.Ne, new Binary(BinOp.Add, state, Expr.C(3, 32), 32), Expr.C(0, 32)));
            var entry = new Block(0) { Statements = [new Branch(0, condition, 8, 4)] };
            var dispose = new Block(4) { Statements = [new Call(4, CallKind.Tail, Expr.C(target, 64))
                { Arguments = [receiver], StackPointer = new FrameAddress(-32) }] };
            var done = new Block(8) { Statements = [new Return(8)] };
            var function = new MachineFunction { Entry = 0, Range = new(0, 12, CodeRegion.Managed, default), Blocks = [entry, dispose, done] };
            return StateDispatch.Read(function, c => c);
        }
        var dispatch = Read(Cond.Uge, 4);
        check.True(dispatch is not null && Read(Cond.Ugt, 3) is { } equivalent && dispatch.Same(equivalent), "有符号状态的无符号范围比较按精确分区证明清理分派等价");
        check.True(dispatch is not null && dispatch.Otherwise.Length == 0 && new uint[] { 1, 4, unchecked((uint)-3) }
            .All(s => dispatch.Cases[s].SequenceEqual(new ulong[] { 100 })), "范围端点及负状态均保留清理调用");
        check.True(dispatch is not null && Read(Cond.Uge, 5) is { } wider && !dispatch.Same(wider), "清理状态范围不同不能视为等价");
        check.True(dispatch is not null && Read(Cond.Uge, 4, 104) is { } other && !dispatch.Same(other), "清理调用目标不同不能视为等价");
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
        method.Method.Parameters = [new("pair", pair, 0, null, false), new("scalar", types.Int64, 0, null, false)];
        var packed = values.Syms.Arg(0, 64);
        check.True(oracle.EnclosingScalar(new SliceSym(packed, 33, 31)) is { Low: 1, Type: var pieceType } && pieceType == types.Single,
            "结构体字段内部的位片按完整浮点字段的位型解释");
        check.True(oracle.EnclosingScalar(new SliceSym(packed, 24, 16)) is null, "跨字段位片不能假定为一个标量");
        check.True(oracle.EnclosingScalar(new SliceSym(packed, 32, 32)) is null, "完整字段不重复拆成自身的位片");
        var merge = new Block(8);
        MachineFunction.AddEdge(new Block(0), merge);
        var whole = values.Syms.Phi(merge, "typed-whole", 64);
        var integerWhole = values.Syms.Phi(merge, "integer-whole", 64);
        values.Syms.SetSource(integerWhole, 0, values.Syms.Const(1, 64));
        var integerPiece = new PhiSym(merge, "integer-piece", 31) { Projection = (integerWhole, 0) };
        check.True(oracle.ProjectedScalar(integerPiece) is { Low: 0, Type: var carrier } && carrier == types.Int64,
            "非标准位宽的合流投影复用完整整数载体");
        var vectorWhole = values.Syms.Phi(merge, "vector-whole", 128);
        check.True(oracle.ProjectedScalar(new PhiSym(merge, "vector-piece", 31) { Projection = (vectorWhole, 0) }) is null,
            "未知向量的投影不能假定为整数");
        var unknownWhole = values.Syms.Phi(merge, "unknown-whole", 64);
        check.True(oracle.ProjectedScalar(new PhiSym(merge, "unknown-piece", 31) { Projection = (unknownWhole, 0) }) is null,
            "没有完整来源的合流不能借用整数载体");
        values.Syms.SetSource(whole, 0, values.Syms.Arg(0, 64));
        var field = new PhiSym(merge, "field", 32) { Projection = (whole, 32) };
        check.True(oracle.ProjectedField(field) is { } projected && projected.Whole == whole && projected.Type == types.Single
            && projected.Path.Count == 1, "结构体字段投影保留已知类型的整体合流");
        var scalar = values.Syms.Phi(merge, "scalar-whole", 64);
        values.Syms.SetSource(scalar, 0, values.Syms.Arg(1, 64));
        check.True(oracle.ProjectedField(new PhiSym(merge, "scalar-piece", 32) { Projection = (scalar, 0) }) is null,
            "标量投影不借用结构体整体视图");
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
        var nested = Structure("Nested", 68, 16, false, (types.Int64, 0), (pair, 8));
        var projection = types.Project(nested, 96, 32);
        check.True(projection is { Bit: 96, Width: 32, Path.Count: 2 } && projection.Type.Equals(types.Single),
            "嵌套字段的投影统一使用值起点的位偏移");
        check.True(projection is not null && types.Project(nested, projection.Path) is { } byPath
            && byPath.Bit == projection.Bit && byPath.Width == projection.Width && byPath.Type.Equals(projection.Type),
            "路径投影与位范围投影得到相同字段");
        check.True(types.Project(nested, 88, 16) is null && types.Project(padded, 32, 32) is null,
            "字段投影拒绝跨字段和尾部填充");
        check.True(types.Project(nested, 64, 64) is { Path.Count: 1, Type: var nestedType } && nestedType.Equals(pair),
            "完整嵌套字段保留整体投影");
        check.True(types.IntegerPieces(integer) is { Count: 1 } && types.IntegerPieces(reference) is null,
            "整数打包的覆盖证明不将引用按整数位读取");
        check.True(types.IntegerPieces(padded) is null && types.IntegerPieces(overlap) is null,
            "整数打包拒绝填充与重叠字段");
        var assembled = oracle.Aggregate(values.Syms.Concat([values.Syms.Const(0, 64), values.Syms.Const(0x80000000_3f800000, 64)]), nested);
        check.True(assembled is { Whole: null, Fields.Count: 2 } && assembled.Fields[0].Projection.Bit == 64
            && assembled.Fields[1].Value is ConstSym { Value: 0x80000000 }, "结构体组合计划保留嵌套浮点位型与负零");
        check.True(oracle.Aggregate(values.Syms.Const(1, 32), pair) is null, "不足的位不能组成完整字段");
        var undefined = oracle.Aggregate(values.Syms.Concat([values.Syms.Const(0, 32), values.Syms.Undef(32)]), pair);
        check.True(undefined is { Fields.Count: 1 } && undefined.Fields[0].Value is UndefSym,
            "组合计划只省略已知零，未定义位继续交给下降报洞");
        var pairFields = types.Projections(pair).ToArray();
        var parentField = types.Fields(nested).Last();
        var one = new ConstantValue(0x3f800000, types.Single, 32);
        var two = new ConstantValue(0x40000000, types.Single, 32);
        var innerValue = new ComposedValue(pair, [(pairFields[0].Path, one), (pairFields[1].Path, two)]);
        var nestedValue = new ComposedValue(nested, [(parentField.Path, innerValue)]);
        var selected = ManagedProjections.Project(types, nestedValue, types.Project(nested, 96, 32)!, f => f);
        check.True(selected?.Value == two && selected.Discarded.SequenceEqual([one]),
            "完整嵌套值与叶子组成共享字段投影，并保留其他字段的求值义务");
        var zero = ManagedProjections.Project(types, new ComposedValue(pair, []), pairFields[0], f => f);
        check.True(zero?.Value is ConstantValue { Bits: 0 }, "initobj 未覆盖的字段投影为已知默认值");
        var flat = new ComposedValue(nested, types.Projections(nested).Skip(1).Select((p, i) => (p.Path, (ManagedValue)(i == 0 ? one : two))).ToArray());
        check.True(ManagedProjections.Project(types, flat, parentField, f => f)?.Value is ComposedValue { Leaves.Count: 2 },
            "分散叶子可以投影回嵌套整体");
        var repeated = innerValue with { Leaves = [.. innerValue.Leaves, (pairFields[0].Path, two)] };
        check.True(ManagedProjections.Project(types, repeated, pairFields[0], f => f) is null,
            "重叠写入不能按字段集合推导值");
        var unavailable = Structure("UnboundLayout", 169, 8, false);
        unavailable.Definition.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        check.True(oracle.Aggregate(values.Syms.Const(0, 64), unavailable) is null,
            "没有布局的结构体不能因字段枚举为空而组成默认值");
        var empty = Structure("EmptyValue", 170, 1, false);
        check.True(oracle.Aggregate(values.Syms.Undef(8), empty) is { Fields.Count: 0 },
            "已知布局的空结构体不观察填充位");
    }

    private static void ConstructorStoreOrder(Assertions check, ManagedTypes types)
    {
        var parent = Type("BaseStorage", 70);
        parent.BaseType = types.Object;
        var parentRef = new DefinitionRef(parent, []);
        var child = Type("ChildStorage", 71);
        child.BaseType = parentRef;
        var childRef = new DefinitionRef(child, []);
        FieldDef Field(TypeDef owner, int index, int offset) => new() { Index = index, Owner = owner, Name = $"f{index}",
            Type = types.Int32, Offset = offset, Attributes = FieldAttributes.Public };
        var first = Field(parent, 70, 16);
        var second = Field(parent, 71, 20);
        var own = Field(child, 72, 24);
        parent.Fields = [first, second];
        child.Fields = [own];
        var baseCtor = new MethodRef(Method(parent, ".ctor", 70), [], []);
        parent.Methods = [baseCtor.Method];
        var childCtor = new MethodRef(Method(child, ".ctor", 71), [], []);
        child.Methods = [childCtor.Method];
        var objectCtor = new MethodRef(types.Object.Definition.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0), [], []);
        ManagedCall Initialize(TypeRef owner) => new(0, new(objectCtor, new ArgumentValue(-1, owner, 64), [], false), null, false);
        ManagedStore Store(TypeRef owner, FieldDef field, int value) => new((ulong)field.Index,
            new FieldValue(new ArgumentValue(-1, owner, 64), new(field, field.Owner == parent ? parentRef : childRef), types.Int32, 32),
            new ConstantValue((ulong)value, types.Int32, 32));
        var template = new ManagedBody(baseCtor, [new(0, [Initialize(parentRef), Store(parentRef, first, 1), Store(parentRef, second, 2), new ManagedReturn(100, null)])]);
        MethodRecoveryResult? Summary(MethodRef method) => method == baseCtor ? new(baseCtor, 0, template, []) : null;
        ManagedBody Recover(bool interveningRead, bool prelude = false)
        {
            var middle = Store(childRef, own, 3);
            if (interveningRead) middle = middle with { Value = new FieldValue(new ArgumentValue(-1, childRef, 64), new(second, parentRef), types.Int32, 32) };
            var body = new ManagedBody(childCtor, [new(0, prelude
                ? [middle, Store(childRef, first, 1), Store(childRef, second, 2), Initialize(childRef), new ManagedReturn(100, null)]
                : [Initialize(childRef), Store(childRef, first, 1), middle, Store(childRef, second, 2), new ManagedReturn(100, null)])]);
            return new TemplateRecovery(types, childCtor, Summary, new(types, childCtor, Summary))
                .Run(body, new Dictionary<Variable, PendingConstruction>(), 0).Body;
        }
        bool CallsBase(ManagedBody body) => body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Inlined && c.Invocation.Method == baseCtor);
        check.True(CallsBase(Recover(false)), "独立本类写入可移到完整基类构造之后");
        check.True(!CallsBase(Recover(true)), "依赖字段读取的写入不得重排越过基类赋值");
        template = new(baseCtor, [new(0, [Store(parentRef, first, 1), Store(parentRef, second, 2), Initialize(parentRef), new ManagedReturn(100, null)])]);
        check.True(CallsBase(Recover(false, true)), "基类初始化在父类调用之前时，本类写入留在完整模板之前");
    }

    private static void ConstructorPreludeStores(Assertions check, ManagedTypes types)
    {
        var owner = Type("InitializedStorage", 881);
        owner.BaseType = types.Object;
        var type = new DefinitionRef(owner, []);
        var field = new FieldDef { Index = 881, Owner = owner, Name = "value", Type = types.Int32, Offset = 16, Attributes = FieldAttributes.Public };
        var second = new FieldDef { Index = 882, Owner = owner, Name = "second", Type = types.Int32, Offset = 20, Attributes = FieldAttributes.Public };
        owner.Fields = [field, second];
        var constructor = new MethodRef(Method(owner, ".ctor", 881), [], []);
        owner.Methods = [constructor.Method];
        var parent = new MethodRef(types.Object.Definition.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0), [], []);
        ManagedStore Store(ManagedValue receiver, ulong value) => new(4, new FieldValue(receiver, new(field, type), types.Int32, 32), new ConstantValue(value, types.Int32, 32));
        ManagedStore Other(ManagedValue receiver) => new(5, new FieldValue(receiver, new(second, type), types.Int32, 32), new ConstantValue(9, types.Int32, 32));
        ManagedCall Initialize(ManagedValue receiver) => new(8, new(parent, receiver, [], false), null, false);
        var self = new ArgumentValue(-1, type, 64);
        var template = new ManagedBody(constructor, [new(0, [Store(self, 7), Other(self), Initialize(self), new ManagedReturn(12, null)])]);
        MethodRecoveryResult? Summary(MethodRef method) => method == constructor ? new(method, 0, template, []) : null;
        var caller = new MethodRef(Method(Type("InitializedConsumer", 882), "Create", 882), [], []);
        caller.Method.ReturnType = type;
        var local = new LocalValue(new(Storage.Temp(881), 1), type, 64);
        foreach (var correct in new[] { true, false })
        {
            var body = new ManagedBody(caller, [new(0, [Other(local), Store(local, correct ? 7UL : 8UL), Initialize(local), new ManagedReturn(12, local)])]);
            var recovered = new TemplateRecovery(types, caller, Summary, new(types, caller, Summary)).Run(body,
                new Dictionary<Variable, PendingConstruction> { [local.Variable] = new(8, type, parent) }, 0);
            check.Equal(correct, recovered.Holes.Count == 0 && recovered.Body.Blocks.SelectMany(b => b.Statements)
                .OfType<ManagedAssignment>().Any(a => a.Value is NewObjectValue { Transparent: true }), "基类调用前的字段初始化须与构造模板一致");
            if (!correct) check.True(recovered.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>()
                .Single().Value is HoleValue, "构造证明失败时接收者保留缺口");
        }
    }

    private static void ConstructorContracts(Assertions check, ManagedTypes types)
    {
        var owner = Type("ConstructorContracts", 180);
        owner.BaseType = types.Object;
        var ownerType = new DefinitionRef(owner, []);
        var ctor = new MethodRef(Method(owner, ".ctor", 180), [], []);
        ctor.Method.Parameters = [new("value", types.Int32, 0, null, false)];
        owner.Methods = [ctor.Method];
        var field = new FieldDef { Index = 180, Owner = owner, Name = "value", Type = types.Int32,
            Offset = 16, Attributes = FieldAttributes.Public };
        owner.Fields = [field];
        var self = new ArgumentValue(-1, ownerType, 64);
        var baseCtor = MethodRef.Open(types.Object.Definition.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0));
        var initialize = new ManagedCall(4, new(baseCtor, self, [], false), null, false);
        var ret = new ManagedReturn(8, null);
        ManagedBody Body(ManagedValue value) => new(ctor, [new(0, [
            new ManagedStore(0, new FieldValue(self, new(field, ownerType), types.Int32, 32), value), initialize, ret])]);
        EmissionProblem? Cil(ManagedBody body) => new BodyValidation(types, EmissionPolicy.Recovered, body.Method).Check(body, true);
        var parameter = Body(new ArgumentValue(0, types.Int32, 32));
        check.True(Cil(parameter) is null, "初始化前写本类字段可以依赖参数，CIL 检查不施加字段初始化器限制");
        check.True(SourceSuitability.Check([parameter]).GetValueOrDefault(parameter)?.Kind == EmissionProblemKind.SourceForm,
            "依赖参数的前导写入单独报告为源码形式限制");
        var constant = Body(new ConstantValue(1, types.Int32, 32));
        check.True(Cil(constant) is null && SourceSuitability.Check([constant]).Count == 0,
            "普通字段初始化器同时通过两层检查");
        var uninitialized = new ManagedBody(ctor, [new(0, [ret])]);
        check.True(Cil(uninitialized)?.Kind == EmissionProblemKind.Constructor
            && SourceSuitability.Check([uninitialized])[uninitialized].Kind == EmissionProblemKind.Constructor,
            "分离源码限制不允许未初始化 this 的返回");
        var twice = new ManagedBody(ctor, [new(0, [initialize, initialize, ret])]);
        check.True(Cil(twice)?.Kind == EmissionProblemKind.Constructor, "重复初始化仍是 CIL 写出问题");
        var read = Body(new FieldValue(self, new(field, ownerType), types.Int32, 32));
        check.True(Cil(read)?.Kind == EmissionProblemKind.Constructor, "初始化前读取 this 仍被拒绝");
        var other = new MethodRef(Method(owner, ".ctor", 181), [], []);
        owner.Methods = [ctor.Method, other.Method];
        var different = Body(new ConstantValue(2, types.Int32, 32)) with { Method = other };
        check.True(Cil(constant) is null && Cil(different) is null, "不同构造体的前导写入不影响各自的 CIL 合法性");
        check.True(SourceSuitability.Check([constant, different]).Count == 2, "跨构造函数的字段初始化器一致性属于源码检查");
    }

    private static void Effects(Assertions check, ManagedTypes types)
    {
        check.True(!EffectSummary.Unknown.CanDiscard && EffectSummary.Unknown.InvalidatesMemory,
            "未知效果同时阻止删除并使内存快照失效");
        check.True(EffectSummary.Access(MemoryKind.Local).CanDiscard && !EffectSummary.Access(MemoryKind.Local).CanDuplicate,
            "无异常读取可以丢弃，但不能跨写入重复求值");
        check.True(!RuntimeOps.Of(OpKind.MemoryBarrier)!.Behavior.CanDiscard
            && RuntimeOps.Of(OpKind.MemoryBarrier)!.Behavior.InvalidatesMemory, "内存屏障独立记录顺序效果");
        check.True(RuntimeOps.Of(OpKind.RunClassConstructor)!.Behavior.InvalidatesMemory
            && !RuntimeOps.Of(OpKind.NewObject)!.Behavior.CanDiscard, "初始化与分配不能当作纯操作");
        var zero = new ConstantValue(0, types.Int32, 32);
        var div = new BinaryValue(BinOp.SDiv, zero, zero, types.Int32, 32);
        check.True(ManagedEffects.Value(div).MayThrow, "整数除法的异常参与效果合并");
        var owner = Type("EffectStorage", 190);
        var ownerType = new DefinitionRef(owner, []);
        var field = new FieldDef { Index = 190, Owner = owner, Name = "child", Type = ownerType, Offset = 16, Attributes = FieldAttributes.Public };
        var read = new FieldValue(new ArgumentValue(0, ownerType, 64), new(field, ownerType), ownerType, 64);
        check.True(ManagedEffects.Value(read).Exceptions == ExceptionEffect.NullReference,
            "托管字段读取与机器位置共用判空异常分类");
        var address = new AddressValue(read with { Receiver = read });
        check.True((ManagedEffects.Value(address).Kinds & EffectKind.Read) != 0,
            "取址只免去目标读取，不能去掉接收者求值中的读取");
        check.True(MemoryFootprint.MayAlias(null, MemoryFootprint.Of(read)), "未知位置不能证明不别名");
        check.True(MemoryFootprint.MayAlias(MemoryFootprint.Of(read), MemoryFootprint.Of(read)), "同一字段位置可能别名");
        var staticField = new StaticFieldValue(new(field, ownerType), ownerType, 64);
        check.True(!ManagedEffects.Value(staticField).CanDiscard && ManagedEffects.Value(staticField).InvalidatesMemory,
            "静态读取的类初始化不能在内联证明中丢弃");
    }

    private static void TypeUses(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var abi = new ManagedAbi(facts.Layouts);
        var shapes = new CallShapes(facts, abi, (_, _) => false);
        (TypeUsePlan Plan, TypeOracle Oracle, ValueModel Values) Analyze(MethodRef method, MachineFunction function)
        {
            var signature = abi.Machine(method, out _)!;
            var environment = new MethodEnvironment(method, signature, shapes);
            var values = ValueModel.Build(function, environment);
            var oracle = new TypeOracle(types, facts, method, environment.Shape, values);
            var analysis = new MethodAnalysis(method, 0, signature, function, new(), new([]), values) { Environment = environment };
            return (new TypeUseAnalysis(analysis, oracle).Run(), oracle, values);
        }
        var method = MethodRef.Open(Method(Type("TypeUseConsumer", 200), "Choose", 200, MethodAttributes.Public | MethodAttributes.Static));
        method.Method.ReturnType = types.Double;
        var left = new Variable(Storage.Gpr(2), 1);
        var right = new Variable(Storage.Gpr(2), 2);
        var joined = new Variable(Storage.Gpr(2), 3);
        var entry = new Block(0) { Statements = [new Branch(0, Expr.C(1, 1), 4, 8)] };
        var a = new Block(4) { Statements = [new Define(4, left, Expr.C(0x3ff0000000000000, 64)), new Jump(4, 12)] };
        var b = new Block(8) { Statements = [new Define(8, right, Expr.C(0x4000000000000000, 64)), new Jump(8, 12)] };
        var end = new Block(12) { Statements = [new Phi(12, joined, [left, right]), new Return(16) { Pieces = [new(0, new Use(joined, 64))] }] };
        MachineFunction.AddEdge(entry, a); MachineFunction.AddEdge(entry, b);
        MachineFunction.AddEdge(a, end); MachineFunction.AddEdge(b, end);
        var function = new MachineFunction { Entry = 0, Range = new(0, 20, CodeRegion.Managed, default), Blocks = [entry, a, b, end] };
        var before = function.Blocks.SelectMany(block => block.Statements).ToArray();
        var result = Analyze(method, function);
        check.Equal(TypeSolveState.Stable, result.Plan.State, "类型用途分析独立收敛");
        check.Equal(types.Double, result.Oracle.TypeOf(result.Values.Of(joined)), "返回签名将无自然类型的常量合流约束为 double");
        check.True(before.SequenceEqual(function.Blocks.SelectMany(block => block.Statements)), "约束收集不改写机器图");

        method.Method.ReturnType = types.Int32;
        method.Method.Parameters = [new("source", new ByRefRef(types.Int32), 0, null, false)];
        var loaded = new Variable(Storage.Gpr(2), 1);
        var read = new Define(0, loaded, new Load(new Use(new Variable(Storage.Gpr(0), 0), 64), 32));
        var unused = new Define(4, new Variable(Storage.Gpr(3), 1), new Load(Expr.C(64, 64), 32));
        var block = new Block(0) { Statements = [read, unused, new Return(8) { Pieces = [new(0, new Use(loaded, 32))] }] };
        var reads = Analyze(method, new() { Entry = 0, Range = new(0, 12, CodeRegion.Managed, default), Blocks = [block] });
        check.True(reads.Plan.Materialized.Count == 1 && ReferenceEquals(reads.Plan.Materialized.Single().Site, read),
            "读取落点来自实际值用途，不收集未使用读取");
        var op = new OpSym(new Operator(OperatorKind.Binary, (byte)BinOp.Shl), [reads.Values.Syms.Arg(0, 64), reads.Values.Syms.Const(1, 32)], 64);
        check.Equal(types.Int32, reads.Oracle.OperationTypes(op, types.Int64).Inputs[1], "移位量与结果类型分别约束");
        var arrayCall = new Call(0, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.NewArray, new ArrayRef(types.Int32, 1)) };
        var inputs = RuntimeOps.Of(OpKind.NewArray)!.Inputs!(arrayCall, [reads.Values.Syms.Const(0, 64), reads.Values.Syms.Const(3, 32)], reads.Oracle);
        check.True(inputs.Count == 1 && inputs[0].Type == types.Int32, "运行时用途描述排除类元数据并约束数组长度");
        var test = arrayCall with { Op = new(OpKind.IsInst, types.Object) };
        check.True(RuntimeOps.Of(OpKind.IsInst)!.Inputs!(test, [reads.Values.Syms.Arg(0, 64)], reads.Oracle).Count == 1,
            "类型实体已在操作数中时，isinst 的单个值实参仍有类型用途");
    }

    private sealed class EmptyEnvironment : IValueEnvironment
    {
        public Sym? Entry(SymTable syms, Storage storage) => null;
        public Sym? CallResult(SymTable syms, Call call, int index, IReadOnlyList<Sym> arguments) => null;
        public Sym? MetadataRead(SymTable syms, Sym address, int width) => null;
    }

    private static void ReturnedTemplates(Assertions check, ManagedTypes types)
    {
        var owner = Type("PairStorage", 40);
        var ownerRef = new DefinitionRef(owner, []);
        FieldDef Field(string name, int index) => new() { Index = index, Owner = owner, Name = name,
            Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 16 + (index - 40) * 4 };
        var first = Field("first", 40);
        var second = Field("second", 41);
        var other = Field("other", 42);
        owner.Fields = [first, second, other];
        var definition = Method(owner, "Sum", 40);
        definition.ReturnType = types.Int32;
        owner.Methods = [definition];
        var method = new MethodRef(definition, [], []);
        var self = new ArgumentValue(-1, ownerRef, 64);
        FieldValue Read(ManagedValue receiver, FieldDef field) => new(receiver, new FieldRef(field, ownerRef), types.Int32, 32);
        var template = new ManagedBody(method, [new(0, [new ManagedReturn(0,
            new BinaryValue(BinOp.Add, Read(self, first), Read(self, second), types.Int32, 32))])]);
        MethodRecoveryResult? Summary(MethodRef requested) => requested == method ? new(method, 0, template, []) : null;
        var callerDefinition = Method(Type("PairConsumer", 41), "Run", 41);
        callerDefinition.ReturnType = types.Int32;
        var caller = new MethodRef(callerDefinition, [], []);
        var receiver = new ArgumentValue(0, ownerRef, 64);
        var a = new LocalValue(new Variable(Storage.Temp(40), 1), types.Int32, 32);
        var b = new LocalValue(new Variable(Storage.Temp(41), 1), types.Int32, 32);
        var unused = new LocalValue(new Variable(Storage.Temp(42), 1), types.Int32, 32);
        TemplateResult Run(bool unrelated)
        {
            var statements = new List<ManagedStatement> { new ManagedAssignment(0, a, Read(receiver, first) with { Pending = new(0, "待证字段", false) }) };
            if (unrelated) statements.Add(new ManagedAssignment(2, unused, Read(new ArgumentValue(1, ownerRef, 64), other)));
            statements.Add(new ManagedAssignment(4, b, Read(receiver, second) with { Pending = new(4, "待证字段", false) }));
            statements.Add(new ManagedReturn(8, new BinaryValue(BinOp.Add, a, b, types.Int32, 32)));
            var fields = new InlineEvidence(types, caller, Summary);
            return new TemplateRecovery(types, caller, Summary, fields).Run(new(caller, [new(0, statements)]), new Dictionary<Variable, PendingConstruction>(), 0);
        }
        var recovered = Run(false);
        check.True(recovered.Holes.Count == 0 && recovered.Body.Blocks.SelectMany(b => b.Statements)
            .OfType<ManagedCall>().Any(c => c.Inlined && c.Tail && c.Invocation.Method == method), "分段读取的返回表达式可证明为完整取值调用");
        var interleaved = Run(true);
        check.True(interleaved.Body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
            .OfType<FieldValue>().Count(f => f.Field.Field == other) == 1, "无关对象上的读取必须保留，即使后续区域可以独立证明");
    }

    private static void UnusedCallStacks(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var lifter = new Cpp2CS.Machine.Lifting.FunctionLifter(facts);
        foreach (var variant in new[] { "registers", "stack-argument", "stack-methodinfo", "unknown" })
        {
            var frame = new FrameAddress(-16);
            var dynamicSp = new Variable(Storage.Temp(880), 1);
            var entry = new Use(new Variable(Storage.Gpr(0), 0), 64);
            var call = new Call(8, CallKind.Direct, Expr.C(1, 64)) { StackPointer = new Use(dynamicSp, 64) };
            var function = new MachineFunction { Entry = 0, Range = new(0, 16, CodeRegion.Managed, default), Blocks = [new(0)
                { Statements = [new Define(0, dynamicSp, new Binary(BinOp.Sub, frame, entry, 64)), new Store(4, frame, entry), call,
                    new Return(12) { Pieces = [new(0, new Load(frame, 64))] }] }] };
            var input = new MachineValue(0, types.Int64, Transfer.Value,
                [new(variant == "stack-argument" ? Storage.Slot(0) : Storage.Gpr(1), 64, 0)], 8, MemoryAccess.None);
            var callee = variant == "unknown" ? null : new MachineSignature([input], null,
                variant == "stack-methodinfo" ? new(Storage.Slot(0), 64, 0) : null, variant.StartsWith("stack-") ? 8 : 0);
            var signature = new MachineSignature([], null, null, 0);
            var result = Cpp2CS.Recovery.Memory.MemoryPromotion.Run(function, signature, c => new(c, [], callee),
                new ManagedAbi(facts.Layouts), lifter.Calls, lifter.Machine.Convention.StackPointer);
            check.True(result.TryGet(out var layout, out _) && layout.Cells.All(c => c.Promoted) == (variant == "registers")
                && (function.EntryBlock.Statements.OfType<Call>().Single().StackPointer is null) == (variant == "registers"),
                $"调用栈指针按完整签名保留 {variant}");
        }
    }

    private static void ConstantMemoryCopies(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var destination = new FrameAddress(-24);
        var source = new FrameAddress(-16);
        MachineFunction Expand(CallKind kind, ulong size)
        {
            var call = new Call(0, kind, Expr.C(1, 64)) { Op = new(OpKind.Import, "memmove"), Arguments = [destination, source, Expr.C(size, 64)] };
            var function = new MachineFunction { Entry = 0, Range = new(0, 4, CodeRegion.Managed, default), Blocks = [new(0) { Statements = [call] }] };
            var next = 0;
            ConstantMemoryNormalizer.Run(function, () => new Variable(Storage.Temp(next++), 1));
            return function;
        }
        var tail = Expand(CallKind.Tail, 16).EntryBlock.Statements;
        check.True(tail.LastOrDefault() is Return { Pieces: [{ Offset: 0, Value: var pointer }] } && pointer.Equals(destination),
            "定长内存尾调用展开后仍返回目标指针");
        check.True(tail.Take(2).All(s => s is Define { Value: Load }) && tail.Skip(2).Take(2).All(s => s is Store),
            "重叠复制必须先读取全部源字节再写入");
        check.True(!Expand(CallKind.Direct, 16).EntryBlock.Statements.Any(s => s is Return), "普通内存调用不能提前终结方法");
        check.True(Expand(CallKind.Tail, 4097).EntryBlock.Statements.Single() is Call, "超过展开上限的尾调用保持原形");
        var buffer = new Entry(Storage.Gpr(8));
        var indirect = new MachineFunction { Entry = 0, Range = new(0, 8, CodeRegion.Managed, default), Blocks = [new(0)
            { Statements = [new Store(0, buffer, Expr.C(7, 64)), new Return(4) { Pieces = [new(0, buffer)] }] }] };
        var signature = new MachineSignature([], new(MachineSignature.ReturnIndex, types.Int64, Transfer.ResultBuffer,
            [new(Storage.Gpr(8), 64, 0)], 8, MemoryAccess.Write), null, 0);
        var lifter = new Cpp2CS.Machine.Lifting.FunctionLifter(facts);
        var promoted = Cpp2CS.Recovery.Memory.MemoryPromotion.Run(indirect, signature, _ => throw new NotSupportedException(),
            new ManagedAbi(facts.Layouts), lifter.Calls, lifter.Machine.Convention.StackPointer);
        check.True(promoted.TryGet(out _, out _) && indirect.EntryBlock.Statements.LastOrDefault() is Return { Pieces: [{ Value: Const { Value: 7 } }] },
            "间接返回按签名读取结果缓冲区，不让附带的目标指针返回值使地址逃逸");
    }

    private static void ReturnedFields(Assertions check, ManagedTypes types)
    {
        var pairDefinition = new TypeDef { Index = 150, Name = "ReturnedPair", Namespace = "Tests", Assembly = "Tests.dll", Token = 0,
            Attributes = TypeAttributes.Public | TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false, Size = 8 };
        pairDefinition.Fields = Enumerable.Range(0, 2).Select(i => new FieldDef { Index = 1500 + i, Owner = pairDefinition,
            Name = $"f{i}", Type = types.Int32, Offset = i * 4, Attributes = FieldAttributes.Public }).ToArray();
        var pair = new DefinitionRef(pairDefinition, []);
        var owner = Type("PairStorage", 151);
        var ownerType = new DefinitionRef(owner, []);
        var state = new FieldDef { Index = 151, Owner = owner, Name = "state", Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 16 };
        owner.Fields = [state];
        var read = Method(owner, "Read", 151);
        read.ReturnType = pair;
        owner.Methods = [read];
        var method = new MethodRef(read, [], []);
        var query = Method(Type("PairSource", 152), "Query", 152, MethodAttributes.Public | MethodAttributes.Static);
        query.ReturnType = pair;
        var consumer = Method(Type("PairConsumer", 153), "Consume", 153, MethodAttributes.Public | MethodAttributes.Static);
        consumer.Parameters = [new("pair", pair, 0, null, false)];
        var caller = new MethodRef(Method(Type("PairCaller", 154), "Run", 154), [], []);
        var returned = new LocalValue(new Variable(Storage.Temp(150), 1), pair, 64);
        var first = new LocalValue(new Variable(Storage.Temp(151), 1), types.Int32, 32);
        var second = new LocalValue(new Variable(Storage.Temp(152), 1), types.Int32, 32);
        var paths = types.Leaves(pair).Select(l => l.Path).ToArray();
        ManagedValue Field(int index) => new FieldValue(returned, paths[index][0], types.Int32, 32);
        ComposedValue Pair(ManagedValue a, ManagedValue b) => new(pair, [(paths[0], a), (paths[1], b)]);
        ManagedValue Test(ManagedValue receiver, bool pending) => new ComparisonValue(Cond.Ne,
            new FieldValue(receiver, new(state, ownerType), types.Int32, 32) { Pending = pending ? new(0, "待证字段", false) : null },
            new ConstantValue(0, types.Int32, 32), types.Boolean);
        var call = new ManagedCall(8, new(new(query, [], []), null, [], false), returned, false);
        var one = new ConstantValue(1, types.Int32, 32);
        var two = new ConstantValue(2, types.Int32, 32);
        var template = new ManagedBody(method,
        [
            new(0, [new ManagedBranch(0, Test(new ArgumentValue(-1, ownerType, 64), false), new(8, []), new(16, []))]),
            new(8, [call, new ManagedReturn(12, Pair(Field(0), Field(1)))]),
            new(16, [new ManagedReturn(16, Pair(one, two))]),
        ]);
        TemplateResult Run(bool consistent, bool complete, bool whole = false, bool grouped = false)
        {
            var selected = whole ? template with { Blocks = template.Blocks.Select(b => b.Address == 8
                ? b with { Statements = [call, new ManagedReturn(12, returned)] } : b).ToArray() } : template;
            MethodRecoveryResult? SelectedSummary(MethodRef requested) => requested == method ? new(method, 0, selected, []) : null;
            var body = new ManagedBody(caller,
            [
                new(0, [new ManagedBranch(0, Test(new ArgumentValue(0, ownerType, 64), true), new(8, []), new(16, []))]),
                new(8, [call, new ManagedJump(12, new(24, complete ? [new(first, Field(0)), new(second, Field(1))] : [new(first, Field(0))]))]),
                new(16, [new ManagedJump(16, new(24, complete ? [new(first, one), new(second, consistent ? two : one)] : [new(first, one)]))]),
                new(24, [new ManagedCall(24, new(new(consumer, [], []), null, [Pair(first, complete ? second : one)], false), null, false), new ManagedReturn(28, null)]),
            ]);
            if (grouped)
            {
                var aggregate = new LocalValue(new Variable(Storage.Temp(153), 1), pair, 64);
                body = body with { Blocks = body.Blocks.Select(b => b.Address == 8 || b.Address == 16
                    ? b with { Statements = b.Statements.Select(s => s is ManagedJump jump
                        ? jump with { Edge = jump.Edge with { Copies = [.. jump.Edge.Copies,
                            new(aggregate, b.Address == 8 ? Pair(Field(0), Field(1)) : Pair(one, consistent ? two : one))] } } : s).ToArray() }
                    : b.Address == 24 ? b with { Statements = [new ManagedCall(24, new(new(consumer, [], []), null, [aggregate], false), null, false), new ManagedReturn(28, null)] } : b).ToArray() };
            }
            return new TemplateRecovery(types, caller, SelectedSummary, new InlineEvidence(types, caller, SelectedSummary)).Run(body, new Dictionary<Variable, PendingConstruction>(), 0);
        }
        check.Equal(0, Run(true, true).Holes.Count, "结构体返回值由多个字段局部承接时仍可证明完整返回");
        check.True(Run(false, true).Holes.Count > 0, "一个字段在常量路径不同则拒绝结构体返回证明");
        check.True(Run(true, false).Holes.Count > 0, "缺少叶子承接时不猜测结构体返回的对应关系");
        check.Equal(0, Run(true, true, true).Holes.Count, "完整结构体调用结果可按出口字段逐一证明");
        check.True(Run(false, true, true).Holes.Count > 0, "完整结构体的字段证明仍须覆盖其他返回路径");
        check.Equal(0, Run(true, true, true, true).Holes.Count, "出口同时组合已证明字段时使用同一完整返回值");
        check.True(Run(false, true, true, true).Holes.Count > 0, "组合字段不掩盖不同返回路径中的值差异");
        TemplateResult Branched(bool consistent)
        {
            var selected = template with { Blocks = template.Blocks.Select(b => b.Address == 8
                ? b with { Statements = [call, new ManagedReturn(12, returned)] } : b).ToArray() };
            MethodRecoveryResult? Summary(MethodRef requested) => requested == method ? new(method, 0, selected, []) : null;
            var copies = new ManagedCopy[] { new(first, Field(0)), new(second, Field(1)) };
            var body = new ManagedBody(caller,
            [
                new(0, [new ManagedBranch(0, Test(new ArgumentValue(0, ownerType, 64), true), new(8, []), new(16, []))]),
                new(8, [call, new ManagedBranch(12, new ComparisonValue(Cond.Ne, Field(1), two, types.Boolean), new(32, copies), new(40, copies))]),
                new(16, [new ManagedJump(16, new(40, [new(first, consistent ? one : two), new(second, two)]))]),
                new(32, [new ManagedCall(32, new(new(consumer, [], []), null, [Pair(first, second)], false), null, false), new ManagedReturn(36, null)]),
                new(40, [new ManagedCall(40, new(new(consumer, [], []), null, [Pair(first, second)], false), null, false), new ManagedReturn(44, null)]),
            ]);
            return new TemplateRecovery(types, caller, Summary, new InlineEvidence(types, caller, Summary)).Run(body, new Dictionary<Variable, PendingConstruction>(), 0);
        }
        var branched = Branched(true);
        check.Equal(0, branched.Holes.Count, "结构体返回字段决定分支，其他字段仍经出口复制保留：" + string.Join("；", branched.Holes.Select(h => h.Reason)));
        check.True(Branched(false).Holes.Count > 0, "条件出口的其他字段不同则拒绝内联替换");
    }

    private static void ReturnedPredicates(Assertions check, ManagedTypes types)
    {
        var owner = Type("StatusStorage", 45);
        var ownerRef = new DefinitionRef(owner, []);
        var field = new FieldDef { Index = 45, Owner = owner, Name = "state", Type = types.Int32, Attributes = FieldAttributes.Private, Offset = 16 };
        owner.Fields = [field];
        var definition = Method(owner, "Read", 45);
        definition.ReturnType = types.Int32;
        owner.Methods = [definition];
        var method = new MethodRef(definition, [], []);
        var operation = Method(Type("StatusSource", 46), "Query", 46, MethodAttributes.Public | MethodAttributes.Static);
        operation.ReturnType = types.Int32;
        var query = new MethodRef(operation, [], []);
        var callerDefinition = Method(Type("StatusConsumer", 47), "Run", 47);
        callerDefinition.ReturnType = types.Boolean;
        var caller = new MethodRef(callerDefinition, [], []);
        var state = new LocalValue(new Variable(Storage.Temp(45), 1), types.Int32, 32);
        var returned = new LocalValue(new Variable(Storage.Temp(46), 1), types.Int32, 32);
        var result = new LocalValue(new Variable(Storage.Temp(47), 1), types.Boolean, 8);
        var zero = new ConstantValue(0, types.Int32, 32);
        var one = new ConstantValue(1, types.Int32, 32);
        FieldValue Read(ManagedValue receiver) => new(receiver, new FieldRef(field, ownerRef), types.Int32, 32);
        ManagedValue Compare(ManagedValue value) => new ComparisonValue(Cond.Ne, value, zero, types.Boolean);
        var call = new ManagedCall(8, new ManagedInvocation(query, null, [], false), returned, false);
        var template = new ManagedBody(method,
        [
            new(0, [new ManagedBranch(0, Compare(Read(new ArgumentValue(-1, ownerRef, 64))), new(8, []), new(16, []))]),
            new(8, [call, new ManagedReturn(12, returned)]),
            new(16, [new ManagedReturn(16, one)]),
        ]);
        MethodRecoveryResult? Summary(MethodRef requested) => requested == method ? new(method, 0, template, []) : null;
        TemplateResult Run(bool consistent, string? saved = null, bool sharedCopy = false, bool outsidePredicate = false, bool outsideCall = false)
        {
            var savedLocal = new LocalValue(new Variable(Storage.Temp(48), 1), types.Boolean, 8);
            var external = new LocalValue(new Variable(Storage.Temp(49), 1), types.Int32, 32);
            ManagedValue savedValue = Compare(new BinaryValue(BinOp.LShr, saved == "changed" ? state : external, one, types.Int32, 32));
            if (saved == "memory") savedValue = Compare(Read(new ArgumentValue(0, ownerRef, 64)));
            var entry = new List<ManagedStatement>
            {
                new ManagedAssignment(0, state, Read(new ArgumentValue(0, ownerRef, 64)) with { Pending = new(0, "待证字段", false) }),
            };
            var acrossCall = saved is "entry-same" or "entry-different" or "entry-input-changed";
            if (saved is not null && !acrossCall) entry.Add(new ManagedAssignment(2, savedLocal, savedValue));
            entry.Add(new ManagedBranch(4, Compare(state), new(8, []), new(16, [])));
            var body = new ManagedBody(caller,
            [
                new(0, entry),
                new(8, [.. acrossCall ? new ManagedStatement[] { new ManagedAssignment(8, savedLocal, savedValue) } : [],
                    call, new ManagedJump(12, new(24, [new(result, Compare(returned))]))]),
                new(16, [new ManagedJump(16, new(24, [new(result, new ConstantValue(consistent ? 1UL : 0UL, types.Boolean, 8))]))]),
                new(24, [new ManagedReturn(24, saved is null ? result : new BooleanValue(true, result, savedLocal, types.Boolean))]),
            ]);
            if (acrossCall)
                body = body with
                {
                    Blocks = [new(100, [new ManagedAssignment(100, savedLocal, saved == "entry-different" ? new ConstantValue(0, types.Boolean, 8) : savedValue),
                        call with { Address = 104, Result = saved == "entry-input-changed" ? external : returned }, new ManagedJump(108, new(0, []))]),
                        .. body.Blocks, new(32, [new ManagedReturn(32, savedLocal)])],
                    Regions = [new([0, 8, 16], 32, [32], null, ManagedRegionKind.Catch)],
                };
            if (sharedCopy)
                body = body with
                {
                    Blocks = [.. body.Blocks.Select(b => b.Address != 8 ? b : b with
                        { Statements = [call, new ManagedJump(12, new(20, [new(savedLocal, Compare(returned))]))] }),
                        new(20, [new ManagedJump(20, new(24, [new(result, savedLocal)]))]),
                        new(32, [new ManagedJump(32, new(20, [new(savedLocal, new ConstantValue(0, types.Boolean, 8))]))])],
                };
            if (outsidePredicate)
                body = body with
                {
                    Blocks = [.. body.Blocks.Select(b => b.Address != 8 ? b : b with
                        { Statements = [call, new ManagedJump(12, new(20, [new(external, returned)]))] }),
                        new(20, [new ManagedJump(20, new(24, [new(result, Compare(external))]))]),
                        new(40, [new ManagedReturn(40, new ConstantValue(0, types.Boolean, 8))])],
                    Regions = [new([0, 8], 40, [40], null, ManagedRegionKind.Catch)],
                };
            if (outsideCall) body = body with { Regions = [new([0, 16], 24, [24], null, ManagedRegionKind.Catch)] };
            return new TemplateRecovery(types, caller, Summary, new InlineEvidence(types, caller, Summary))
                .Run(body, new Dictionary<Variable, PendingConstruction>(), 0);
        }
        check.True(Run(true).Holes.Count == 0, "返回值比较可在所有路径证明后承接到同一布尔局部");
        check.True(Run(false).Holes.Count > 0, "常量路径与同一返回值比较不一致时拒绝恢复");
        var chained = Run(true, sharedCopy: true);
        check.True(chained.Holes.Count == 0, "共享出口复制逐边组合后可承接同一返回值比较");
        check.True(chained.Body.Blocks.Any(b => b.Address == 20), "仍有外部入边的共享复制块保留");
        check.True(Run(false, sharedCopy: true).Holes.Count > 0, "复制链不能掩盖不同路径的结果差异");
        check.Equal(0, Run(true, outsidePredicate: true).Holes.Count, "不抛异常的出口比较复制可以位于 try 外");
        check.True(Run(true, outsideCall: true).Holes.Count > 0, "真实调用不能跨越异常上下文搬移");
        TemplateResult BooleanBranch(bool inverted, bool consistent, string? copy = null, bool shared = false)
        {
            definition.ReturnType = types.Boolean;
            var publicField = new FieldDef { Index = 48, Owner = owner, Name = "fallback", Type = types.Boolean, Attributes = FieldAttributes.Public, Offset = 20 };
            ManagedValue Fallback(int argument) => new FieldValue(new ArgumentValue(argument, ownerRef, 64), new FieldRef(publicField, ownerRef), types.Boolean, 8);
            template = template with { Blocks = [template.Blocks[0], new(8, [call, new ManagedReturn(12, Compare(returned))]),
                new(16, [new ManagedReturn(16, shared ? Fallback(-1) : new ConstantValue(1, types.Boolean, 8))])] };
            var copied = new LocalValue(new Variable(Storage.Temp(50), 1), types.Int32, 32);
            var yes = new ManagedEdge(24, copy is null ? [] : [new(copied, zero)]);
            var alternate = yes with { Copies = copy is null ? [] : [new(copied, copy == "throwing" ? Read(new ArgumentValue(0, ownerRef, 64)) : one)] };
            var no = new ManagedEdge(32, []);
            var body = new ManagedBody(caller,
            [
                new(0, [new ManagedBranch(0, Compare(Read(new ArgumentValue(0, ownerRef, 64)) with { Pending = new(0, "待证字段", false) }), new(8, []), new(16, []))]),
                new(8, [call, new ManagedBranch(12, inverted ? new NegatedValue(Compare(returned), types.Boolean) : Compare(returned), inverted ? no : yes, inverted ? yes : no)]),
                new(16, [new ManagedJump(16, shared ? new(20, []) : consistent ? alternate : no)]),
                new(24, [call with { Address = 24 }, new ManagedReturn(28, copy == "live" ? Compare(copied) : new ConstantValue(1, types.Boolean, 8))]),
                new(32, [call with { Address = 32 }, new ManagedReturn(36, new ConstantValue(0, types.Boolean, 8))]),
            ]);
            if (shared) body = body with { Blocks = [.. body.Blocks,
                new(20, [new ManagedBranch(20, Fallback(0), yes, no)]), new(40, [new ManagedJump(40, new(20, []))])] };
            var recovered = new TemplateRecovery(types, caller, Summary, new InlineEvidence(types, caller, Summary)).Run(body, new Dictionary<Variable, PendingConstruction>(), 0);
            definition.ReturnType = types.Int32;
            template = template with { Blocks = [template.Blocks[0], new(8, [call, new ManagedReturn(12, returned)]), new(16, [new ManagedReturn(16, one)])] };
            return recovered;
        }
        var directBranch = BooleanBranch(false, true);
        check.True(directBranch.Holes.Count == 0, $"返回布尔谓词可直接承接调用方分支：{string.Join("；", directBranch.Holes.Select(h => h.Reason))}");
        check.Equal(0, BooleanBranch(true, true).Holes.Count, "返回布尔谓词的取反可承接相反分支");
        check.True(BooleanBranch(false, false).Holes.Count > 0, "常量路径去向不一致时拒绝布尔分支证明");
        check.Equal(0, BooleanBranch(false, true, "dead").Holes.Count, "条件出口未使用的纯局部复制不要求各路径相同");
        check.True(BooleanBranch(false, true, "live").Holes.Count > 0, "条件出口仍使用的局部复制必须相同");
        check.True(BooleanBranch(false, true, "throwing").Holes.Count > 0, "条件出口可能抛异常的复制不能因无用而丢弃");
        var sharedBranch = BooleanBranch(false, true, shared: true);
        check.True(sharedBranch.Holes.Count == 0 && sharedBranch.Body.Blocks.Any(b => b.Address == 20)
            && sharedBranch.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Invocation.Method == method),
            "共享条件尾部可被已证明调用旁路，其他入口使用的原块仍保留：" + string.Join("；", sharedBranch.Holes.Select(h => h.Reason)));
        var copied = Run(true, "stable");
        check.True(copied.Holes.Count == 0 && copied.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
            .Any(a => a.Value is ComparisonValue { Left: BinaryValue { Op: BinOp.LShr } }), "稳定整数表达式可提前保存，供内联区域外继续使用");
        check.True(Run(true, "changed").Holes.Count > 0, "依赖区域内定义的表达式不能提前保存");
        check.True(Run(true, "entry-same").Holes.Count == 0, "跨调用证明入口局部已保存同值，异常读取不阻止内联");
        check.True(Run(true, "entry-different").Holes.Count > 0, "异常路径可见的旧值不同，不得提前覆盖");
        check.True(Run(true, "entry-input-changed").Holes.Count > 0, "入口表达式的输入已被调用改写，不能沿用旧值证明");
        var memory = Run(true, "memory");
        check.True(memory.Body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
            .OfType<FieldValue>().Any(f => f.Field.Field == field), "读取内存的表达式仍保留实际读取，不按稳定整数副本消除");
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
        var parent = Type("VirtualBase", 51);
        parent.GenericParameters = [new() { Name = "TValue", Position = 0, Attributes = 0 }];
        var callback = new MethodDef { Index = 51, Owner = parent, Name = "Read", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Virtual, ImplAttributes = 0, Slot = 7 };
        parent.Methods = [callback];
        var constraint = new DefinitionRef(parent, [new GenericParameterRef("TValue", false, 0)]);
        var parameter = new GenericParameterRef("TReceiver", true, 0)
        {
            Parameter = new() { Name = "TReceiver", Position = 0, Attributes = 0, Constraints = [constraint] },
        };
        check.Equal(new MethodRef(callback, [types.Int32], []), DispatchResolution.VirtualSlot(parameter, 7, types,
            t => t.Substitute([types.Int32], []))!, "基类约束提供虚表声明，并代入调用方的类型实参");
        var shared = new GenericParameterRef("T", true, 0) { Binding = new(NativeBindingKind.Reference) };
        check.Equal(DispatchResolution.VirtualSlot(types.Object, 0, types)!, DispatchResolution.VirtualSlot(shared, 0, types)!,
            "引用共享形参使用 Object 的对象虚表槽");
        check.True(DispatchResolution.VirtualSlot(shared, 7, types) is null,
            "没有基类约束时不能推断额外虚表槽");
        check.True(DispatchResolution.VirtualSlot(shared with { Binding = new(NativeBindingKind.Shared) }, 0, types) is null,
            "未知值类型形参不能套用引用接收者约定");
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

    private static void UnchangedBarriers(Assertions check, ProgramFacts facts)
    {
        foreach (var variant in new[] { "unchanged", "different-location", "write", "call" })
        {
            var address = new Use(new Variable(Storage.Gpr(0), 0), 64);
            var loaded = new Variable(Storage.Gpr(1), 1);
            var block = new Block(0);
            block.Statements.Add(new Define(0, loaded, new Load(address, 64)));
            if (variant == "write") block.Statements.Add(new Store(4, address, Expr.C(0, 64)));
            if (variant == "call") block.Statements.Add(new Call(4, CallKind.Direct, Expr.C(100, 64)));
            var function = new MachineFunction { Entry = 0, Range = new(0, 12, CodeRegion.Managed, default), Blocks = [block] };
            var state = new IdiomState(new IdiomRewriter(facts), function);
            Expr target = variant == "different-location" ? new Binary(BinOp.Add, address, Expr.C(8, 64), 64) : address;
            check.Equal(variant == "unchanged", state.UnchangedReference(block, block.Statements.Count, target, new Use(loaded, 64)),
                $"未改变引用的屏障 {variant}");
        }
    }

    private static void CardMarkingBarriers(Assertions check)
    {
        uint[] body = [0xf003aea8, 0xb941c908, 0x340001e8, 0x90039e2a, 0xd3528008, 0x9133014a,
            0x528c9c0b, 0xd34cfc09, 0x72a0008b, 0x5280002c, 0x8b080d48, 0x8b0b0108,
            0x9ac92189, 0xc85f7d0a, 0xaa09014a, 0xc80b7d0a, 0x35ffffab, 0xd65f03c0];
        check.True(RuntimeHelpers.CardMarkingBody(body), "GC 位图通知完整指令证据");
        var referenceWrite = body.ToArray();
        referenceWrite[15] = 0xf9000001; // str x1, [x0]
        check.True(!RuntimeHelpers.CardMarkingBody(referenceWrite), "写入对象引用的实现不是纯 GC 通知");
        var externalBranch = body.ToArray();
        externalBranch[2] = 0x34000208; // cbz w8, body end
        check.True(!RuntimeHelpers.CardMarkingBody(externalBranch), "跳出已证明函数体的实现不能归一");
    }

    private static void CheckedByteArrays(Assertions check)
    {
        uint[] body = [0xf81f0ffe, 0xb9401808, 0x6b08003f, 0x540000a2, 0x8b010008, 0x39408100, 0xf84107fe, 0xd65f03c0, 0x94000004];
        check.True(RuntimeHelpers.CheckedByteArrayBody(body), "字节读取包含完整的无符号边界检查");
        var signed = body.ToArray();
        signed[3] = 0x540000aa; // b.ge
        check.True(!RuntimeHelpers.CheckedByteArrayBody(signed), "有符号比较不能替代数组下标边界检查");
        var index = new Use(new Variable(Storage.Gpr(1), 0), 32);
        check.True(DirectPass.ArrayIndex32(new Cpp2CS.Ir.Convert(ConvKind.SignExtend, index, 64)) == index
            && DirectPass.ArrayIndex32(new Use(index.Variable, 64)) is null, "地址下标必须有完整的高位扩展证据");
    }

    private static void ArrayIndices(Assertions check)
    {
        var syms = new SymTable();
        var index = syms.Arg(0, 32);
        check.True(ReferenceEquals(index, TypeOracle.ArrayIndex(syms.ZeroExtend(index, 64))), "数组访问与边界检查共用零扩展下标");
        check.True(ReferenceEquals(index, TypeOracle.ArrayIndex(syms.Convert(ConvKind.SignExtend, index, 64))), "数组下标保留 32 位来源");
        var whole = new PhiSym(new Block(0), new object(), 64);
        var low = new PhiSym(whole.Block, new object(), 32) { Projection = (whole, 0) };
        check.True(ReferenceEquals(whole, TypeOracle.ArrayIndex(low)), "数组下标的低位合流投影统一回到整体");
        var narrow = syms.Slice(index, 0, 16);
        check.True(ReferenceEquals(narrow, TypeOracle.ArrayIndex(narrow)), "不能丢弃 16 位下标的截断");
    }

    private static void AffineInductions(Assertions check)
    {
        foreach (var variant in new[] { "aligned", "different-edges", "narrow-counter" })
        {
            var entry = new Block(0); var loop = new Block(8); var back = new Block(16);
            var origin = new Variable(Storage.Gpr(0), 1); var index = origin with { Version = 2 }; var next = origin with { Version = 3 };
            var start = new Variable(Storage.Gpr(1), 1); var offset = start with { Version = 2 }; var advance = start with { Version = 3 };
            entry.Statements = [new Define(0, origin, Expr.C(0, 64)), new Define(4, start, Expr.C(32, 64))];
            loop.Statements = [new Phi(8, index, [origin, next]),
                new Phi(8, offset, variant == "different-edges" ? [advance, start] : [start, advance])];
            back.Statements = [new Define(16, next, new Binary(BinOp.Add, new Use(index, 64), Expr.C(1, 64), variant == "narrow-counter" ? 32 : 64)),
                new Define(20, advance, new Binary(BinOp.Add, new Use(offset, 64), Expr.C(8, 64), 64))];
            MachineFunction.AddEdge(entry, loop); MachineFunction.AddEdge(loop, back); MachineFunction.AddEdge(back, loop);
            var function = new MachineFunction { Entry = 0, Range = new(0, 24, CodeRegion.Managed, default), Blocks = [entry, loop, back] };
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            check.Equal(variant == "aligned", AffineInduction.Run(function, e => e is Use use ? definitions.GetValueOrDefault(use.Variable) : null),
                $"线性计数器 {variant}");
        }
    }

    private static void ArrayOffsetInductions(Assertions check)
    {
        foreach (var variant in new[] { "matched", "zero-offset", "wrong-stride", "narrow-offset", "unit-counter" })
        {
            var array = new Variable(Storage.Gpr(0), 0);
            var start = new Variable(Storage.Gpr(1), 1); var offset = start with { Version = 2 }; var next = start with { Version = 3 };
            var entry = new Block(0); var loop = new Block(8); var back = new Block(16);
            entry.Statements = [new Define(0, start, Expr.C(variant is "zero-offset" or "unit-counter" ? 0UL : 32UL, 64)), new Jump(4, 8)];
            loop.Statements = [new Phi(8, offset, [start, next]),
                new Store(8, new Binary(BinOp.Add, new Use(array, 64), new Use(offset, 64), 64), Expr.C(0, 64)), new Jump(12, 16)];
            back.Statements = [new Define(16, next, new Binary(BinOp.Add, new Use(offset, 64), Expr.C(variant == "wrong-stride" ? 16UL : variant == "unit-counter" ? 1UL : 8UL, 64),
                variant == "narrow-offset" ? 32 : 64)), new Jump(20, 8)];
            MachineFunction.AddEdge(entry, loop); MachineFunction.AddEdge(loop, back); MachineFunction.AddEdge(back, loop);
            var function = new MachineFunction { Entry = 0, Range = new(0, 24, CodeRegion.Managed, default), Blocks = [entry, loop, back] };
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            function.Renumber();
            var serial = 0;
            check.Equal(variant is "matched" or "zero-offset", ArrayPointerLoopsPass.Run(function, new Dictionary<Variable, int> { [array] = variant == "unit-counter" ? 1 : 8 },
                e => e is Use use ? definitions.GetValueOrDefault(use.Variable) : null, () => new Variable(Storage.Temp(serial++), 1)),
                $"数组字节偏移计数器 {variant}");
            if (variant == "unit-counter") check.True(loop.Statements.OfType<Phi>().Any(p => p.Target == offset),
                "已有单位计数器保留原定义，不能在自替换时删除");
        }
    }

    private static void ArrayElementTypes(Assertions check, ProgramFacts facts, ManagedTypes types)
    {
        var element = new ArrayRef(types.Byte, 1);
        var array = new Variable(Storage.Gpr(0), 1);
        var result = new Variable(Storage.Gpr(2), 1);
        foreach (var variant in new[] { "element", "wrong-scale", "partial-read" })
        {
            var index = new Binary(BinOp.Shl, new Use(new(Storage.Gpr(1), 0), 64), Expr.C(variant == "wrong-scale" ? 2UL : 3UL, 64), 64);
            var block = new Block(0) { Statements = [
                new Call(0, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.NewArray, new ArrayRef(element, 1)), Defines = [array] },
                new Define(4, result, new Load(new Binary(BinOp.Add, new Binary(BinOp.Add, new Use(array, 64), index, 64), Expr.C(32, 64), 64),
                    variant == "partial-read" ? 32 : 64))] };
            var function = new MachineFunction { Entry = 0, Range = new(0, 8, CodeRegion.Managed, default), Blocks = [block] };
            check.Equal(variant == "element" ? element : null, DelegateCallNormalizer.TypeQuery(facts, function)(new Use(result, 64)),
                $"机器数组元素类型 {variant}");
        }
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

    private static MethodDef Method(TypeDef owner, string name, int index, MethodAttributes attributes = MethodAttributes.Public) => new()
    {
        Index = index, Owner = owner, Name = name, Token = 0, Attributes = attributes, ImplAttributes = 0, Slot = -1,
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
        public void Assign(int index, ManagedValue value) => throw new NotSupportedException();
        public ManagedTypes Types => types;
        public Call Call { get; } = new(0, CallKind.Direct, new Const(0, 64));
        public List<ManagedStatement> Statements { get; } = [];
        public void Emit(ManagedStatement statement) => Statements.Add(statement);
        public RuntimeOp Op => new(OpKind.MemoryBarrier, null);
        public IReadOnlyList<Sym> Arguments => [];
        public TypeRef? ClassOperand => throw new NotSupportedException();
        public Sym Result => throw new NotSupportedException();
        public Sym ResultAt(int index) => throw new NotSupportedException();
        public bool InFault => throw new NotSupportedException();
        public ManagedValue Input(int index) => throw new NotSupportedException();
        public TypeRef? TypeOf(Sym sym) => throw new NotSupportedException();
        public LocalValue Local(Sym sym, TypeRef type) => throw new NotSupportedException();
        public LocalValue Temporary(TypeRef type) => throw new NotSupportedException();
        public ManagedValue Field(ManagedValue receiver, FieldRef field) => throw new NotSupportedException();
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
