using Cpp2CS.Model;
using Cpp2CS.Tests.Execution;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Metrics;

internal static partial class MetricChecks
{
    private static void DeferredConversions(Assertions checks)
    {
        const string source = """
            public class A {
                public int Value;
                [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
                public extern void Consume();
            }
            public class B { }
            public static class Entry {
                public static int Field;
                [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
                public static extern void Tick();
                [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.InternalCall)]
                public static extern int Current();
                public static void ThrowInside() { throw new System.NullReferenceException(); }
                public static void CheckInside() { A a = null; a.Consume(); }
                public static void Reference(object x, object y, int selector) { }
                public static void Output(object x, object y, int selector) { }
                public static void GenericReference<T>(object x, object y, int selector) { }
                public static void GenericOutput<T>(object x, object y, int selector) { }
            }
            """;
        using var fixture = new CompiledSource(source);
        var module = fixture.Module;
        var target = module.GetType("A");
        var other = module.GetType("B");
        var reference = fixture.Method("Entry", "Reference");
        var output = fixture.Method("Entry", "Output");
        var tick = fixture.Method("Entry", "Tick");
        var field = module.GetType("Entry").Fields.Single();
        Instruction Call() => Instruction.Create(OpCodes.Call, tick);
        Instruction[] Cast(OpCode? code = null, TypeReference? type = null, bool second = false) =>
            [Instruction.Create(second ? OpCodes.Ldarg_1 : OpCodes.Ldarg_0), Instruction.Create(code ?? OpCodes.Castclass, type ?? target), Instruction.Create(OpCodes.Pop)];
        void Body(MethodDefinition method, params Instruction[] instructions)
        {
            method.Body = new MethodBody(method);
            foreach (var instruction in instructions) method.Body.Instructions.Add(instruction);
            method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
            // 手工 IL 也保留真实偏移，供分支覆盖与异常区域检查使用。
            var offset = 0;
            foreach (var instruction in method.Body.Instructions) { instruction.Offset = offset; offset += instruction.GetSize(); }
        }
        void Pair(OpCode? code = null, TypeReference? type = null, int calls = 1)
        {
            Body(reference, [.. Cast(code, type), .. Enumerable.Range(0, calls).Select(_ => Call())]);
            Body(output, [.. Enumerable.Range(0, calls).Select(_ => Call()), .. Cast(code, type)]);
        }
        TraceDifference? Execute(bool compatible = false, bool reverse = false, bool prefixMemoryMismatch = false, bool receiverNull = false)
        {
            var model = new CecilModel(module);
            var types = new ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8);
            var index = new WorldIndex(model.Program, types);
            var method = model.Method(reference);
            var world = new World(index, 0, new Hints([], []), method.DeclaringType);
            var objectType = model.Type(compatible ? target : other);
            // 同一实际类型的两个不同对象用于排除仅按运行时类型比较的实现。
            StackValue[] values = [StackValue.O(world.Object(objectType, "first", 0)), StackValue.O(world.Object(objectType, "second", 0)), StackValue.I4(0)];
            if (receiverNull) values[1] = StackValue.O(0);
            var interpreter = new CilInterpreter(model, index) { BodyModule = module };
            var left = interpreter.Run(world, reference, method, values);
            var right = interpreter.Run(world, output, model.Method(output), values);
            if (prefixMemoryMismatch) right.WriteValue(World.HeapBase + 0x1000, 1, 4);
            return reverse ? Trace.Difference(world, right, left) : Trace.Difference(world, left, right);
        }
        void Mismatch(string label, bool receiverNull = false)
        {
            var result = Execute(receiverNull: receiverNull);
            checks.True(result is { ReasonKind: ComparisonReason.None }, label + "：" + result);
        }
        foreach (var (code, type) in new[] { (OpCodes.Castclass, (TypeReference)target), (OpCodes.Unbox, module.TypeSystem.Int32),
                     (OpCodes.Unbox_Any, module.TypeSystem.Int32), (OpCodes.Unbox_Any, (TypeReference)target) })
        {
            Pair(code, type, calls: 2);
            checks.True(Execute()?.ReasonKind == ComparisonReason.ImplementationDifference, code + " 的失败保留对象与目标类型，允许多个调用");
        }
        Pair();
        checks.True(Execute(compatible: true) is null, "转换成功时两侧一致");
        checks.True(Execute()?.ReasonKind == ComparisonReason.ImplementationDifference, "转换失败判为实现差异");
        checks.True(Execute(reverse: true) is { ReasonKind: ComparisonReason.None }, "输出先抛仍是不一致");

        Body(output, Call()); Mismatch("输出不抛出");
        Body(output, [Call(), Instruction.Create(OpCodes.Ldnull), Instruction.Create(OpCodes.Throw)]); Mismatch("输出抛其他异常");
        Body(output, [Call(), .. Cast(second: true)]); Mismatch("转换对象不同");
        Body(output, [Call(), .. Cast(type: module.TypeSystem.String)]); Mismatch("转换目标类型不同");
        Body(output, [Call(), Instruction.Create(OpCodes.Ldc_I4_1), Instruction.Create(OpCodes.Stsfld, field), .. Cast()]); Mismatch("调用后有写入");
        Body(output, [Call(), Instruction.Create(OpCodes.Ldsfld, field), Instruction.Create(OpCodes.Stsfld, field), .. Cast()]); Mismatch("同值写入也拒绝");
        Body(output, [Call(), Instruction.Create(OpCodes.Ldc_I4_0), Instruction.Create(OpCodes.Newarr, module.TypeSystem.Int32), Instruction.Create(OpCodes.Pop), .. Cast()]); Mismatch("调用之间分配");
        var exceptionConstructor = module.ImportReference(typeof(InvalidCastException).GetConstructor(Type.EmptyTypes)!);
        Body(output, [Call(), Instruction.Create(OpCodes.Newobj, exceptionConstructor), Instruction.Create(OpCodes.Throw)]); Mismatch("显式 InvalidCastException 没有转换来源");

        // 一个被接住的异常夹在调用与转换之间，即使最终转换仍失败，也不能登记。
        var tryStart = Instruction.Create(OpCodes.Ldnull);
        var catchStart = Instruction.Create(OpCodes.Pop);
        var castStart = Instruction.Create(OpCodes.Ldarg_0);
        Body(output, [Call(), tryStart, Instruction.Create(OpCodes.Throw), catchStart, Instruction.Create(OpCodes.Leave, castStart),
            castStart, Instruction.Create(OpCodes.Castclass, target), Instruction.Create(OpCodes.Pop)]);
        output.Body.ExceptionHandlers.Add(new(ExceptionHandlerType.Catch) { TryStart = tryStart, TryEnd = catchStart,
            HandlerStart = catchStart, HandlerEnd = castStart, CatchType = module.ImportReference(typeof(Exception)) });
        Mismatch("调用之间有被接住的抛出事件");

        // catch 后 rethrow 的最终异常相同，但原抛出已经被方法内处理块接住。
        void CaughtConversion(MethodDefinition method, bool delayed, bool rethrow = true)
        {
            var cast = Cast();
            var handler = Instruction.Create(OpCodes.Pop);
            var tail = Instruction.Create(OpCodes.Nop);
            Body(method, [.. delayed ? new[] { Call() } : [], .. cast, Instruction.Create(OpCodes.Leave, tail), handler,
                rethrow ? Instruction.Create(OpCodes.Rethrow) : Instruction.Create(OpCodes.Leave, tail), tail]);
            method.Body.ExceptionHandlers.Add(new(ExceptionHandlerType.Catch) { TryStart = cast[0], TryEnd = handler,
                HandlerStart = handler, HandlerEnd = tail, CatchType = module.ImportReference(typeof(InvalidCastException)) });
        }
        CaughtConversion(reference, false); CaughtConversion(output, true); Mismatch("参考转换失败被 catch 接住再重抛");
        CaughtConversion(reference, false, rethrow: false); CaughtConversion(output, true, rethrow: false); Mismatch("参考转换失败被 catch 接住并返回");
        Pair(); CaughtConversion(output, true); Mismatch("输出转换失败被 catch 接住再重抛");

        // 未捕获的异常可经过 finally；抛出后的共同事件与结局内存仍须按原规则核对。
        void FinallyConversion(MethodDefinition method, bool delayed)
        {
            var cast = Cast();
            var handler = Call();
            var tail = Instruction.Create(OpCodes.Nop);
            Body(method, [.. delayed ? new[] { Call() } : [], .. cast, Instruction.Create(OpCodes.Leave, tail), handler,
                Instruction.Create(OpCodes.Ldc_I4_1), Instruction.Create(OpCodes.Stsfld, field), Instruction.Create(OpCodes.Endfinally), tail]);
            method.Body.ExceptionHandlers.Add(new(ExceptionHandlerType.Finally) { TryStart = cast[0], TryEnd = handler,
                HandlerStart = handler, HandlerEnd = tail });
        }
        FinallyConversion(reference, false); FinallyConversion(output, true);
        checks.True(Execute()?.ReasonKind == ComparisonReason.ImplementationDifference, "未捕获异常经过相同 finally 时核对共同后缀及结局内存");

        // 差异前已有共同事件和堆写入；必须比较到首个不同事件当时的内存。
        Body(reference, [Instruction.Create(OpCodes.Ldc_I4_1), Instruction.Create(OpCodes.Stsfld, field), Call(), .. Cast(), Call()]);
        Body(output, [Instruction.Create(OpCodes.Ldc_I4_1), Instruction.Create(OpCodes.Stsfld, field), Call(), Call(), .. Cast()]);
        checks.True(Execute()?.ReasonKind == ComparisonReason.ImplementationDifference, "共同事件前缀及其内存相同后登记实现差异");
        Body(reference, [Call(), .. Cast(), Call()]);
        Body(output, [Call(), Instruction.Create(OpCodes.Ldsfld, field), Instruction.Create(OpCodes.Ldc_I4_1), Instruction.Create(OpCodes.Xor),
            Instruction.Create(OpCodes.Stsfld, field), Call(), .. Cast()]);
        Mismatch("共同前缀之后、首个不同事件之前的内存已不同");
        Pair();
        checks.True(Execute(prefixMemoryMismatch: true) is { ReasonKind: ComparisonReason.None }, "抛出之后的写入也拒绝");

        // 接收者判空可先于延后的转换；来源须来自当前方法的检查。
        var nullConstructor = module.ImportReference(typeof(NullReferenceException).GetConstructor(Type.EmptyTypes)!);
        var argumentConstructor = module.ImportReference(typeof(ArgumentException).GetConstructor(Type.EmptyTypes)!);
        var consume = target.Methods.Single(m => m.Name == "Consume");
        var valueField = target.Fields.Single();
        Instruction[] ExplicitNullCheck(bool branchOnNull = false)
        {
            var create = Instruction.Create(OpCodes.Newobj, nullConstructor);
            var tail = Instruction.Create(OpCodes.Nop);
            return branchOnNull
                ? [Instruction.Create(OpCodes.Ldarg_1), Instruction.Create(OpCodes.Brfalse, create), Instruction.Create(OpCodes.Br, tail),
                    create, Instruction.Create(OpCodes.Throw), tail]
                : [Instruction.Create(OpCodes.Ldarg_1), Instruction.Create(OpCodes.Brtrue, tail), create, Instruction.Create(OpCodes.Throw), tail];
        }
        void NullDifference(string label)
        {
            var result = Execute(receiverNull: true);
            checks.True(result is { ReasonKind: ComparisonReason.ImplementationDifference } && result.Message.Contains("(b)"), label + "：" + result);
        }
        Pair();
        checks.True(Execute() is { Message: var conversionMessage } && conversionMessage.Contains("(a)"), "转换失败诊断标明 (a)");
        Body(output, [Call(), Instruction.Create(OpCodes.Ldarg_1), Instruction.Create(OpCodes.Callvirt, consume)]);
        NullDifference("调用接收者的隐式判空");
        checks.True(Execute(reverse: true, receiverNull: true) is { ReasonKind: ComparisonReason.None }, "判空先抛的反方向仍不一致");
        foreach (var code in new[] { OpCodes.Ldfld, OpCodes.Ldflda, OpCodes.Stfld })
        {
            Body(output, [Call(), Instruction.Create(OpCodes.Ldarg_1), .. code == OpCodes.Stfld ? new[] { Instruction.Create(OpCodes.Ldc_I4_1) } : [],
                Instruction.Create(code, valueField), .. code == OpCodes.Stfld ? [] : new[] { Instruction.Create(OpCodes.Pop) }]);
            NullDifference(code + " 接收者的隐式判空");
        }
        foreach (var branchOnNull in new[] { false, true })
        {
            Body(output, [Call(), .. ExplicitNullCheck(branchOnNull)]);
            NullDifference("显式判空分支 " + (branchOnNull ? "brfalse" : "brtrue"));
            Mismatch("显式判空分支未走空路径时不登记");
        }
        var nullArm = Instruction.Create(OpCodes.Nop);
        var nullJump = Instruction.Create(OpCodes.Nop);
        var continued = Instruction.Create(OpCodes.Nop);
        Body(output, [Instruction.Create(OpCodes.Ldarg_1), Instruction.Create(OpCodes.Ldnull), Instruction.Create(OpCodes.Ceq),
            Instruction.Create(OpCodes.Brtrue, nullJump), Instruction.Create(OpCodes.Br, continued), nullJump, Instruction.Create(OpCodes.Br, nullArm),
            nullArm, Instruction.Create(OpCodes.Call, fixture.Method("Entry", "Current")), Instruction.Create(OpCodes.Pop),
            Instruction.Create(OpCodes.Newobj, nullConstructor), Instruction.Create(OpCodes.Throw), continued]);
        NullDifference("直接 null 比较经跳板与调用后显式判空");
        Mismatch("同一判空模板的非空输入不登记");
        Body(output, [Call(), Instruction.Create(OpCodes.Newobj, argumentConstructor), Instruction.Create(OpCodes.Throw)]);
        Mismatch("输出 ArgumentException 不登记", receiverNull: true);
        Body(output, [Call(), Instruction.Create(OpCodes.Newobj, nullConstructor), Instruction.Create(OpCodes.Throw)]);
        Mismatch("无判空分支的显式 NullReferenceException 不登记", receiverNull: true);
        foreach (var callee in new[] { fixture.Method("Entry", "ThrowInside"), fixture.Method("Entry", "CheckInside") })
        {
            Body(output, [Call(), Instruction.Create(OpCodes.Call, callee)]);
            Mismatch("被调方法内部的 NullReferenceException 不登记：" + callee.Name, receiverNull: true);
        }
        Body(output, [Call(), Instruction.Create(OpCodes.Ldc_I4_1), Instruction.Create(OpCodes.Stsfld, field), .. ExplicitNullCheck()]);
        Mismatch("调用与显式判空之间有写入", receiverNull: true);
        Body(output, [Call(), Instruction.Create(OpCodes.Ldsfld, field), Instruction.Create(OpCodes.Stsfld, field),
            Instruction.Create(OpCodes.Ldarg_1), Instruction.Create(OpCodes.Callvirt, consume)]);
        Mismatch("调用与隐式判空之间有同值写入", receiverNull: true);
        Body(output, [Call(), Instruction.Create(OpCodes.Ldnull), Instruction.Create(OpCodes.Ldlen), Instruction.Create(OpCodes.Pop)]);
        Mismatch("数组判空不登记", receiverNull: true);
        Body(output, ExplicitNullCheck());
        Mismatch("判空之前没有调用不登记", receiverNull: true);
        var boolTail = Instruction.Create(OpCodes.Nop);
        Body(output, [Call(), Instruction.Create(OpCodes.Ldc_I4_0), Instruction.Create(OpCodes.Brtrue, boolTail),
            Instruction.Create(OpCodes.Newobj, nullConstructor), Instruction.Create(OpCodes.Throw), boolTail]);
        Mismatch("整数条件分支不冒充判空", receiverNull: true);
        var equalityTail = Instruction.Create(OpCodes.Nop);
        Body(output, [Call(), Instruction.Create(OpCodes.Ldarg_1), Instruction.Create(OpCodes.Ldarg_1), Instruction.Create(OpCodes.Ceq),
            Instruction.Create(OpCodes.Brfalse, equalityTail), Instruction.Create(OpCodes.Newobj, nullConstructor), Instruction.Create(OpCodes.Throw), equalityTail]);
        Mismatch("普通对象相等分支不冒充判空", receiverNull: true);
        Body(output, [Call(), .. ExplicitNullCheck()]);
        checks.True(Execute(receiverNull: true, prefixMemoryMismatch: true) is { ReasonKind: ComparisonReason.None }, "判空抛出之后仍检查结局内存");
        var check = ExplicitNullCheck();
        var nullHandler = Instruction.Create(OpCodes.Pop);
        var nullTail = Instruction.Create(OpCodes.Nop);
        Body(output, [Call(), .. check, Instruction.Create(OpCodes.Leave, nullTail), nullHandler, Instruction.Create(OpCodes.Rethrow), nullTail]);
        output.Body.ExceptionHandlers.Add(new(ExceptionHandlerType.Catch) { TryStart = check[0], TryEnd = nullHandler,
            HandlerStart = nullHandler, HandlerEnd = nullTail, CatchType = module.ImportReference(typeof(NullReferenceException)) });
        Mismatch("判空异常被 catch 接住再重抛不登记", receiverNull: true);
        FinallyConversion(reference, false);
        var finallyCheck = ExplicitNullCheck();
        var nullFinally = Call();
        var finallyTail = Instruction.Create(OpCodes.Nop);
        Body(output, [Call(), .. finallyCheck, Instruction.Create(OpCodes.Leave, finallyTail), nullFinally,
            Instruction.Create(OpCodes.Ldc_I4_1), Instruction.Create(OpCodes.Stsfld, field), Instruction.Create(OpCodes.Endfinally), finallyTail]);
        output.Body.ExceptionHandlers.Add(new(ExceptionHandlerType.Finally) { TryStart = finallyCheck[0], TryEnd = nullFinally,
            HandlerStart = nullFinally, HandlerEnd = finallyTail });
        NullDifference("不同异常经过共同 finally 后继续核对事件和内存");
        Pair();

        var options = new MetricOptions(64, 10000);
        var modelFactory = CecilModel.Factory(module);
        var metric = IlMetrics.Compare(reference, output, options, modelFactory);
        checks.True(metric is { Status: MetricStatus.Inconclusive, ReasonKind: ComparisonReason.ImplementationDifference, CompletedCases: 64 }, "方法层面保留实现差异并完成全部输入");
        var seeds = Enumerable.Range(0, 64).Select(seed => IlMetrics.Compare(reference, output, options with { Cases = 1, FirstSeed = seed }, modelFactory)).ToArray();
        checks.True(seeds.Any(m => m.Status == MetricStatus.Match) && seeds.Any(m => m.ReasonKind == ComparisonReason.ImplementationDifference), "同一 IL 夹具分别覆盖转换成功和失败输入");
        var report = IlMetrics.Report([metric], options);
        checks.True(report.Summary.Reasons.GetValueOrDefault("ImplementationDifference") == 1
            && report.Summary.Statuses["Match"].Count == 0 && report.Summary.Statuses["Mismatch"].Count == 0, "汇总单列实现差异，不计一致或不一致");

        // 转换失败时是实现差异，成功时输出多抛异常；真实不一致必须覆盖早先的实现差异。
        var early = seeds.First(m => m.ReasonKind == ComparisonReason.ImplementationDifference).Seed!.Value;
        Body(output, [Call(), .. Cast(), Instruction.Create(OpCodes.Ldnull), Instruction.Create(OpCodes.Throw)]);
        checks.True(IlMetrics.Compare(reference, output, options with { FirstSeed = early }, modelFactory) is { Status: MetricStatus.Mismatch, CompletedCases: > 1 }, "后续输入的真实不一致优先于实现差异");

        var genericReference = fixture.Method("Entry", "GenericReference");
        var genericOutput = fixture.Method("Entry", "GenericOutput");
        void GenericBody(MethodDefinition method, bool delayed)
        {
            var tail = Instruction.Create(OpCodes.Nop);
            var cast = Cast(OpCodes.Unbox_Any, method.GenericParameters[0]);
            // 值类型拆箱 null 抛 NullReferenceException，不属于本条差异。
            Body(method, [Instruction.Create(OpCodes.Ldarg_0), Instruction.Create(OpCodes.Brfalse, tail),
                .. delayed ? new[] { Call() } : [], .. cast, .. delayed ? [] : new[] { Call() }, tail]);
        }
        GenericBody(genericReference, false); GenericBody(genericOutput, true);
        var generic = IlMetrics.Compare(genericReference, genericOutput, options, modelFactory);
        checks.True(generic is { Status: MetricStatus.Inconclusive, ReasonKind: ComparisonReason.ImplementationDifference }
            && generic.Instances!["ref"].Status == MetricStatus.Match && generic.Instances["value"].ReasonKind == ComparisonReason.ImplementationDifference,
            "泛型引用轮的一致不能覆盖值轮的实现差异");
    }
}
