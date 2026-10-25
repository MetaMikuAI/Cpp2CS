using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>在真实骨架中写入手工托管体；结果来自 ECMA 语义，不取任何被测方法的原生实现。</summary>
internal static class ExceptionOutputCheck
{
    [Command("eh-output", "手写托管体的区域、返回与边复制写出/解释检查", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var definition = facts.Model.Methods.First(m => m.IsStatic && m.Parameters.Count == 0 && m.GenericParameters.Count == 0
            && m.Owner.GenericParameters.Count == 0 && m.ReturnType.Equals(types.Int32) && m.Address != 0);
        var tested = new MethodRef(definition, [], []);
        var skeleton = new Skeleton(facts.Model);
        var emitter = new BodyEmitter(skeleton, types);
        var index = new WorldIndex(facts, types);
        var model = new CecilModel(facts.Model, skeleton);
        var interpreter = new CilInterpreter(model, index);
        var a = new Assertions();
        var ex = new LocalValue(new Variable(Storage.Temp(-9000), 1), types.Corlib("System.Exception"), 64);
        var outerEx = ex with { Variable = new Variable(Storage.Temp(-9001), 1) };
        var state = new LocalValue(new Variable(Storage.Temp(-9002), 1), types.Int32, 32);
        var ctor = types.Corlib("System.InvalidOperationException").Definition.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        var created = new NewObjectValue(new MethodRef(ctor, [], []), []);
        ConstantValue Number(int n) => new((ulong)n, types.Int32, 32);
        ManagedReturn Ret(int n) => new(0, Number(n));
        ThrowPlan? plan = null;
        string Execute()
        {
            var world = new World(index, 0, new Hints([], []), null) { ThrowPlan = plan };
            return interpreter.Run(world, skeleton.Method(definition), tested, []).Result!;
        }
        void Mutants(string kind)
        {
            var expected = Execute();
            var count = 0;
            foreach (var (description, apply, revert) in ExecutionCheck.ExceptionMutations(skeleton.Method(definition)))
            {
                if (!description.StartsWith(kind, StringComparison.Ordinal)) continue;
                count++;
                try { apply(); a.True(Execute() != expected, $"独立 CIL 场景必须检出 {description}"); }
                finally { revert(); }
            }
            a.True(count > 0, $"独立 CIL 场景必须产生 {kind}");
        }
        string Run(ManagedBlock[] blocks, params ManagedRegion[] regions)
        {
            var body = new ManagedBody(tested, blocks) { Regions = regions };
            var errors = emitter.Emit([body]);
            if (errors.Count != 0) throw new InvalidOperationException(string.Join(";", errors.Values));
            var method = skeleton.Method(definition);
            var instructions = method.Body.Instructions.ToArray();
            foreach (var handler in method.Body.ExceptionHandlers)
            {
                var begin = Array.IndexOf(instructions, handler.TryStart);
                var end = Array.IndexOf(instructions, handler.TryEnd);
                a.True(!instructions[begin..end].Any(i => i.OpCode.Code == Code.Ret), "try 内 ret 必须提升为区域外返回");
                begin = Array.IndexOf(instructions, handler.HandlerStart); end = Array.IndexOf(instructions, handler.HandlerEnd);
                a.True(!instructions[begin..end].Any(i => i.OpCode.Code == Code.Ret), "handler 内 ret 必须提升为区域外返回");
            }
            return Execute();
        }
        var one = new ManagedRegion([0], 1, [1], ex, ManagedRegionKind.Catch);
        a.Equal("return 0x7", Run([new(0, [new ManagedThrow(0, created)]), new(1, [Ret(7)])], one), "throw 到 catch，区域内返回");
        a.Equal("return 0xb", Run([new(0, [Ret(11)]), new(1, [Ret(7)])], one), "正常返回不进入 catch");
        a.Equal($"throw @0x{World.ExceptionBase:x}", Run([new(0, [new ManagedThrow(0, created)]), new(1, [new ManagedRethrow(0)])], one),
            "rethrow 离开方法时必须保留原始对象地址");
        var outer = new ManagedRegion([0, 1], 2, [2], outerEx, ManagedRegionKind.Catch);
        a.Equal("return 0xd", Run([new(0, [new ManagedThrow(0, created)]), new(1, [new ManagedRethrow(0)]), new(2, [Ret(13)])], outer, one), "内层重抛被外层 catch 捕获");
        Mutants("F5 删去 rethrow");
        string TypedCatch(TypeRef target)
        {
            var matches = new ComparisonValue(Cond.Ne, new IsInstValue(ex, target), new ConstantValue(0, target, 64), types.Boolean);
            return Run([new(0, [new ManagedThrow(0, created)]), new(1, [new ManagedBranch(0, matches, new(4, []), new(2, []))]),
                new(2, [new ManagedRethrow(0)]), new(3, [Ret(19)]), new(4, [Ret(17)])],
                new ManagedRegion([0, 1, 2], 3, [3], outerEx, ManagedRegionKind.Catch), new ManagedRegion([0], 1, [1, 2], ex, ManagedRegionKind.Catch));
        }
        a.Equal("return 0x11", TypedCatch(types.Corlib("System.InvalidOperationException")), "catch(T) 类型命中时 leave 到处理代码");
        a.Equal("return 0x13", TypedCatch(types.Corlib("System.NullReferenceException")), "catch(T) 类型不命中时重抛到外层");
        var fault = new ManagedRegion([0], 1, [1], null, ManagedRegionKind.Fault);
        a.Equal("return 0x11", Run([new(0, [new ManagedThrow(0, created)]),
            new(1, [new ManagedAssignment(0, state, Number(17)), new ManagedEndFault(0)]), new(2, [new ManagedReturn(0, state)])], outer, fault), "fault 写入对外层 catch 可见");
        a.Equal("return 0x9", Run([new(0, [Ret(9)]), new(1, [new ManagedAssignment(0, state, Number(17)), new ManagedEndFault(0)])], fault), "正常 leave 返回不运行 fault");
        var edge = new ManagedEdge(2, [new ManagedCopy(state, Number(19))]);
        a.Equal("return 0x13", Run([new(0, [new ManagedJump(0, edge)]), new(1, [Ret(7)]), new(2, [new ManagedReturn(0, state)])], one), "leave 之前执行边并行赋值");
        a.Equal("return 0x7", Run([new(0, [new ManagedThrow(0, new ConstantValue(0, ex.Type, 64))]), new(1, [Ret(7)])], one), "throw null 产生可捕获的 NullReferenceException");

        a.Equal($"throw @0x{World.ExceptionBase:x}", Run([new(0, [new ManagedThrow(0, created)]),
            new(1, [new ManagedJump(0, new(2, []))]), new(2, [new ManagedThrow(0, ex)]), new(3, [Ret(17)])], one), "catch 外重抛保存的同一对象");
        Mutants("F5 重抛改为吞掉");
        a.Equal("return 0x11", Run([new(0, [new ManagedJump(0, new(2, []))]), new(1, [new ManagedJump(0, new(3, []))]),
            new(2, [Ret(17)]), new(3, [Ret(19)])], one), "两个 leave 目标返回不同结果");
        Mutants("F5 交换 leave 目标");
        plan = new(0, types.Corlib("System.InvalidOperationException"));
        a.Equal("return 0x7", Run([new(0, [new ManagedCall(0, new(tested, null, [], false), null, false), new ManagedJump(0, new(1, []))]),
            new(1, [Ret(3)]), new(2, [Ret(7)])], new ManagedRegion([0, 1], 2, [2], ex, ManagedRegionKind.Catch)), "计划在普通调用事件抛出并被捕获");
        Mutants("F5 块移出 try");
        // ECMA-335 I.12.4.2 / III.4.1：异常转移保留方法局部存储；fault 中的写入对外层 catch 可见。
        // 用公开 Vector3 字段构造独立托管体，不读取业务方法机器码。
        plan = null;
        var vector = new DefinitionRef(facts.Model.Types.Single(t => t.FullName == "UnityEngine.Vector3"), []);
        var local = new LocalValue(new Variable(Storage.Temp(-9010), 1), vector, 0);
        var x = new FieldValue(new AddressValue(local), new FieldRef(vector.Definition.Fields.Single(f => f.Name == "x"), vector), types.Single, 32);
        var sample = new ConstantValue(BitConverter.SingleToUInt32Bits(1.5f), types.Single, 32);
        var initialized = new ManagedStore(0, new IndirectValue(new AddressValue(local), vector), new ComposedValue(vector, []));
        var writeX = new ManagedStore(0, x, sample);
        var equalX = new ManagedReturn(0, new ComparisonValue(Cond.Eq, x, sample, types.Boolean));
        a.Equal("return 0x1", Run([new(0, [initialized, writeX, new ManagedThrow(0, created)]), new(1, [equalX])], one),
            "结构体局部根跨 try/catch 保留全部字段");
        a.Equal("return 0x1", Run([new(0, [new ManagedThrow(0, created)]), new(1, [initialized, writeX, equalX])], one),
            "catch 内声明、清零并写入结构体局部变量");
        a.Equal("return 0x1", Run([new(0, [new ManagedThrow(0, created)]),
            new(1, [initialized, writeX, new ManagedEndFault(0)]), new(2, [equalX])], outer, fault),
            "fault 内结构体局部的写入对外层 catch 可见");
        var vectorCtor = new MethodRef(vector.Definition.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 3), [], []);
        plan = new(0, types.Corlib("System.InvalidOperationException"));
        a.Equal("return 0x1", Run([new(0, [initialized, writeX,
            new ManagedCall(0, new(vectorCtor, new AddressValue(local), [sample, sample, sample], false), null, false), Ret(0)]),
            new(1, [equalX])], one), "局部 ref 调用按计划抛出时不能执行正常返回的构造后值写回");
        return a.Finish("eh-output");
    }
}
