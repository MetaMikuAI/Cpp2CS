using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceReturnsCheck
{
    [Command("source-returns", "共享返回尾部、布尔位宽与同时复制", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var owner = new TypeDef { Index = -1, Assembly = "Source.Tests.dll", Namespace = "Tests", Name = "Subject",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var boolean = new DefinitionRef(new TypeDef { Index = -2, Assembly = "mscorlib.dll", Namespace = "System", Name = "Boolean",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        var method = new MethodRef(new MethodDef { Index = -1, Owner = owner, Name = "Read", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = boolean }, [], []);
        var local = new LocalValue(new(Storage.Temp(1), 1), boolean, 1);
        var other = new LocalValue(new(Storage.Temp(2), 1), boolean, 1);
        var widened = new ConversionValue(ConvKind.ZeroExtend, local, new PrimitiveRef("U1"), 8);
        ManagedBody Body(ManagedValue result, params ManagedCopy[] copies) => new(method,
            [new(0, [new ManagedJump(0, new(1, copies))]), new(1, [new ManagedReturn(1, result)])]);
        foreach (var bit in new ulong[] { 0, 1 })
        {
            var rewritten = SourceReturns.Rewrite(Body(widened, new ManagedCopy(local, new ConstantValue(bit, boolean, 1))));
            a.True(rewritten.Blocks[0].Statements is [ManagedReturn { Value: ConstantValue c }] && c.Bits == bit && c.Width == 1,
                $"普通 bool 方法的 {bit} 返回直接还原");
        }
        var parallel = SourceReturns.Rewrite(Body(widened, new(local, other), new(other, new ConstantValue(0, boolean, 1))));
        a.Equal(other, ((ManagedReturn)parallel.Blocks[0].Statements[0]).Value, "同时复制返回旧的另一局部值");
        var nonCanonical = new ConversionValue(ConvKind.ZeroExtend, other with { Width = 8 }, new PrimitiveRef("U4"), 32);
        var wide = SourceReturns.Rewrite(Body(nonCanonical));
        a.Equal(nonCanonical, ((ManagedReturn)wide.Blocks[0].Statements[0]).Value, "未证明为 0/1 的 bool 存储值保留位宽转换");
        var unknown = new HoleValue("保留缺口", boolean, 1);
        var hole = Body(unknown);
        a.True(SourceReturns.Rewrite(hole).Blocks[0].Statements[0] is ManagedJump, "带洞尾部不能被当作纯返回复制");
        var field = new FieldDef { Index = -1, Owner = owner, Name = "Flag", Token = 0, Type = boolean, Offset = 16, Attributes = FieldAttributes.Public };
        var read = new FieldValue(new ArgumentValue(0, new DefinitionRef(owner, []), 64), new(field, new DefinitionRef(owner, [])), boolean, 8);
        a.True(SourceReturns.Rewrite(Body(read)).Blocks[0].Statements[0] is ManagedJump, "可能抛出的字段读取保留位置");
        var reference = new LocalValue(new(Storage.Temp(3), 1), new ByRefRef(boolean), 64);
        var indirect = new IndirectValue(reference, boolean);
        var selected = Body(indirect, new ManagedCopy(reference, new AddressValue(local)));
        a.True(SourceReturns.Rewrite(selected).Blocks[0].Statements is [ManagedReturn { Value: var selectedValue }] && selectedValue == local,
            "条件引用在返回前选择局部存储时直接返回局部值");
        var updated = Body(indirect, new(reference, new AddressValue(local)), new(local, other));
        a.True(SourceReturns.Rewrite(updated).Blocks[0].Statements is [ManagedJump], "地址目标同时被边复制写入时不能返回旧值");
        var refChain = Body(indirect);
        a.True(SourceReturns.Rewrite(refChain).Blocks[0].Statements is [ManagedReturn { Value: IndirectValue }], "同一区域内的纯跳转可以复制间接返回");
        var guarded = refChain with { Regions = [new([0], 1, [1], null, ManagedRegionKind.Catch)] };
        a.True(SourceReturns.Rewrite(guarded).Blocks[0].Statements is [ManagedJump], "可能抛出的ref读取不能越过catch边界");
        var generic = new GenericParameterRef("T", true, 0);
        var genericLocal = local with { Type = generic, Width = 0 };
        var genericReference = reference with { Type = new ByRefRef(generic) };
        var copiedReturn = Body(indirect) with { Blocks = [new(0, [new ManagedAssignment(0, genericLocal,
            new IndirectValue(genericReference, generic)), new ManagedReturn(1, genericLocal)])] };
        a.True(SourceReturns.Rewrite(copiedReturn).Blocks[0].Statements is [ManagedReturn { Value: IndirectValue }], "紧邻返回的局部读取副本原地内联");
        var observedReturn = copiedReturn with { Blocks = [new(0, [new ManagedAssignment(0, genericReference, new AddressValue(genericLocal)),
            .. copiedReturn.Blocks[0].Statements])] };
        a.True(SourceReturns.Rewrite(observedReturn).Blocks[0].Statements.Count == 3, "被取地址的返回局部仍保留实际写入");
        var narrowed = copiedReturn with { Blocks = [new(0, [new ManagedAssignment(0, local,
            new ConstantValue(256, new PrimitiveRef("U8"), 64)), new ManagedReturn(1, local)])] };
        a.True(SourceReturns.Rewrite(narrowed).Blocks[0].Statements.Count == 2, "局部赋值隐含的类型或位宽转换不能省略");
        Throws(a, method);
        Dispatch(a);
        return a.Finish("source-returns");
    }

    private static void Throws(Assertions a, MethodRef method)
    {
        var type = new PrimitiveRef("Object");
        var first = new LocalValue(new(Storage.Temp(1), 1), type, 64);
        var second = new LocalValue(new(Storage.Temp(2), 1), type, 64);
        var merged = new LocalValue(new(Storage.Temp(3), 1), type, 64);
        var body = new ManagedBody(method, [
            new(0, [new ManagedJump(0, new(2, [new(merged, first)]))]),
            new(1, [new ManagedJump(1, new(2, [new(merged, second)]))]),
            new(2, [new ManagedJump(2, new(3, []))]), new(3, [new ManagedThrow(3, merged)])]);
        var result = SourceReturns.Rewrite(body);
        a.True(result.Blocks[0].Statements is [ManagedAssignment { Value: var value }, ManagedThrow { Exception: var thrown }]
            && value == first && thrown == merged, "第一条失败路径保留赋值后直接抛出");
        a.True(result.Blocks[1].Statements is [ManagedAssignment { Value: var other }, ManagedThrow] && other == second,
            "第二条失败路径使用自己的异常值");
        a.True(result.Blocks[2].Statements is [ManagedThrow], "纯跳转链收敛到抛出尾部");
        var region = body with { Regions = [new([0, 1, 2], 3, [3], merged, ManagedRegionKind.Catch)] };
        a.True(SourceReturns.Rewrite(region).Blocks[2].Statements is [ManagedJump], "抛出操作不能跨越异常区域");
        var writes = body with { Blocks = [body.Blocks[0] with { Statements = [new ManagedJump(0, new(3,
            [new(merged, first), new(second, new ConstantValue(0, type, 64))]))] }, .. body.Blocks.Skip(1)] };
        a.True(SourceReturns.Rewrite(writes).Blocks[0].Statements is [ManagedAssignment, ManagedAssignment { Target: var target }, ManagedThrow]
            && target == second, "外层异常处理可能读取的其他边复制不能丢弃");
        var parallel = body with { Blocks = [body.Blocks[0] with { Statements = [new ManagedJump(0, new(3,
            [new(merged, second), new(second, first)]))] }, .. body.Blocks.Skip(1)] };
        a.True(SourceReturns.Rewrite(parallel).Blocks[0].Statements is [ManagedJump], "有交叉依赖的同时复制不顺序展开");
        var call = body with { Blocks = [.. body.Blocks.Take(3), new(3,
            [new ManagedCall(3, new(method, null, [], false), null, false), new ManagedThrow(3, merged)])] };
        a.True(SourceReturns.Rewrite(call).Blocks[2].Statements is [ManagedJump], "不复制带调用的异常尾部");
    }

    private static void Dispatch(Assertions a)
    {
        TypeDef Type(string ns, string name) => new() { Index = -1, Assembly = "Source.Tests.dll", Namespace = ns, Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        MethodDef Method(TypeDef owner, string name) => new() { Index = -1, Owner = owner, Name = name, Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = new PrimitiveRef("Boolean") };
        var owner = Type("Tests", "Iterator");
        owner.Interfaces = [new DefinitionRef(Type("System.Collections", "IEnumerator"), [])];
        owner.CustomAttributes = [new(Method(Type("System.Runtime.CompilerServices", "CompilerGeneratedAttribute"), ".ctor"), [], [], [])];
        var type = new DefinitionRef(owner, []);
        var integer = new PrimitiveRef("I4");
        var state = new LocalValue(new(Storage.Temp(1), 1), integer, 32);
        var capture = new LocalValue(new(Storage.Temp(2), 1), type, 64);
        ManagedAssignment Read(ulong address, LocalValue target, string name) => new(address, target, new FieldValue(new ArgumentValue(-1, type, 64),
            new(new FieldDef { Index = -1, Owner = owner, Name = name, Token = 0, Type = target.Type, Offset = 16, Attributes = FieldAttributes.Public }, type), target.Type, target.Width));
        ManagedBranch Branch(ulong address, ulong left, ulong right) => new(address, new ComparisonValue(Cond.Eq, state,
            new ConstantValue(0, integer, 32), new PrimitiveRef("Boolean")), new(left, []), new(right, []));
        var load = Read(1, capture, "<>4__this");
        var body = new ManagedBody(new(Method(owner, "MoveNext"), [], []),
            [new(0, [Read(0, state, "<>1__state"), Branch(0, 1, 2)]), new(1, [load, Branch(1, 2, 3)]),
                new(2, [new ManagedReturn(2, new ConstantValue(0, type, 64))]), new(3, [new ManagedReturn(3, capture)])]);
        var rewritten = SourceIteratorDispatch.Rewrite(body);
        a.True(rewritten.Blocks[0].Statements[0] == load && rewritten.Blocks[1].Statements.Count == 1,
            "捕获对象读取提前到状态判断前，读取次数不增加");
        var sideEffect = new ManagedStore(1, ((FieldValue)load.Value), new ConstantValue(0, type, 64));
        var blocked = body with { Blocks = [body.Blocks[0], body.Blocks[1] with { Statements = [sideEffect, .. body.Blocks[1].Statements] }, .. body.Blocks.Skip(2)] };
        a.Equal(blocked, SourceIteratorDispatch.Rewrite(blocked), "不跨过写入提前读取捕获对象");
        var loop = body with { Blocks = [.. body.Blocks.Take(3), new(3, [new ManagedJump(3, new(1, []))])] };
        a.Equal(loop, SourceIteratorDispatch.Rewrite(loop), "业务路径重入状态判断时不提升读取");

        var result = new LocalValue(new(Storage.Temp(3), 1), new PrimitiveRef("Boolean"), 1);
        var write = new ManagedStore(2, Read(2, state, "<>1__state").Value, state);
        var shared = new ManagedBody(body.Method, [
            new(0, [new ManagedJump(0, new(2, [new(state, new ConstantValue(1, integer, 32)), new(result, new ConstantValue(1, result.Type, 1))]))]),
            new(1, [new ManagedJump(1, new(2, [new(state, new ConstantValue(uint.MaxValue, integer, 32)), new(result, new ConstantValue(0, result.Type, 1))]))]),
            new(2, [write, new ManagedReturn(2, result)])]);
        var returns = SourceReturns.Rewrite(shared);
        a.True(returns.Blocks[0].Statements is [ManagedStore { Value: ConstantValue { Bits: 1 } }, ManagedReturn { Value: ConstantValue { Bits: 1 } }],
            "挂起路径先写状态 1，再返回 true");
        a.True(returns.Blocks[1].Statements is [ManagedStore { Value: ConstantValue { Bits: uint.MaxValue } }, ManagedReturn { Value: ConstantValue { Bits: 0 } }],
            "完成路径先写状态 -1，再返回 false");
        var ordinary = shared with { Blocks = [.. shared.Blocks.Take(2), new(2, [write with { Target = Read(2, state, "Other").Value }, new ManagedReturn(2, result)])] };
        a.True(SourceReturns.Rewrite(ordinary).Blocks[0].Statements[0] is ManagedJump, "普通字段写入不应用迭代器返回规则");
        var overwritten = shared with { Blocks = [shared.Blocks[0] with { Statements =
            [write with { Value = new ConstantValue(uint.MaxValue, integer, 32) }, .. shared.Blocks[0].Statements] }, .. shared.Blocks.Skip(1)] };
        a.True(SourceReturns.Rewrite(overwritten).Blocks[0].Statements is
            [ManagedStore { Value: ConstantValue { Bits: 1 } }, ManagedReturn { Value: ConstantValue { Bits: 1 } }],
            "展开挂起尾部后删除紧邻且被覆盖的负状态");
        var observed = overwritten with { Blocks = [overwritten.Blocks[0] with { Statements =
            [overwritten.Blocks[0].Statements[0], Read(0, state, "<>1__state"), shared.Blocks[0].Statements[0]] }, .. shared.Blocks.Skip(1)] };
        a.True(SourceReturns.Rewrite(observed).Blocks[0].Statements.OfType<ManagedStore>().Count() == 2,
            "两次写入之间有读取时保留中间状态");
        var current = new ManagedStore(0, Read(0, capture, "<>2__current").Value, new ConstantValue(0, type, 64));
        var saved = new ManagedStore(0, Read(0, state, "<time>5__2").Value,
            new BinaryValue(BinOp.Add, state, new ConstantValue(1, integer, 32), integer, 32));
        var suspended = new ManagedBody(body.Method, [new(0, [current, saved, write with { Value = new ConstantValue(1, integer, 32) },
            new ManagedReturn(0, new ConstantValue(1, result.Type, 1))])]);
        var reordered = SourceReturns.Rewrite(suspended).Blocks[0].Statements;
        a.True(reordered[0] == saved && reordered[1] == current, "独立的局部值写入先完成，current/state 挂起序列相邻");
        var readsCurrent = suspended with { Blocks = [suspended.Blocks[0] with { Statements =
            [current, saved with { Value = current.Target }, .. suspended.Blocks[0].Statements.Skip(2)] }] };
        a.True(SourceReturns.Rewrite(readsCurrent).Blocks[0].Statements[0] == current, "读取 current 的写入不能提前");
        var callBetween = suspended with { Blocks = [suspended.Blocks[0] with { Statements =
            [current, new ManagedCall(0, new(null!, null, [], false), null, false), .. suspended.Blocks[0].Statements.Skip(1)] }] };
        a.True(SourceReturns.Rewrite(callBetween).Blocks[0].Statements[0] == current, "不跨过调用调整挂起写入");
    }
}
