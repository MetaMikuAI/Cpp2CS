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
        Dispatch(a);
        return a.Finish("source-returns");
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
    }
}
