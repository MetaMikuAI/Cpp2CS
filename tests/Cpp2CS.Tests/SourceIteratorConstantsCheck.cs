using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceIteratorConstantsCheck
{
    [Command("source-iterator-constants", "状态等值边的宽副本常量与合流、写入边界", Gate = Gate.Unit)]
    public static int Run()
    {
        TypeDef Type(string ns, string name) => new() { Index = -1, Assembly = "Sample", Namespace = ns, Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        MethodDef Method(TypeDef owner, string name) => new() { Index = -1, Owner = owner, Name = name, Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = new PrimitiveRef("Boolean") };
        var owner = Type("Tests", "Iterator");
        owner.Interfaces = [new DefinitionRef(Type("System.Collections", "IEnumerator"), [])];
        owner.CustomAttributes = [new(Method(Type("System.Runtime.CompilerServices", "CompilerGeneratedAttribute"), ".ctor"), [], [], [])];
        var type = new DefinitionRef(owner, []);
        var integer = new PrimitiveRef("I4");
        var wide = new PrimitiveRef("U8");
        var state = new LocalValue(new(Storage.Temp(0), 1), wide, 64);
        var result = new LocalValue(new(Storage.Temp(1), 1), wide, 64);
        var field = new FieldValue(new ArgumentValue(-1, type, 64), new(new FieldDef { Index = -1, Owner = owner,
            Name = "<>1__state", Type = integer, Attributes = FieldAttributes.Private, Offset = 16 }, type), integer, 32);
        var assign = new ManagedAssignment(0, state, new ConversionValue(ConvKind.ZeroExtend, field, wide, 64));
        ManagedBody Body(Cond condition, uint value) => new(new(Method(owner, "MoveNext"), [], []),
            [new(0, [assign, new ManagedBranch(0, new ComparisonValue(condition,
                new ConversionValue(ConvKind.Truncate, state, integer, 32), new ConstantValue(value, integer, 32), new PrimitiveRef("Boolean")),
                new(1, [new(result, state)]), new(2, [new(result, state)]))]),
                new(1, [new ManagedReturn(1, result)]), new(2, [new ManagedReturn(2, result)])]);
        var a = new Assertions();
        foreach (var condition in new[] { Cond.Eq, Cond.Ne })
            foreach (var value in new uint[] { 0, 1, 0x80000000, uint.MaxValue })
            {
                var original = Body(condition, value);
                var rewritten = SourceIteratorConstants.Rewrite(original);
                var branch = (ManagedBranch)rewritten.Blocks[0].Statements[1];
                var equal = condition == Cond.Eq ? branch.Taken : branch.Fallthrough;
                var other = condition == Cond.Eq ? branch.Fallthrough : branch.Taken;
                a.Equal(new ConstantValue(value, wide, 64), equal.Copies.Single().Value, "32 位等值分支保留完整零扩展值");
                a.Equal(state, other.Copies.Single().Value, "不等分支没有唯一常量");
            }
        var body = Body(Cond.Eq, 0);
        var branch0 = (ManagedBranch)body.Blocks[0].Statements[1];
        var direct = body with { Blocks = [body.Blocks[0], new(1, [new ManagedReturn(1, state)]), body.Blocks[2]] };
        a.True(SourceIteratorConstants.Rewrite(direct).Blocks[1].Statements is [ManagedReturn { Value: ConstantValue { Bits: 0 } }],
            "后继语句沿用等值边的事实");
        var merge = direct with { Blocks = [.. direct.Blocks.Take(2), new(2, [new ManagedJump(2, new(1, []))])] };
        a.True(SourceIteratorConstants.Rewrite(merge).Blocks[1].Statements is [ManagedReturn { Value: LocalValue }],
            "不等路径合流后不能保留常量");
        var handler = direct with { Regions = [new([0], 1, [1], null, ManagedRegionKind.Fault)] };
        a.True(SourceIteratorConstants.Rewrite(handler).Blocks[1].Statements is [ManagedReturn { Value: LocalValue }],
            "异常入口不继承正常分支的事实");
        var mutation = body with { Blocks = [body.Blocks[0], new(1, [assign, new ManagedReturn(1, state)]), body.Blocks[2]] };
        a.Equal(mutation, SourceIteratorConstants.Rewrite(mutation), "多个定义不能作为固定状态快照");
        var copied = body with { Blocks = [new(0, [assign, branch0 with { Taken = new(1, [new(state, result)]) }]), .. body.Blocks.Skip(1)] };
        a.Equal(copied, SourceIteratorConstants.Rewrite(copied), "边复制写入排除固定状态快照");
        var addressed = body with { Blocks = [body.Blocks[0], new(1, [new ManagedReturn(1, new AddressValue(state))]), body.Blocks[2]] };
        a.Equal(addressed, SourceIteratorConstants.Rewrite(addressed), "地址逃逸的状态副本不能替换");
        var signed = body with { Blocks = [new(0, [assign with { Value = new ConversionValue(ConvKind.SignExtend, field, wide, 64) }, branch0]), .. body.Blocks.Skip(1)] };
        a.Equal(signed, SourceIteratorConstants.Rewrite(signed), "符号扩展不等于完整的 32 位无符号常量");
        var ordinary = body with { Method = new(Method(owner, "Read"), [], []) };
        a.Equal(ordinary, SourceIteratorConstants.Rewrite(ordinary), "普通方法不应用迭代器规则");
        return a.Finish("source-iterator-constants");
    }
}
