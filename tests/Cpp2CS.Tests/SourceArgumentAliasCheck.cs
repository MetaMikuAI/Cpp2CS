using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceArgumentAliasCheck
{
    [Command("source-argument-aliases", "ref 参数的分支副本与未初始化路径", Gate = Gate.Unit)]
    public static int Run()
    {
        var type = new ByRefRef(new PrimitiveRef("I4"));
        var argument = new ArgumentValue(0, type, 64);
        var local = new LocalValue(new(Storage.Temp(1), 1), type, 64);
        var other = new LocalValue(new(Storage.Temp(2), 1), type, 64);
        var owner = new TypeDef { Index = -1, Assembly = "Aliases.Tests.dll", Namespace = "Tests", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodDef { Index = -1, Owner = owner, Name = "Use", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, ReturnType = type };
        ManagedBody Body(params ManagedBlock[] blocks) => new(new(method, [], []), blocks);
        var branch = new ManagedBranch(0, new ArgumentValue(1, new PrimitiveRef("Boolean"), 32),
            new(4, [new(local, argument)]), new(4, [new(local, argument)]));
        var sample = Body(new(0, [branch]), new(4, [new ManagedReturn(4, local)]));
        var a = new Assertions();
        var folded = SourceArgumentAliases.Rewrite(sample);
        a.True(folded.Blocks[1].Statements[0] is ManagedReturn { Value: ArgumentValue }, "相同参数的两条边直接返回参数");
        a.True(folded.Blocks[0].Statements.SelectMany(ManagedValues.Edges).All(e => e.Copies.Count == 0), "已消去的引用副本不再赋值");
        var conflict = sample with { Blocks = [new(0, [branch with { Fallthrough = new(4, [new(local, new ArgumentValue(2, type, 64))]) }]), sample.Blocks[1]] };
        a.True(ReferenceEquals(conflict, SourceArgumentAliases.Rewrite(conflict)), "不同参数来源不合并");
        var missing = sample with { Blocks = [new(0, [branch with { Fallthrough = new(4, []) }]), sample.Blocks[1]] };
        a.True(ReferenceEquals(missing, SourceArgumentAliases.Rewrite(missing)), "一条边未赋值时保留默认引用");
        var early = Body(new ManagedBlock(0, [new ManagedAssignment(0, other, local), new ManagedAssignment(1, local, argument), new ManagedReturn(2, other)]));
        a.True(ReferenceEquals(early, SourceArgumentAliases.Rewrite(early)), "间接来源在赋值前被读取时也不能替换");
        var escaped = Body(new ManagedBlock(0, [new ManagedAssignment(0, local, argument), new ManagedReturn(1, new AddressValue(local))]));
        a.True(ReferenceEquals(escaped, SourceArgumentAliases.Rewrite(escaped)), "引用局部本身取地址时保留");
        var through = Body(new ManagedBlock(0, [new ManagedAssignment(0, local, argument), new ManagedAssignment(1, other, local), new ManagedReturn(2, other)]));
        a.True(SourceArgumentAliases.Rewrite(through).Blocks[0].Statements.ToArray() is [ManagedReturn { Value: ArgumentValue }], "连续引用副本归并到同一参数");
        var caught = Body(new(0, [new ManagedAssignment(0, local, argument), new ManagedReturn(1, local)]), new(8, [new ManagedReturn(8, local)]))
            with { Regions = [new([0], 8, [8], null, ManagedRegionKind.Catch)] };
        a.True(ReferenceEquals(caught, SourceArgumentAliases.Rewrite(caught)), "handler 不借用 try 块内尚未发生的赋值");
        var storage = new LocalValue(new(Storage.Temp(3), 1), type.Element, 32);
        var address = new AddressValue(storage);
        var localAddress = Body(new ManagedBlock(0, [new ManagedAssignment(0, local, address),
            new ManagedStore(1, storage, new ConstantValue(7, storage.Type, 32)), new ManagedReturn(2, new IndirectValue(local, storage.Type))]));
        var addressFolded = SourceArgumentAliases.Rewrite(localAddress);
        a.True(addressFolded.Blocks[0].Statements is [ManagedStore, ManagedReturn { Value: IndirectValue { Address: var root } }]
            && root == address, "局部存储的地址保持稳定，保留其间值写入");
        var alternatives = sample with { Blocks = [new(0, [branch with { Taken = new(4, [new(local, address)]),
            Fallthrough = new(4, [new(local, new AddressValue(storage with { Variable = new(Storage.Temp(4), 1) }))]) }]), sample.Blocks[1]] };
        a.True(ReferenceEquals(alternatives, SourceArgumentAliases.Rewrite(alternatives)), "不同局部存储的条件引用不能直接归并");
        return a.Finish("source-argument-aliases");
    }
}
