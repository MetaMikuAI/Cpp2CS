using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Managed.Analysis;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class ManagedChecks
{
    public const string Command = "managed";

    public static int Run()
    {
        var checks = new Assertions();
        var owner = new TypeDef
        {
            Index = 0, Assembly = "Checks", Namespace = "Checks", Name = "Container", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false,
        };
        TypeRef type = new GenericParameterRef("T", false, 0);
        var method = MethodRef.Open(new MethodDef
        {
            Index = 0, Owner = owner, Name = "Apply", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, ReturnType = type,
        });
        var local = new LocalValue(new LocalId(0), type, 32);
        var other = new LocalValue(new LocalId(1), type, 32);
        var one = new ConstantValue(1, type, 32);
        var two = new ConstantValue(2, type, 32);
        var sum = new BinaryValue(BinaryOperator.Add, local, one, type, 32);
        ManagedBody Body(params ManagedBlock[] blocks) => new(method, blocks);
        ManagedBlock Block(ulong id, params ManagedStatement[] statements) => new(id, statements);
        ManagedJump Jump(ulong id, ulong target) => new(id, new(target, []));
        ManagedAssignment Assign(ulong id) => new(id, local, one);
        ulong[] Missing(ManagedBody body) => DefiniteInitialization.Uninitialized(body,
            new HashSet<ManagedValue> { local, other }, v => v == local || v == other ? [v] : []).ToArray();

        var body = Body(Block(0, Assign(1), new ManagedReturn(2, sum)));
        checks.True(body.Method == method && body.Blocks.Count == 1 && body.Regions.Count == 0,
            "构造方法体保留方法、块与默认异常区域");
        checks.True(local.Id != other.Id && (local with { Width = 64 }).Id == local.Id,
            "局部身份不依赖类型与位宽");
        checks.True(ManagedValues.Walk(sum).SequenceEqual([sum, local, one]), "值按先序遍历");
        var mapped = ManagedValues.Map(body, v => v == one ? two : v);
        checks.True(mapped.Blocks[0].Statements[0] is ManagedAssignment { Value: ConstantValue { Bits: 2 } }
            && body.Blocks[0].Statements[0] is ManagedAssignment { Value: ConstantValue { Bits: 1 } },
            "方法体映射重建语句且不修改输入");
        checks.True(ManagedStructure.Same(body, ManagedValues.Map(body, v => v)), "恒等映射保持方法体结构");
        checks.True(!ManagedStructure.Same(body, mapped), "结构比较识别值变化");
        var edge = new ManagedEdge(1, [new(other, local), new(local, other)]);
        var jump = new ManagedJump(3, edge);
        checks.True(ManagedValues.Edges(jump).SequenceEqual([edge])
            && ManagedValues.CopiedValues(jump).SequenceEqual([local, other]), "边遍历保留并行复制的源次序");
        checks.True(ManagedValues.Map(jump, v => v == local ? one : v) is ManagedJump
            { Edge.Copies: var copies } && copies[0].Target == other && copies[0].Value == one,
            "语句映射改变复制源且保留复制目标");
        checks.True(Missing(body).Length == 0, "先赋值后读取通过");
        checks.True(Missing(Body(Block(0, new ManagedReturn(1, sum)))).SequenceEqual([1UL]),
            "表达式内未赋值读取报告语句位置");
        checks.True(Missing(Body(Block(0, new ManagedAssignment(1, local, sum)))).SequenceEqual([1UL]),
            "自引用赋值先读后写");
        checks.True(Missing(Body(Block(0, new ManagedStore(1, local, one), new ManagedReturn(2, local)))).Length == 0,
            "写入已定位的存储叶子建立赋值");
        var call = new ManagedCall(1, new(method, null, [local], false), local);
        checks.True(Missing(Body(Block(0, call, new ManagedReturn(2, local)))).SequenceEqual([1UL]),
            "调用先读取实参，再定义结果");
        ManagedBody Diamond(bool both) => Body(
            Block(0, new ManagedBranch(1, one, new(1, []), new(2, []))),
            Block(1, Assign(2), Jump(3, 3)),
            both ? Block(2, Assign(4), Jump(5, 3)) : Block(2, Jump(5, 3)),
            Block(3, new ManagedReturn(6, local)));
        checks.True(Missing(Diamond(true)).Length == 0, "合流的两条路径均赋值才通过");
        checks.True(Missing(Diamond(false)).SequenceEqual([6UL]), "合流保留未赋值路径");
        var loop = Body(Block(0, Jump(1, 1)),
            Block(1, new ManagedAssignment(2, local, sum), new ManagedBranch(3, one, new(1, []), new(2, []))),
            Block(2, new ManagedReturn(4, local)));
        checks.True(Missing(loop).SequenceEqual([2UL]), "循环回边不能证明首次迭代已赋值");
        var handler = Body(Block(0, Jump(1, 1)), Block(1, Assign(2), new ManagedReturn(3, local)),
            Block(2, new ManagedReturn(4, local))) with
        {
            Regions = [new([1], 2, [2], null, ManagedRegionKind.Fault)],
        };
        checks.True(Missing(handler).SequenceEqual([4UL]), "保护块内的赋值不能证明异常入口已赋值");
        var initializedHandler = handler with { Blocks = [Block(0, Assign(0), Jump(1, 1)), .. handler.Blocks.Skip(1)] };
        checks.True(Missing(initializedHandler).Length == 0, "进入保护块前的赋值传给异常入口");
        checks.True(Missing(Body(Block(0, jump), Block(1, new ManagedReturn(4, null)))).SequenceEqual([3UL]),
            "并行复制先读取全部源值");

        foreach (var width in new[] { 32, 64 })
        {
            var array = new NewArrayValue(new ArrayRef(type, 1), one, width);
            var addressed = new AddressValue(local, width);
            var pointerBody = Body(Block(0, new ManagedReturn(1, array), new ManagedReturn(2, addressed)));
            var renamed = ManagedTypeMap.Map(pointerBody, t => t);
            checks.True(ManagedStructure.Same(pointerBody, renamed)
                && array.Width == width && addressed.Width == width, "引用与地址宽度由调用方给出并在类型映射后保留");
        }
        var renamedLocal = ManagedTypeMap.Map(body, t => t == type ? new ByRefRef(type) : t, _ => 64);
        checks.True(renamedLocal.Blocks[0].Statements[0] is ManagedAssignment { Target.Width: 64, Target.Id.Index: 0 },
            "类型代换重算局部宽度并保留身份");
        var root = new RecoveryHole(1, "无法定位") { Id = 1, Code = "recovery.Location" };
        var derived = new RecoveryHole(2, "依赖失败", true) { Id = 2, CauseId = root.Id };
        var partial = Body(Block(0, new ManagedHole(1, root.Reason, true)));
        var result = new MethodRecoveryResult(method, 0, null, [root, derived]) { Partial = partial };
        checks.True(root.Category == "memory" && (root with { Reason = "另一说明" }).Category == root.Category,
            "洞的分类来自编码而非文本");
        checks.True(result.Body is null && result.Partial == partial && derived.CauseId == root.Id && derived.Derived,
            "部分方法体与完整产物分离，派生洞保留根因编号");
        return checks.Finish("Managed");
    }
}
