using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private sealed record StackEnum(DefinitionRef Type, Expr Value, long Offset, Store[] Stores);
        private readonly Dictionary<Call, StackEnum> stackEnums = new(ReferenceEqualityComparer.Instance);

        /// <summary>Il2CppFakeBox 的类指针、栈标记和枚举值组成临时装箱；仅接收不逃逸的 Enum 实例调用。</summary>
        [Analysis("栈上枚举", 28, After = ["异常值", "栈上调用"])]
        private void PrepareStackEnums()
        {
            var candidates = new Dictionary<Call, StackEnum>(ReferenceEqualityComparer.Instance);
            foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Store { Target: FrameAddress }) continue;
                var stores = new List<Store>();
                foreach (var statement in Straight(block, i - 1))
                {
                    if (statement is Define or Nop) continue;
                    if (statement is Store { Target: FrameAddress } store && stores.Count < 3) { stores.Add(store); continue; }
                    if (statement is Call call && stores.Count == 3 && stores.Select(s => ((FrameAddress)s.Target).Offset).Distinct().Count() == 3
                        && Receiver(call) is { } receiver && FrameOffset(receiver) is { } offset
                        && Resolve(call) is { Method: { IsStatic: false, Owner.FullName: "System.Enum" } } callee
                        && call.Arguments.Skip(1).All(a => !ExprMap.Walk(a).Any(p => FrameOffset(p) is not null)))
                    {
                        var klass = stores.SingleOrDefault(s => ((FrameAddress)s.Target).Offset == offset + RuntimeLayout.ObjectKlass);
                        var monitor = stores.SingleOrDefault(s => ((FrameAddress)s.Target).Offset == offset + RuntimeLayout.ObjectMonitor);
                        var data = stores.SingleOrDefault(s => ((FrameAddress)s.Target).Offset == offset + RuntimeLayout.ObjectHeaderSize);
                        if (klass?.Value is Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsEnum: true } type }
                            && monitor?.Value is Const { Width: 64, Value: ulong.MaxValue } && data is not null
                            && data.Value.Width == types.Bits(type))
                        {
                            candidates[call] = new(type, data.Value, offset, stores.ToArray());
                            resolved[call] = (callee, Pinned);
                        }
                    }
                    break;
                }
            }
            foreach (var group in candidates.GroupBy(p => p.Value.Offset))
            {
                var members = group.ToArray();
                var end = group.Key + RuntimeLayout.ObjectHeaderSize + members.Max(p => types.Size(p.Value.Type));
                var covered = members.SelectMany(p => p.Value.Stores.Cast<Stmt>().Append(p.Key)).ToHashSet(ReferenceEqualityComparer.Instance);
                // 地址被保存、转交或另行读取时，不能只删除局部对象头。
                if (blocks.SelectMany(b => b.Statements).Any(s => !covered.Contains(s)
                    && ExprMap.Operands(s).SelectMany(ExprMap.Walk).Any(e => FrameOffset(e) is { } at && at >= group.Key && at < end))) continue;
                foreach (var (call, box) in members)
                {
                    stackEnums[call] = box;
                    dropped.UnionWith(box.Stores);
                }
            }
        }
    }
}
