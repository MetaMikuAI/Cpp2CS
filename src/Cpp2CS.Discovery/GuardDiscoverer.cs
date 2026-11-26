using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Discovery;

/// <summary>
/// 守卫的发现器（设计 9.5、14.5）。起点是不可表达的分支：条件只依赖运行时状态上的读取
/// （方法的元数据初始化标志、类的初始化完成标志）。这样的分支不能留在输出里，必须由某条声明消费。
///   元数据惰性初始化的守卫没有托管操作可以归属：提出空操作的声明，占用这个分支与未就绪一臂上的效果。
///   类初始化的守卫属于它后面那个带类初始化分量的操作：对守卫之后同一个类的静态字段读写与静态方法调用，
///   提出 ldsfld、stsfld、call 的声明，占用守卫的分支、未就绪一臂上的类初始化与那次读写或调用。
/// 只提出声明；两臂在可观察行为上是否相同、守卫是否配给了正确的访问，都由证明决定。
/// </summary>
public sealed class GuardDiscoverer : IDiscoverer
{
    public string Name => "guard";

    /// <summary>一个守卫：分支所在的块，两臂重新汇合的块，未就绪一臂上的块（没有时为空），条件依赖的类（类初始化的守卫）。</summary>
    public sealed record Guard(BlockId Branch, BlockId Merge, BlockId? Arm, EntityRef? Class);

    public IEnumerable<Claim> Propose(FactView facts)
    {
        var graph = facts.Effects;
        if (graph.Failure is not null) yield break;
        var terms = graph.Snapshot.Terms;
        foreach (var guard in Guards(facts))
        {
            var occupied = new List<EffectRef> { EffectRef.Of(new EdgeId(guard.Branch, 0)), EffectRef.Of(new EdgeId(guard.Branch, 1)) };
            if (guard.Arm is { } arm)
                for (int i = 0; i < graph.Snapshot.OccurrenceCount(arm); i++)
                    if (graph.Effect(new(arm, i)) is { Kind: not NativeEffectKind.None }) occupied.Add(EffectRef.Of(new OccurrenceId(arm, i)));
            // 空操作：两臂在可观察行为上相同时成立。
            yield return new Claim("nop", null, [], new ProgramPoint(guard.Merge, 0), occupied, null);
            if (guard.Class is not { } type) continue;

            // 类初始化的守卫：汇合之后，同一个类的静态区上的读写。静态区的地址是类结构里静态区指针的一次读取的结果。
            int count = graph.Snapshot.OccurrenceCount(guard.Merge);
            for (int i = 0; i < count; i++)
            {
                // 同一个类的静态方法的调用：调用点先确保该类已初始化。
                if (graph.Effect(new(guard.Merge, i)) is { Kind: NativeEffectKind.Call, Callee: { HasThis: false, HasInitializer: true } callee } call
                    && callee.DeclaringType == type)
                    yield return new Claim("call.static.init", callee.Entity, call.Arguments, new ProgramPoint(guard.Merge, i + 1),
                        occupied.Append(EffectRef.Of(call.Occurrence)), call.Result);
                if (graph.Effect(new(guard.Merge, i)) is not { Kind: NativeEffectKind.Read or NativeEffectKind.Write } access) continue;
                var (root, offset) = access.Address is { Kind: TermKind.Operation, Op: Op.Add } sum && sum.Operands[1].IsConstant
                    ? (sum.Operands[0], unchecked((long)(ulong)sum.Operands[1].Value)) : (access.Address!, 0L);
                if (graph.RuntimeStateAddress(root) is not { Kind: TermKind.Operation, Op: Op.Add } statics
                    || statics.Operands[0] is not { Kind: TermKind.Entity } owner || owner.Entity != type
                    || !statics.Operands[1].IsConstant || statics.Operands[1].Value != (UInt128)facts.Layout.ClassStaticFieldsOffset) continue;
                if (facts.Metadata.StaticFieldAt(type, (int)offset) is not { } field || field.Type.StorageBits != access.Width
                    || field.Type.Kind == StackKind.Value) continue;
                var effects = occupied.Append(EffectRef.Of(access.Occurrence));
                var landing = new ProgramPoint(guard.Merge, i + 1);
                bool small = field.Type.Kind == StackKind.Int32 && access.Width < 32;
                if (access.Kind == NativeEffectKind.Read)
                {
                    var value = !small ? access.Value! : field.Type.Signed && !field.Type.TwoValued ? terms.SignExtend(access.Value!, 32) : terms.ZeroExtend(access.Value!, 32);
                    yield return new Claim("ldsfld.init", field.Entity, [], landing, effects, value);
                }
                else
                {
                    // 存进较窄位置的值在栈上的写法：低位相同的 32 位值。
                    var stored = access.Value!;
                    var value = !small ? stored
                        : stored is { Kind: TermKind.Slice, Offset: 0 } slice && slice.Operands[0].Width >= 32 ? terms.Slice(slice.Operands[0], 0, 32)
                        : terms.ZeroExtend(stored, 32);
                    yield return new Claim("stsfld.init", field.Entity, [value], landing, effects, null);
                }
            }
        }
    }

    /// <summary>
    /// 方法里的守卫：条件不可表达的二路分支，一臂直接到汇合块，另一臂经一个块到汇合块（或两臂各经一个块）。
    /// 条件依赖类结构上初始化完成标志的读取时，Class 是那个类。
    /// </summary>
    public static IEnumerable<Guard> Guards(FactView facts)
    {
        var graph = facts.Effects;
        var snapshot = graph.Snapshot;
        BlockId? Next(BlockId block) =>
            !graph.EndsInThrow(block) && snapshot.Terminator(block) is { Kind: TerminatorKind.Single } single
            && single.Exits[0].Kind == ExitKind.Target ? single.Exits[0].Target : null;
        foreach (int index in graph.Order)
        {
            var block = new BlockId(index);
            if (graph.EndsInThrow(block) || graph.Condition(block) is not { } condition) continue;
            var terminator = snapshot.Terminator(block);
            if (terminator.Kind != TerminatorKind.Branch || terminator.Exits[0].Kind != ExitKind.Target || terminator.Exits[1].Kind != ExitKind.Target) continue;
            // 条件的每个叶子是常量，或运行时状态上一次读取的结果。
            bool inexpressible = false, expressible = false;
            EntityRef? type = null;
            foreach (var leaf in Leaves(condition))
            {
                if (leaf.IsConstant) continue;
                if (graph.RuntimeStateAddress(leaf) is not { } address) { expressible = true; break; }
                inexpressible = true;
                if (address is { Kind: TermKind.Operation, Op: Op.Add } sum && sum.Operands[0] is { Kind: TermKind.Entity } owner
                    && sum.Operands[1].IsConstant && sum.Operands[1].Value == (UInt128)facts.Layout.ClassInitializedOffset) type = owner.Entity;
            }
            if (expressible || !inexpressible) continue;
            var (first, second) = (terminator.Exits[0].Target, terminator.Exits[1].Target);
            if (first == second) continue;
            if (Next(second) == first) yield return new Guard(block, first, second, type);
            else if (Next(first) == second) yield return new Guard(block, second, first, type);
        }
    }

    private static IEnumerable<Term> Leaves(Term term)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Term>();
        pending.Push(term);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (!seen.Add(current)) continue;
            if (current.Operands.Length == 0) yield return current;
            foreach (var operand in current.Operands) pending.Push(operand);
        }
    }
}
