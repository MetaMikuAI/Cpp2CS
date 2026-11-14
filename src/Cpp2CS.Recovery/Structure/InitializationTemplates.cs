using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Model;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Structure;

/// <summary>生成代码的零／非零测试；布尔字节只使用低位时保留实际测试的位。</summary>
internal sealed record InitializationTest(ReadIdentity Read, bool ZeroWhenTrue, int Low, int Width)
{
    internal static InitializationTest? Of(Term condition)
    {
        bool zero = false;
        while (condition.Operator is CoreOperator { Operation: CoreOperation.Not })
        { zero = !zero; condition = condition.Operands[0]; }
        if (condition.Operator is CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual } op)
        {
            var value = condition.Operands.FirstOrDefault(t => t.ConstantValue is not { IsZero: true });
            if (value is null || !condition.Operands.Any(t => t.ConstantValue is { IsZero: true })) return null;
            zero ^= op.Operation == CoreOperation.Equal;
            condition = value;
        }
        else if (condition.Width != 1) return null;
        int low = 0, width = condition.Width;
        if (condition.Kind == TermKind.Slice) { low = condition.SliceLow!.Value; condition = condition.Operands[0]; }
        return condition.Identity is ResultAtom { Definition: ReadIdentity read } ? new(read, zero, low, width) : null;
    }
}

internal readonly record struct InitializationPrefix(FlowEdge Edge, FieldName? Field, Location? Flag, int TestLow = 0, int TestWidth = 8, MethodRef? InternalCall = null);
internal sealed record InitializationGroup(Point After, ImmutableArray<Statement> Statements, string Evidence)
{
    internal Term? WrittenResult { get; init; }
}

/// <summary>用共同的前沿查询逐项验证初始化模板前缀；分支、共享入口及其他效果终止凭据。</summary>
internal sealed class InitializationPrefixQuery(StateQueries state, CallNamingQuery calls, ValueNamingQuery names, IImage? image)
    : Query<InitializationPrefix, InitializationGroup>
{
    internal static IEnumerable<RuntimeStateRepresentation> Representations(RuntimeOperation operation)
    {
        if (operation is not { Observation: RuntimeObservation.IdempotentEvent, DoesNotReturn: false, Idempotence: { } post }) yield break;
        foreach (var representation in post.Representations)
            if (representation.Test == RuntimeStateTest.Nonzero && representation.Field is not null
                && (representation.Record == "Il2CppClass" && operation.Result.Kind == RuntimeValueKind.Void
                    || representation.Record == "MethodInfo" && operation.MetadataInitialization?.Input == representation.Input
                    && operation.Result.ReturnInput == representation.Input)) yield return representation;
    }

    public override Outcome<InitializationGroup> Compute(QueryContext c, InitializationPrefix key)
    {
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<InitializationGroup>();
        var blocks = index.Value.Blocks;
        var statements = ImmutableArray.CreateBuilder<Statement>();
        var evidence = new List<string>();
        Outcome<InitializationGroup> No(string code, string text, Reason? cause = null) =>
            Outcome<InitializationGroup>.Failure(new("structure.init-guard." + code, text, cause));
        // 前沿只越过无语句的单入口跳转；调用在执行前停下，展开边由调用本身保留。
        var frontier = new EventFrontierQuery((context, point) => Outcome<bool>.Success(
            point.Before == 0 && (point.Block == key.Edge.Source || blocks[point.Block].Handler is not null || (index.Value.Predecessors[point.Block].Length != 1 || !blocks[point.Block].Merges.IsEmpty))
            || point.Before < blocks[point.Block].Statements.Length || blocks[point.Block].End is not Jump));
        var start = FrontierStart.FromEdge(key.Edge);
        var seen = new HashSet<Point>(); int initializers = 0; Term? resolvedCall = null;
        while (true)
        {
            if (c.Step() is { } budget) return Outcome<InitializationGroup>.Failure(budget);
            var next = c.Get(frontier, start); if (!next.IsSuccess) return next.Propagate<InitializationGroup>();
            if (next.Value.HasCycle || next.Value.ReachesExit || next.Value.Stops.Count != 1)
                return No("event-missing", "初始化事件组完成前存在循环或出口。");
            var point = next.Value.Stops.Single(); var block = blocks[point.Block];
            if (!seen.Add(point)) return No("event-missing", "初始化事件组完成前存在循环。");
            if (point.Before == 0 && (point.Block == key.Edge.Source || block.Handler is not null || (index.Value.Predecessors[point.Block].Length != 1 || !block.Merges.IsEmpty)))
                return No("shared-prefix", "初始化事件组入口有其他前驱、合流或处理入口。");
            if (point.Before == block.Statements.Length)
                return No("branch-before-event", "初始化事件组完成前遇到分支或结局。");
            var statement = block.Statements[point.Before];
            if (statement is MemoryRead read)
            {
                if (!FixedRead(c, read, out var why)) return No("effect-before-event", "初始化事件组前有不能证明定值或不可变的读取。", why);
                statements.Add(read);
            }
            else if (statement is Call call && !call.DoesNotReturn && c.Get(calls, call.Identity) is { IsSuccess: true } classified)
            {
                var named = classified.Value;
                if (key.InternalCall is { } internalCall)
                {
                    if (resolvedCall is not null || named.Operation?.Name != "ResolveInternalCall" || call.Unwind is not null
                        || named.Inputs?.GetValueOrDefault("name")?.Source is not TermSource name
                        || named.Result?.Source is not TermSource result || image is null
                        || !InternalCallNames.Matches(c, state, image, name.Term, internalCall))
                        return No("icall-name", "解析调用或只读名字串与包装的内部调用定义不符。");
                    resolvedCall = result.Term; statements.Add(call);
                    start = new(new(point.Block, point.Before + 1));
                    continue;
                }
                if (key.Field is { } field && named.Operation is { } operation)
                {
                    foreach (var representation in Representations(operation))
                    {
                        if (representation.Record != field.Record || field.Field != representation.Record + "." + representation.Field
                            || representation.Test != RuntimeStateTest.Nonzero
                            || named.Inputs?.GetValueOrDefault(representation.Input)?.Source is not TermSource owner) continue;
                        var ownerName = names.FixedValue(c, owner.Term);
                        var expected = field.Owner is EntityName entity ? entity with { Slot = null } : field.Owner;
                        if (!ownerName.IsSuccess || ownerName.Value != expected)
                            return No("entity-mismatch", "守卫状态与幂等事件的对象不同");
                        statements.Add(call);
                        return Outcome<InitializationGroup>.Success(new(new(point.Block, point.Before + 1), statements.ToImmutable(), representation.Evidence + "；" + operation.Evidence));
                    }
                }
                if (key.Flag is not null && named.Operation?.Name == "InitializeMetadata"
                    && named.Inputs?.GetValueOrDefault("slot")?.Source is TermSource slot)
                {
                    var address = c.Get(state.Resolve, slot.Term);
                    var location = address.IsSuccess ? c.Get(state.Locations, new(address.Value, c.Snapshot.AddressWidth)) : default;
                    if (!location.IsSuccess || location.Value is not { Region: Region.Image, Offset: not null })
                        return No("metadata-slot", "元数据初始化实参不是映像里的常量槽位地址。", location.Why);
                    initializers++; statements.Add(call); evidence.Add(named.Operation.Evidence);
                }
                else return No("effect-before-event", "初始化事件组完成前遇到其他调用。");
            }
            else if (statement is MemoryWrite write && key.Flag is { } flag)
            {
                var address = c.Get(state.Resolve, write.Address);
                var location = address.IsSuccess ? c.Get(state.Locations, new(address.Value, write.Width)) : default;
                var value = c.Get(state.Resolve, write.Value);
                if (key.InternalCall is not null)
                {
                    if (write.Release || resolvedCall is null || write.Width != c.Snapshot.AddressWidth || !location.IsSuccess || location.Value != flag
                        || !value.IsSuccess || value.Value != resolvedCall)
                        return No("icall-write", "缓存写回不是该次解析调用的完整结果。");
                    statements.Add(write);
                    return Outcome<InitializationGroup>.Success(new(new(point.Block, point.Before + 1), statements.ToImmutable(),
                        "内部调用解析结果写回同一缓存；生成包装的缓存正常返回后稳定") { WrittenResult = resolvedCall });
                }
                if (write.Width != 8 || !location.IsSuccess || location.Value != flag
                    || !value.IsSuccess || value.Value.ConstantValue is not { IsZero: false } constant
                    || (constant >> key.TestLow & ((System.Numerics.BigInteger.One << key.TestWidth) - 1)) == 0)
                    return No("effect-before-event", "初始化事件组完成前遇到其他写入。");
                if (initializers == 0) return No("metadata-missing", "标志置位之前没有元数据初始化操作。");
                statements.Add(write);
                return Outcome<InitializationGroup>.Success(new(new(point.Block, point.Before + 1), statements.ToImmutable(), string.Join("；", evidence.Distinct())));
            }
            else return No("effect-before-event", "初始化事件组完成前遇到其他效果。");
            start = new(new(point.Block, point.Before + 1));
        }
    }

    private bool FixedRead(QueryContext c, MemoryRead read, out Reason? why)
    {
        why = null;
        if (read.Acquire) return false;
        var value = c.Get(state.Read, read.Identity);
        if (value.IsSuccess && value.Value != read.Result && !value.Value.ContainsUndefined
            && !SnapshotRewrite.Dependencies([value.Value]).Any(t => t.Identity is MemoryAtom or MemoryMerge or EdgeReadAtom)) return true;
        var fixedValue = names.FixedValue(c, read.Result);
        if (fixedValue.IsSuccess && fixedValue.Value is EntityName or FieldName or ArrayElementName) return true;
        var address = c.Get(state.Resolve, read.Address);
        var location = address.IsSuccess ? c.Get(state.Locations, new(address.Value, read.Width)) : default;
        if (image is not null && location.IsSuccess && location.Value is { Region: Region.Image, Offset: { } offset }
            && offset >= 0 && offset <= ulong.MaxValue)
        {
            var info = image.Query((ulong)offset);
            if (!info.Writable && info.Storage == StorageKind.FileContent && info.AvailableBytes >= (ulong)((read.Width + 7L) / 8)) return true;
        }
        why = value.IsSuccess ? new("state.read-not-fixed", "读取仍依赖内存版本，未证明为保存值或不可变位置。") : value.Why;
        return false;
    }
}
