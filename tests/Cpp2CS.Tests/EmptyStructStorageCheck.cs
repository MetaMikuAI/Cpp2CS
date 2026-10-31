using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Tests;

internal static class EmptyStructStorageCheck
{
    [Command("empty-struct-storage", "空 awaiter 的栈位置与数值使用边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new MethodRecovery(facts, types);
        const ulong entry = 0x4deac48;
        var method = facts.Registrations.Entries.First(e => e.Address == entry).Method!;
        var context = new RecoveryScope(recovery, method, entry);
        var a = new Assertions();
        a.True(context.Prepare() && context.Analyze() is null, "实际异步方法分析成功");
        var frame = context.State.Frames.frameRegions.First(r => r.Type is DefinitionRef d
            && types.Kind(d) == TypeKind.Struct && facts.Layouts.Of(d) is { Fields.Count: 0 });
        a.True(context.FrameLocation(frame, 0, 8).TryGet(out var value, out _) && value is LocalValue
            && value.Type.Equals(frame.Type), "占位字节保留空结构体的身份");
        a.Equal(false, context.FrameLocation(frame, 1, 8).TryGet(out _, out _), "跨帧访问仍拒绝");
        a.Equal(false, context.Coerce(value, types.Byte, 0).TryGet(out _, out _), "不能把空结构体占位字节伪造为整数");
        a.Equal(false, context.Pack(new Fragment([], types.UInt64, 8)).TryGet(out _, out _), "空片仍不可作为数值使用");
        return a.Finish("empty-struct-storage");
    }
}
