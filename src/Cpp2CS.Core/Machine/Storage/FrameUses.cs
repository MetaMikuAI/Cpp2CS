using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Storage;



/// <summary>精确访存按字节区间相交；逃逸地址只有取得签名长度后才限制其可访问范围。</summary>
internal static class FrameUses
{
    internal static bool Touches(Stmt statement, long offset, int bytes, Func<Call, int, int?> extent)
    {
        bool Overlaps(long start, int? size) => start < offset + bytes && (size is null || offset < start + size);
        bool Read(Expr expression, int? size = null) => expression switch
        {
            Load { Address: FrameAddress frame } load => Overlaps(frame.Offset, load.Width / 8),
            FrameAddress frame => Overlaps(frame.Offset, size),
            _ => ExprMap.Children(expression).Any(e => Read(e)),
        };
        return statement switch
        {
            Store { Target: FrameAddress frame } store => Overlaps(frame.Offset, store.Value.Width / 8) || Read(store.Value),
            Call call => Read(call.Target) || call.DelegateReceiver is { } receiver && Read(receiver)
                || call.Arguments.Select((argument, index) => Read(argument, extent(call, index))).Any(touched => touched),
            _ => ExprMap.Operands(statement).Any(e => Read(e)),
        };
    }
}
