using System.Numerics;
using System.Runtime.CompilerServices;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.State;

/// <summary>
/// 映像里加载之后不再改变的数据（只读数据与只读的重定位区）。读取这样的位置得到的就是文件里的内容：
/// 没有重定位时是常量，有指针重定位且指向映像内时是映像地址。导入的指针、与重定位部分重叠的读取不在此列。
/// </summary>
public sealed class ImageContents
{
    private static readonly ConditionalWeakTable<IImage, ImageContents> cache = [];
    private readonly IImage image;
    private readonly ulong[] starts;
    private readonly ulong[] ends;

    private ImageContents(IImage image)
    {
        this.image = image;
        var ordered = image.Relocations.OrderBy(r => r.Offset).ToArray();
        starts = new ulong[ordered.Length];
        ends = new ulong[ordered.Length];
        ulong furthest = 0;
        for (int i = 0; i < ordered.Length; i++)
        {
            starts[i] = ordered[i].Offset;
            // 前缀上的最大末尾，使嵌套或重叠的记录也能用一次二分判断。
            furthest = Math.Max(furthest, ordered[i].Offset + (ulong)ordered[i].Width);
            ends[i] = furthest;
        }
    }

    /// <summary>同一个映像只建立一次索引。</summary>
    public static ImageContents Of(IImage image) => cache.GetValue(image, i => new(i));

    private bool Relocated(ulong start, ulong bytes)
    {
        int low = 0, high = starts.Length;
        while (low < high)
        {
            int mid = low + (high - low) / 2;
            if (starts[mid] < start + bytes) low = mid + 1; else high = mid;
        }
        return low > 0 && ends[low - 1] > start;
    }

    private bool Immutable(ulong start, ulong bytes)
    {
        while (bytes > 0)
        {
            var info = image.Query(start);
            if (info.Storage != StorageKind.FileContent || info.Writable || info.AvailableBytes == 0) return false;
            ulong take = Math.Min(bytes, info.AvailableBytes);
            start += take; bytes -= take;
        }
        return true;
    }

    /// <summary>诊断用：映像偏移处的存储类别。</summary>
    public string Describe(ulong offset)
    {
        var info = image.Query(offset);
        string relocated = Relocated(offset, (ulong)image.PointerWidth) ? "（带重定位）" : "";
        return info.Storage switch
        {
            StorageKind.Unmapped => "未映射",
            StorageKind.ZeroFill => "可写无初值",
            _ => info.Executable ? "代码" : (info.Writable ? "可写有初值" : "只读") + relocated,
        };
    }

    /// <summary>位置在不变的映像数据里并且内容可以静态确定时返回它的值，否则返回 null。</summary>
    public Term? Read(NativeFunction function, Location location)
    {
        if (location.Region != Region.Image || location.Offset is not { } offset || offset < 0 || offset > ulong.MaxValue) return null;
        if (location.Width <= 64 ? location.Width is not (8 or 16 or 32 or 64) : location.Width % 8 != 0) return null;
        ulong start = (ulong)offset, bytes = (ulong)(location.Width / 8);
        if (start > ulong.MaxValue - bytes) return null;
        if (!Immutable(start, bytes)) return null;
        var terms = function.Terms;
        if (!Relocated(start, bytes))
        {
            if (location.Width <= 64) return terms.Constant(image.ReadUnsigned(start, (int)bytes), location.Width);
            var content = new byte[(int)bytes];
            image.ReadBytes(start, content);
            return terms.Constant(new BigInteger(content, isUnsigned: true, isBigEndian: image.ByteOrder == ByteOrder.BigEndian), location.Width);
        }
        if (location.Width != image.PointerWidth * 8 || function.ImageBase is not { } imageBase) return null;
        return image.ReadPointer(start) switch
        {
            PointerTarget.Internal { Offset: 0 } => imageBase,
            PointerTarget.Internal target => terms.Apply(new CoreOperator(CoreOperation.Add), imageBase.Width, imageBase,
                terms.Constant(target.Offset, imageBase.Width)),
            _ => null,
        };
    }
}
