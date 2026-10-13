using System.Collections.Immutable;
using System.Numerics;

namespace Cpp2CS.Nir;

public enum NirMemoryOrder { Unordered, Relaxed, Acquire, Release, AcquireRelease, SequentiallyConsistent }
public enum NirAtomicCode { Exchange, Add, Sub, And, Or, Xor, Neg, Not }

public sealed record NirAtomicRmw(NirValue Result, NirValue Address, NirValue Value, NirAtomicCode Code,
    NirByteOrder Order, NirMemoryOrder MemoryOrder, NirEffectFlow Flow) : NirOperation;
public sealed record NirCompareExchange(NirValue OldValue, NirValue Success, NirValue Address,
    NirValue Expected, NirValue Replacement, NirByteOrder Order, NirMemoryOrder SuccessOrder,
    NirMemoryOrder FailureOrder, NirEffectFlow Flow, bool WriteBackOnFailure = false) : NirOperation;
public sealed record NirFence(NirMemoryOrder MemoryOrder, NirEffectFlow Flow) : NirOperation;

// 数值均按操作声明的字节序解释；失败事件不含成功的读写值。
public sealed record NirMemoryObservation(string? Space, BigInteger? Address, int Width, int AtomicWidth,
    NirMemoryOrder Order, BigInteger? ReadValue = null, BigInteger? WrittenValue = null, bool? ExchangeSucceeded = null);

public static class NirAtomicContract
{
    public static bool LoadOrder(NirMemoryOrder order, int atomicWidth) => atomicWidth == 0
        ? order == NirMemoryOrder.Unordered
        : order is NirMemoryOrder.Relaxed or NirMemoryOrder.Acquire or NirMemoryOrder.SequentiallyConsistent;
    public static bool StoreOrder(NirMemoryOrder order, int atomicWidth) => atomicWidth == 0
        ? order == NirMemoryOrder.Unordered
        : order is NirMemoryOrder.Relaxed or NirMemoryOrder.Release or NirMemoryOrder.SequentiallyConsistent;
    public static bool RmwOrder(NirMemoryOrder order) => order is NirMemoryOrder.Relaxed or NirMemoryOrder.Acquire or
        NirMemoryOrder.Release or NirMemoryOrder.AcquireRelease or NirMemoryOrder.SequentiallyConsistent;
    public static bool FenceOrder(NirMemoryOrder order) => order is NirMemoryOrder.Acquire or NirMemoryOrder.Release or
        NirMemoryOrder.AcquireRelease or NirMemoryOrder.SequentiallyConsistent;
    public static bool FailureOrder(NirMemoryOrder success, NirMemoryOrder failure) => RmwOrder(success) && failure switch
    {
        NirMemoryOrder.Relaxed => true,
        NirMemoryOrder.Acquire => success is NirMemoryOrder.Acquire or NirMemoryOrder.AcquireRelease or NirMemoryOrder.SequentiallyConsistent,
        NirMemoryOrder.SequentiallyConsistent => success == NirMemoryOrder.SequentiallyConsistent,
        _ => false
    };
    public static bool AtomicWidth(int width, int atomicWidth) => atomicWidth == 0 ||
        atomicWidth > 0 && atomicWidth % 8 == 0 && atomicWidth <= width && width % atomicWidth == 0;

    internal static ImmutableArray<byte> Bytes(BigInteger value, int width, NirByteOrder order)
    {
        var result = new byte[width / 8];
        var encoded = value.ToByteArray(isUnsigned: true, isBigEndian: order == NirByteOrder.Big);
        encoded.CopyTo(result, order == NirByteOrder.Big ? result.Length - encoded.Length : 0);
        return [.. result];
    }
}
