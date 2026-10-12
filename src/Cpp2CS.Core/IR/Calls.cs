using System.Collections.Immutable;
using Cpp2CS.Abi;
using Cpp2CS.Model;

namespace Cpp2CS.IR;

public sealed class RegisterState
{
    private readonly ImmutableDictionary<string, Bits> values;
    public string Identity { get; }
    public RegisterState(string identity) : this(identity, ImmutableDictionary<string, Bits>.Empty) { }
    private RegisterState(string identity, ImmutableDictionary<string, Bits> values) { Identity = identity; this.values = values; }
    public static int Width(string name)
    {
        if (name.Length < 2 || !int.TryParse(name.AsSpan(1), out var n)) throw new ArgumentException("使用规范 X/V 寄存器名");
        return name[0] switch { 'X' when n is >= 0 and <= 30 => 64, 'V' when n is >= 0 and <= 31 => 128, _ => throw new ArgumentException("不支持的寄存器") };
    }
    public Bits Read(string name) => values.GetValueOrDefault(name) ?? new UnknownBits($"{Identity}:{name}", "寄存器未定义", Width(name));
    public RegisterState Set(string name, Bits value)
    {
        if (value.Width != Width(name)) throw new ArgumentException("寄存器位宽不一致");
        return new(Identity, values.SetItem(name, value));
    }
    public Bits ReadW(int number) => BitOps.Slice(Read($"X{number}"), 0, 32);
    public RegisterState WriteW(int number, Bits value)
    {
        if (value.Width != 32) throw new ArgumentException("W 寄存器写入需要 32 位");
        return Set($"X{number}", BitOps.Concat([value, BitOps.Constant(0, 32)]));
    }
    public RegisterState AfterCall(string call)
    {
        var result = new RegisterState(call, values);
        // 基础 AAPCS64：X18 为平台寄存器，未知平台策略下保守失效。
        foreach (var n in Enumerable.Range(0, 19).Append(30))
            result = result.Set($"X{n}", new UnknownBits($"{call}:X{n}", "调用破坏", 64));
        for (var n = 0; n < 32; n++)
        {
            Bits value = new UnknownBits($"{call}:V{n}", "调用破坏", 128);
            if (n is >= 8 and <= 15)
                value = BitOps.Concat([BitOps.Slice(Read($"V{n}"), 0, 64), new UnknownBits($"{call}:V{n}:hi", "调用破坏", 64)]);
            result = result.Set($"V{n}", value);
        }
        return result;
    }
}

public sealed record CallEffects(bool MayWriteMemory, bool MayThrow, bool NoReturn)
{
    public static CallEffects Unknown => new(true, true, false);
}
public sealed record CallSite(string Id, NativeAddress Address, Bits Target, Sequence<MethodBinding> Candidates,
    RegisterState Before, MemoryState MemoryBefore, StorageAddress StackPointer);
public sealed record BoundArgument(AbiValue Abi, Bits Value, bool IsAddress);
public sealed record CallOutcome(Sequence<BoundArgument> Arguments, Bits? ReturnValue,
    RegisterState? NormalRegisters, MemoryState? NormalMemory, MemoryState? ExceptionalMemory,
    string? Unresolved, CallSite Source)
{
    public RegisterState? ExceptionalRegisters { get; init; }
}

public static class CallTransfer
{
    public static CallOutcome Apply(CallSite call, CallLayout? layout, CallEffects effects)
    {
        var registers = call.Before.AfterCall(call.Id);
        var memory = effects.MayWriteMemory ? call.MemoryBefore.Invalidate($"{call.Id}:memory") : call.MemoryBefore;
        var arguments = new List<BoundArgument>();
        Bits? result = null;
        if (layout is not null)
        {
            foreach (var argument in layout.Arguments)
                arguments.Add(new(argument, BitOps.Concat(argument.Pieces.Select(p => ReadPiece(call, p))), argument.Indirect));
            if (!effects.NoReturn && layout.Return.Shape.Kind != ShapeKind.Void)
            {
                result = new InputBits($"{call.Id}:return", checked(layout.Return.Shape.Size * 8));
                if (!layout.Return.Indirect)
                {
                    foreach (var piece in layout.Return.Pieces)
                    {
                        var location = (RegisterLocation)piece.Location;
                        var value = BitOps.Slice(result, piece.ValueOffset * 8, piece.Size * 8);
                        var width = RegisterState.Width(location.Name);
                        if (value.Width < width)
                            value = BitOps.Concat([value, new UnknownBits($"{call.Id}:{location.Name}:unused", "返回值以外的寄存器位", width - value.Width)]);
                        registers = registers.Set(location.Name, value);
                    }
                }
                else
                {
                    // 返回缓冲指针保留于调用前状态；没有指针到区域的证明时不猜写入位置。
                    memory = memory.Invalidate($"{call.Id}:indirect-return");
                }
            }
        }
        return new(new(arguments), result, effects.NoReturn ? null : registers, effects.NoReturn ? null : memory,
            effects.MayThrow ? call.MemoryBefore.Invalidate($"{call.Id}:unwind") : null,
            layout is null ? "调用签名未确定，原始状态保留于 Source" : layout.Return.Indirect ? "返回缓冲尚未绑定存储区域" : null, call)
        {
            ExceptionalRegisters = effects.MayThrow ? call.Before.AfterCall($"{call.Id}:unwind")
                .Set("X0", new InputBits($"{call.Id}:exception-object", 64))
                .Set("X1", new InputBits($"{call.Id}:exception-selector", 64)) : null
        };
    }
    private static Bits ReadPiece(CallSite call, AbiPiece piece) => piece.Location switch
    {
        RegisterLocation r => BitOps.Slice(call.Before.Read(r.Name), r.BitOffset, piece.Size * 8),
        StackLocation s => call.MemoryBefore.Load(call.StackPointer with { Offset = checked(call.StackPointer.Offset + s.Offset) }, piece.Size),
        _ => throw new InvalidOperationException("未知 ABI 位置")
    };
}
