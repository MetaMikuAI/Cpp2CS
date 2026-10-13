namespace Cpp2CS.Native;

public sealed record DecodedMethod(ulong Address, Instruction[] Instructions, UnwindBoundary Boundary);

// 解码结果按入口复用；值、类型绑定和源码投影属于每次方法分析。
public sealed class Arm64MethodReader(ElfImage image, Arm64Decoder decoder, Symbols symbols)
{
    private readonly Dictionary<ulong, DecodedMethod> methods = [];
    public DecodedMethod Read(ulong address)
    {
        if (methods.TryGetValue(address, out var found)) return found;
        var boundary = UnwindBoundary.Read(image, address);
        var end = boundary.Start == address && boundary.End > address ? boundary.End : symbols.Ceiling(address);
        if (end <= address || end - address > 16384) throw new InvalidDataException("候选函数范围超出当前限制");
        return methods[address] = new(address, decoder.Decode(image.Read(address, (int)(end - address)), address), boundary);
    }
}

public sealed record MethodAnalysis(NativeMethod Method, DecodedMethod Machine, NativeControlFlow Flow,
    NativeSsaProgram Ssa, SsaSemantics Semantics, Symbols Symbols, VirtualCall[] VirtualCalls,
    InterfaceCall[] Interfaces, string[] DispatchProblems);
