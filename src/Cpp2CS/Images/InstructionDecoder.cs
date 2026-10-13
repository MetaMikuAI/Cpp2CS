using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.Images;

public enum InstructionDecodeFailure
{
    Unmapped, NotExecutable, NotFileBacked, Truncated, Unaligned,
    InvalidEncoding, Unsupported, CodeRelocation
}
public sealed record InstructionDecodeResult(MirInstruction? Instruction,
    InstructionDecodeFailure? Failure, string? Reason)
{
    public static InstructionDecodeResult Supported(MirInstruction instruction) => new(instruction, null, null);
    public static InstructionDecodeResult Stopped(InstructionDecodeFailure failure, string reason) => new(null, failure, reason);
}

// 从指定入口独立解码；不沿用线性扫描确定的 x64 指令边界。
public sealed class InstructionDecoder(ImageDocument image)
{
    public InstructionDecodeResult Decode(ulong address)
    {
        var mapping = image.Resolve(address);
        if (mapping.Kind == AddressKind.Unmapped)
            return InstructionDecodeResult.Stopped(InstructionDecodeFailure.Unmapped, "目标未映射");
        if (!mapping.Range!.Executable)
            return InstructionDecodeResult.Stopped(InstructionDecodeFailure.NotExecutable, "目标映射不可执行");
        if (mapping.Kind != AddressKind.FileBacked)
            return InstructionDecodeResult.Stopped(InstructionDecodeFailure.NotFileBacked, "目标没有文件字节");
        var size = checked((int)Math.Min(mapping.AvailableBytes, image.Architecture == Architecture.Arm64 ? 4UL : 15UL));
        var offset = mapping.FileOffset!.Value;
        return DecodeBytes(image.Architecture, image.Sha256, address, offset,
            image.Bytes.Slice(checked((int)offset), size), image.HasCodeRelocation);
    }

    public static InstructionDecodeResult DecodeBytes(Architecture architecture, string imageId,
        ulong address, long fileOffset, ReadOnlyMemory<byte> bytes, Func<ulong, int, bool>? hasCodeRelocation = null)
    {
        if (!Enum.IsDefined(architecture)) throw new ArgumentOutOfRangeException(nameof(architecture));
        if (architecture == Architecture.Arm64 && (address & 3) != 0)
            return InstructionDecodeResult.Stopped(InstructionDecodeFailure.Unaligned, "ARM64 入口未按四字节对齐");
        if (bytes.Length == 0 || architecture == Architecture.Arm64 && bytes.Length < 4)
            return InstructionDecodeResult.Stopped(InstructionDecodeFailure.Truncated, "指令文件字节不完整");
        LiftResult lifted;
        if (architecture == Architecture.Arm64)
        {
            if (hasCodeRelocation?.Invoke(address, 4) == true)
                return InstructionDecodeResult.Stopped(InstructionDecodeFailure.CodeRelocation, "指令覆盖尚未应用的代码重定位");
            lifted = Arm64.Arm64Lifter.Lift(new(imageId, address, fileOffset, bytes[..4]));
        }
        else
        {
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes[..Math.Min(bytes.Length, 15)].ToArray()));
            decoder.IP = address;
            decoder.Decode(out var instruction);
            // NoMoreBytes 仅说明解码耗尽输入，不证明该字节前缀原本合法。
            if (instruction.IsInvalid)
                return InstructionDecodeResult.Stopped(decoder.LastError == DecoderError.NoMoreBytes ?
                    InstructionDecodeFailure.Truncated : InstructionDecodeFailure.InvalidEncoding,
                    decoder.LastError == DecoderError.NoMoreBytes ? "x64 解码耗尽文件字节，编码合法性未判定" : "x64 解码器拒绝此入口编码");
            if (instruction.Length <= 0 || instruction.Length > bytes.Length || instruction.IP != address)
                throw new InvalidDataException("x64 解码来源范围不一致");
            if (hasCodeRelocation?.Invoke(address, instruction.Length) == true)
                return InstructionDecodeResult.Stopped(InstructionDecodeFailure.CodeRelocation, "指令覆盖尚未应用的代码重定位");
            lifted = X64.X64Lifter.Lift(new(imageId, address, fileOffset, bytes[..instruction.Length]), in instruction);
        }
        // ARM64 当前没有独立的完整合法性分类器；拒绝提升保留 Unsupported。
        if (lifted.Ir is not { } ir)
            return InstructionDecodeResult.Stopped(InstructionDecodeFailure.Unsupported, lifted.Reason ?? "尚无 MIR 规则");
        var errors = MirValidator.Validate(ir);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        return InstructionDecodeResult.Supported(ir);
    }
}
