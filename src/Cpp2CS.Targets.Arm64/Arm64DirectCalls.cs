using System.Collections.Concurrent;
using System.Runtime.CompilerServices;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Targets.Arm64;

public static class Arm64DirectCalls
{
    private static readonly ConditionalWeakTable<IImage, Targets> targets = [];
    public static CallTargetResolution ResolveTarget(IImage image, CallTarget target) => target is ImageFunction function
        ? targets.GetValue(image, source => new(source)).Resolve(function.EntryOffset) : new(target, null);

    /// <summary>线性扫描范围内的 BL 和向范围外的 B；不依赖可提升性或不返回分析的路径截断。</summary>
    public static IEnumerable<(ulong Address, ulong Target)> ToCandidates(IImage image, FunctionRange range, IReadOnlySet<ulong> candidates)
    {
        for (ulong offset = 0; offset + 4 <= range.Length; offset += 4)
        {
            var address = checked(range.Start + offset);
            if (!image.IsExecutable(address, 4)) continue;
            uint word = (uint)image.ReadUnsigned(address, 4);
            if ((word & 0x7c000000) != 0x14000000) continue;
            long displacement = ((long)(word & 0x03ffffff) << 38) >> 36;
            ulong target = unchecked(address + (ulong)displacement);
            bool linked = (word & 0x80000000) != 0;
            if ((linked || target < range.Start || target - range.Start >= range.Length)
                && ResolveTarget(image, new ImageFunction(target)).Target is ImageFunction normalized && candidates.Contains(normalized.EntryOffset))
                yield return (address, normalized.EntryOffset);
        }
    }

    private sealed class Targets
    {
        private readonly IImage image;
        private readonly FunctionRange[] ranges;
        private readonly ulong[] coveredEnds;
        private readonly ConcurrentDictionary<ulong, CallTargetResolution> cache = [];
        internal Targets(IImage image)
        {
            this.image = image;
            ranges = image.Functions.OrderBy(r => r.Start).ToArray();
            coveredEnds = new ulong[ranges.Length];
            for (int i = 0; i < ranges.Length; i++)
            {
                var range = ranges[i];
                ulong end = range.Start > ulong.MaxValue - range.Length ? ulong.MaxValue : range.Start + range.Length;
                coveredEnds[i] = Math.Max(i == 0 ? 0 : coveredEnds[i - 1], end);
            }
        }
        internal CallTargetResolution Resolve(ulong entry) => cache.GetOrAdd(entry, Normalize);
        private CallTargetResolution Normalize(ulong entry)
        {
            var seen = new HashSet<ulong>();
            for (int depth = 0; depth < 32; depth++)
            {
                if (!seen.Add(entry)) return new(null, new("call-target.cycle", "调用跳板成环。"));
                if (Plt(entry) is { } plt)
                {
                    if (plt is not ImageFunction function) return new(plt, null);
                    entry = function.EntryOffset; continue;
                }
                if (!TryThunk(entry, out var destination)) return new(new ImageFunction(entry), null);
                entry = destination;
            }
            return new(null, new("call-target.budget", "调用跳板链超过解析上限。"));
        }
        private IEnumerable<FunctionRange> Containing(ulong entry)
        {
            int low = 0, high = ranges.Length;
            while (low < high)
            {
                int middle = low + (high - low) / 2;
                if (ranges[middle].Start <= entry) low = middle + 1; else high = middle;
            }
            // 前缀末端界同时覆盖重叠范围，避免逐目标扫描全部函数。
            for (int i = low - 1; i >= 0 && coveredEnds[i] > entry; i--)
            {
                var range = ranges[i];
                if (entry - range.Start < range.Length) yield return range;
            }
        }
        private bool TryThunk(ulong entry, out ulong destination)
        {
            destination = 0;
            // 只归一函数之间空隙里的跳板。有展开信息的函数即使只有一条跳转也是独立的函数：
            // 托管方法、运行时函数的身份登记在它自己的入口上，归一会把调用认到别的函数头上。
            if (Containing(entry).Any()) return false;
            if (Arm64LinkerFlow.DirectBranch(image, entry, out var direct))
            {
                destination = direct; return true;
            }
            var probe = new ConstantThunk(image);
            for (int length = 4; length <= 20; length += 4)
            {
                if (entry > ulong.MaxValue - (ulong)length || !image.IsExecutable(entry + (ulong)length - 4, 4)) return false;
                var decoded = Arm64InstructionSet.DecodeWord(entry + (ulong)length - 4, (uint)image.ReadUnsigned(entry + (ulong)length - 4, 4));
                decoded.Instruction!.Emit(probe);
                if (probe.Invalid) return false;
                if (probe.Destination is not { } target) continue;
                destination = target; return true;
            }
            return false;
        }
        // AArch64 ELF PLT：ADRP x16; LDR x17; ADD x16; BR x17。导入身份只来自重定位。
        private CallTarget? Plt(ulong pc)
        {
            if (!image.IsExecutable(pc, 16)) return null;
            uint a = (uint)image.ReadUnsigned(pc, 4), b = (uint)image.ReadUnsigned(pc + 4, 4),
                c = (uint)image.ReadUnsigned(pc + 8, 4), d = (uint)image.ReadUnsigned(pc + 12, 4);
            if ((a & 0x9f00001f) != 0x90000010 || (b & 0xffc003ff) != 0xf9400211
                || (c & 0xffc003ff) != 0x91000210 || d != 0xd61f0220) return null;
            long immediate = (long)(((a >> 5) & 0x7ffff) << 2 | ((a >> 29) & 3));
            immediate = (immediate << 43) >> 43;
            ulong offset = ((b >> 10) & 4095) * 8UL;
            if (offset != ((c >> 10) & 4095)) return null;
            ulong slot = unchecked((pc & ~4095UL) + (ulong)(immediate << 12) + offset);
            if (image.Query(slot).AvailableBytes < 8) return null;
            return image.ReadPointer(slot) switch
            {
                PointerTarget.Import { Addend: 0 } import => new ImportedTarget(import.Symbol),
                PointerTarget.Internal inner => new ImageFunction(inner.Offset),
                _ => null
            };
        }
    }

    /// <summary>只接受常量形成、只读指针字面量及经 x16/x17 的 BR；沿用解码语义，拒绝其余效果。</summary>
    private sealed class ConstantThunk(IImage image) : IEmitter
    {
        public TermTable Terms { get; } = new();
        private readonly Dictionary<Register, Term> values = [];
        internal bool Invalid { get; private set; }
        internal ulong? Destination { get; private set; }
        private static bool Scratch(Register register) => register == Arm64Registers.X[16] || register == Arm64Registers.X[17];
        private Term Reject(int width) { Invalid = true; return Terms.Undefined(width); }
        public Term Read(Register register) => Scratch(register) && values.TryGetValue(register, out var value) ? value : Reject(register.Width);
        public void Write(Register register, Term value)
        {
            if (!Scratch(register) || value.ConstantValue is null) Invalid = true;
            else values[register] = value;
        }
        public Term Load(Term address, int width)
        {
            if (width != 64 || address.ConstantValue is not { } constant || constant > ulong.MaxValue) return Reject(width);
            ulong slot = (ulong)constant;
            var info = image.Query(slot);
            return info is { Storage: StorageKind.FileContent, Writable: false, AvailableBytes: >= 8 }
                && image.ReadPointer(slot) is PointerTarget.Internal pointer ? Terms.Constant(pointer.Offset, 64) : Reject(width);
        }
        public void IndirectJump(Term target)
        {
            if (target.ConstantValue is { } constant && constant <= ulong.MaxValue && values.Values.Contains(target)) Destination = (ulong)constant;
            else Invalid = true;
        }
        public Term ImageAddress(ulong offset) => Terms.Constant(offset, 64);
        public Term ThreadPointer => Reject(64);
        public void Store(Term address, Term value) => Invalid = true;
        public void Call(CallTarget target) => Invalid = true;
        public void Jump(ulong target) => Invalid = true;
        public void Branch(Term condition, ulong whenTrue, ulong whenFalse) => Invalid = true;
        public void Return() => Invalid = true;
        public void Trap() => Invalid = true;
        public void TrapIf(Term condition) => Invalid = true;
        public void Fail(Reason reason) => Invalid = true;
    }
}
