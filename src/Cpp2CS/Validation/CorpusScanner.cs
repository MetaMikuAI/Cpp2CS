using System.Diagnostics;
using System.Globalization;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Iced.Intel;
using Decoder = Iced.Intel.Decoder;

namespace Cpp2CS.Validation;

public sealed record CorpusScanResult(string ReportPath, string IssueIndexPath, long Candidates, long Validated, long Unsupported, long Invalid, long ValidationErrors, ulong UnrepresentedBytes, long NormalPathOnlyCount, long ExceptionBoundaryOnlyCount)
{
    public bool StructuralChecksPassed => ValidationErrors == 0;
    public bool AllCandidatesRepresented => Unsupported == 0 && Invalid == 0 && ValidationErrors == 0 && UnrepresentedBytes == 0;
    public bool FullyLifted => AllCandidatesRepresented && NormalPathOnlyCount == 0 && ExceptionBoundaryOnlyCount == 0;
}

public static class CorpusScanner
{
    public static CorpusScanResult Run(ImageDocument image, string outputDirectory)
    {
        if (image.ExecutableRanges.Count == 0) throw new InvalidDataException("映像没有可执行映射，不能报告提升完成");
        Directory.CreateDirectory(outputDirectory);
        var stem = $"{image.Architecture.ToString().ToLowerInvariant()}-{image.Sha256[..12].ToLowerInvariant()}";
        var indexPath = Path.GetFullPath(Path.Combine(outputDirectory, stem + ".issues.tsv.gz"));
        var boundaryPath = Path.GetFullPath(Path.Combine(outputDirectory, stem + ".boundaries.tsv.gz"));
        var reportPath = Path.GetFullPath(Path.Combine(outputDirectory, stem + ".report.json"));
        var contractPath = Path.GetFullPath(Path.Combine(outputDirectory, stem + ".contracts.tsv.gz"));
        var timer = Stopwatch.StartNew();
        var assemblyPath = typeof(ImageDocument).Assembly.Location;
        using var assemblyStream = File.OpenRead(assemblyPath);
        var assemblySha256 = Convert.ToHexString(SHA256.HashData(assemblyStream));
        var counts = new ScanCounts();
        using (var file = File.Create(indexPath))
        using (var gzip = new GZipStream(file, CompressionLevel.Fastest))
        using (var writer = new StreamWriter(gzip, new UTF8Encoding(false), 65536))
        using (var boundariesFile = File.Create(boundaryPath))
        using (var boundariesGzip = new GZipStream(boundariesFile, CompressionLevel.Fastest))
        using (var boundaries = new StreamWriter(boundariesGzip, new UTF8Encoding(false), 65536))
        using (var contractFile = File.Create(contractPath))
        using (var contractGzip = new GZipStream(contractFile, CompressionLevel.Fastest))
        using (var contracts = new StreamWriter(contractGzip, new UTF8Encoding(false), 65536))
        {
            writer.WriteLine("address\tfileOffset\tlength\tstatus\tform\tbytes\treason");
            boundaries.WriteLine("address\tfileOffset\tlength\tstatus");
            contracts.WriteLine("address\tfileOffset\tlength\tsupport\tobligations");
            counts.Boundaries = boundaries;
            counts.Contracts = contracts;
            foreach (var range in image.ExecutableRanges)
            {
                counts.ExecutableFileBytes += range.FileSize;
                counts.ExecutableMemoryBytes += range.MemorySize;
                if (image.Architecture == Architecture.Arm64) ScanArm64(image, range, writer, counts);
                else ScanX64(image, range, writer, counts);
                if (range.MemorySize > range.FileSize)
                {
                    var length = range.MemorySize - range.FileSize;
                    counts.ZeroFillBytes += length;
                    WriteIssue(writer, checked(range.Address + range.FileSize), null, length, "NotFileBacked", "range", "", "Executable zero-fill is not decoded from synthetic bytes");
                }
            }
        }
        timer.Stop();
        if (counts.BytesCovered != counts.ExecutableFileBytes) throw new InvalidDataException("扫描没有覆盖全部可执行文件字节");
        var result = new CorpusScanResult(reportPath, indexPath, counts.Candidates, counts.Validated, counts.Unsupported,
            counts.Invalid, counts.ValidationErrors, counts.BoundaryBytes + counts.ZeroFillBytes,
            counts.SupportClasses.GetValueOrDefault(nameof(SupportClass.NormalPathOnly)),
            counts.SupportClasses.GetValueOrDefault(nameof(SupportClass.ExceptionBoundaryOnly)));
        var report = new
        {
            schemaVersion = 2,
            mirSchemaVersion = MirJson.SchemaVersion,
            semanticsVersion = MirJson.SemanticsVersion,
            implementationAssembly = assemblyPath,
            implementationAssemblySha256 = assemblySha256,
            profile = MachineProfile.For(image.Architecture),
            inputSha256 = image.Sha256,
            architecture = image.Architecture.ToString(),
            preferredBase = $"0x{image.PreferredBase:X}",
            scanKind = image.Architecture == Architecture.Arm64 ? "Every aligned 4-byte word in executable file mappings" : "Iced 64-bit linear sweep of executable file mappings; invalid input continues at consumed byte boundary",
            scope = "Candidate bytes only: not reachable CFG, all legal x86 entry points, complete instruction semantics, native equivalence, or game runtime validation. Unsupported and invalid candidates remain in the index.",
            validation = "Every supported MIR candidate passed through MirValidator; structural checking is not semantic equivalence.",
            passedStructuralValidation = result.StructuralChecksPassed,
            allCandidatesRepresented = result.AllCandidatesRepresented,
            fullyLifted = result.FullyLifted,
            normalPathOnlyCount = result.NormalPathOnlyCount,
            exceptionBoundaryOnlyCount = result.ExceptionBoundaryOnlyCount,
            executableFileBytes = counts.ExecutableFileBytes,
            executableMemoryBytes = counts.ExecutableMemoryBytes,
            bytesCovered = counts.BytesCovered,
            bytesLifted = counts.BytesLifted,
            zeroFillBytes = counts.ZeroFillBytes,
            candidates = counts.Candidates,
            decodedX64 = counts.DecodedX64,
            validated = counts.Validated,
            unsupported = counts.Unsupported,
            invalid = counts.Invalid,
            truncatedOrUnalignedBytes = counts.BoundaryBytes,
            validationErrors = counts.ValidationErrors,
            mirOperations = counts.Operations,
            forms = Sorted(counts.Forms),
            supportClasses = Sorted(counts.SupportClasses),
            unsupportedReasons = Sorted(counts.UnsupportedReasons),
            limitations = Sorted(counts.Limitations),
            obligations = Sorted(counts.Obligations),
            elapsedSeconds = timer.Elapsed.TotalSeconds,
            executableRanges = image.ExecutableRanges.Select(r => new { r.Name, address = $"0x{r.Address:X}", fileOffset = $"0x{r.FileOffset:X}", r.FileSize, r.MemorySize }),
            relocationTables = image.RelocationTables,
            codeRelocations = image.CodeRelocations,
            issueIndex = indexPath,
            issueIndexSha256 = FileHash(indexPath),
            boundaryIndex = boundaryPath,
            boundaryIndexSha256 = FileHash(boundaryPath),
            contractIndex = contractPath,
            contractIndexSha256 = FileHash(contractPath)
        };
        File.WriteAllText(reportPath, JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }), new UTF8Encoding(false));
        return result;
    }

    private static void ScanArm64(ImageDocument image, ImageRange range, StreamWriter writer, ScanCounts counts)
    {
        ulong offset = 0;
        if ((range.Address & 3) != 0)
        {
            var prefix = Math.Min(4 - (range.Address & 3), range.FileSize);
            Boundary(image, range, 0, prefix, "UnalignedStart", writer, counts);
            offset += prefix;
        }
        for (; range.FileSize - offset >= 4; offset += 4)
        {
            var origin = Origin(image, range, offset, 4);
            counts.Candidates++;
            counts.BytesCovered += 4;
            if (image.HasCodeRelocation(origin.Address, 4))
                Unsupported(origin, "code.relocation", "CodeRelocationRequired", writer, counts);
            else Process(Cpp2CS.Arm64.Arm64Lifter.Lift(origin), origin, writer, counts);
            Progress(image, counts);
        }
        if (offset != range.FileSize) Boundary(image, range, offset, range.FileSize - offset, "TruncatedWord", writer, counts);
    }

    private static void ScanX64(ImageDocument image, ImageRange range, StreamWriter writer, ScanCounts counts)
    {
        var reader = new ImageCodeReader(image.Bytes, checked((int)range.FileOffset), checked((int)range.FileSize));
        var decoder = Decoder.Create(64, reader);
        decoder.IP = range.Address;
        ulong offset = 0;
        while (offset < range.FileSize)
        {
            decoder.Decode(out var instruction);
            var length = instruction.Length;
            if (length <= 0 || (ulong)length > range.FileSize - offset) throw new InvalidDataException("Iced 消费长度不合法");
            var origin = Origin(image, range, offset, length);
            if (instruction.IP != origin.Address) throw new InvalidDataException("Iced 地址与文件扫描位置不一致");
            counts.Candidates++;
            counts.BytesCovered += (ulong)length;
            if (instruction.IsInvalid)
            {
                counts.Invalid++;
                Increment(counts.Forms, "invalid.encoding");
                WriteBoundary(counts, origin, 'I');
                WriteIssue(writer, origin, "InvalidEncoding", "Iced.INVALID", "Iced rejected this linear-sweep candidate; this is not proof of invalid reachable code");
            }
            else
            {
                counts.DecodedX64++;
                if (image.HasCodeRelocation(origin.Address, length)) Unsupported(origin, instruction.Code.ToString(), "CodeRelocationRequired", writer, counts);
                else Process(Cpp2CS.X64.X64Lifter.Lift(origin, in instruction), origin, writer, counts);
            }
            offset += (ulong)length;
            Progress(image, counts);
        }
    }

    private static InstructionOrigin Origin(ImageDocument image, ImageRange range, ulong offset, int length) =>
        new(image.Sha256, checked(range.Address + offset), checked(range.FileOffset + (long)offset), image.Bytes.Slice(checked((int)(range.FileOffset + (long)offset)), length));

    private static void Process(LiftResult result, InstructionOrigin origin, StreamWriter writer, ScanCounts counts)
    {
        if (result.Ir is not { } ir)
        {
            Unsupported(origin, result.Form, result.Reason ?? "Missing semantic rule", writer, counts);
            return;
        }
        Increment(counts.Forms, result.Form);
        var errors = MirValidator.Validate(ir);
        if (errors.Count != 0)
        {
            counts.ValidationErrors++;
            WriteBoundary(counts, origin, 'E');
            WriteIssue(writer, origin, "InvalidMIR", result.Form, string.Join(" | ", errors));
            return;
        }
        counts.Validated++;
        counts.Operations += ir.Operations.Length;
        Increment(counts.SupportClasses, ir.Support.ToString());
        var obligations = ir.Obligations;
        foreach (var reason in obligations.Select(item => item.Reason).Distinct()) Increment(counts.Limitations, reason);
        var codes = obligations.Select(item => item.Kind.ToString()).Distinct().Order(StringComparer.Ordinal).ToArray();
        foreach (var code in codes) Increment(counts.Obligations, code);
        counts.Contracts.Write(origin.Address.ToString("X", CultureInfo.InvariantCulture)); counts.Contracts.Write('\t');
        counts.Contracts.Write(origin.FileOffset.ToString("X", CultureInfo.InvariantCulture)); counts.Contracts.Write('\t');
        counts.Contracts.Write(origin.Bytes.Length.ToString(CultureInfo.InvariantCulture)); counts.Contracts.Write('\t');
        counts.Contracts.Write(ir.Support.ToString()); counts.Contracts.Write('\t');
        counts.Contracts.WriteLine(codes.Length == 0 ? "-" : string.Join(',', codes));
        WriteBoundary(counts, origin, 'V');
        counts.BytesLifted += (ulong)origin.Bytes.Length;
    }

    private static void Unsupported(InstructionOrigin origin, string form, string reason, StreamWriter writer, ScanCounts counts)
    {
        counts.Unsupported++;
        WriteBoundary(counts, origin, 'U');
        // 未识别 ARM word 的原值在索引中保留，汇总不为每个立即数建立一个表项。
        Increment(counts.Forms, form.StartsWith("word.", StringComparison.Ordinal) ? "unimplemented.word" : form);
        Increment(counts.UnsupportedReasons, reason);
        WriteIssue(writer, origin, "UnsupportedSemantics", form, reason);
    }

    private static void Boundary(ImageDocument image, ImageRange range, ulong offset, ulong length, string reason, StreamWriter writer, ScanCounts counts)
    {
        counts.BoundaryBytes += length;
        counts.BytesCovered += length;
        var origin = Origin(image, range, offset, checked((int)length));
        WriteIssue(writer, origin, "MappingBoundary", "bytes", reason);
    }

    private static void WriteIssue(StreamWriter writer, InstructionOrigin origin, string status, string form, string reason) =>
        WriteIssue(writer, origin.Address, origin.FileOffset, (ulong)origin.Bytes.Length, status, form, Convert.ToHexString(origin.Bytes.Span), reason);

    private static void WriteIssue(StreamWriter writer, ulong address, long? fileOffset, ulong length, string status, string form, string bytes, string reason)
    {
        writer.Write(address.ToString("X", CultureInfo.InvariantCulture)); writer.Write('\t');
        writer.Write(fileOffset?.ToString("X", CultureInfo.InvariantCulture) ?? "-"); writer.Write('\t');
        writer.Write(length.ToString(CultureInfo.InvariantCulture)); writer.Write('\t');
        writer.Write(Clean(status)); writer.Write('\t'); writer.Write(Clean(form)); writer.Write('\t');
        writer.Write(bytes); writer.Write('\t'); writer.WriteLine(Clean(reason));
    }

    private static string Clean(string text) => text.Replace('\t', ' ').Replace('\r', ' ').Replace('\n', ' ');
    private static string FileHash(string path)
    {
        using var stream = File.OpenRead(path);
        return Convert.ToHexString(SHA256.HashData(stream));
    }
    private static void WriteBoundary(ScanCounts counts, InstructionOrigin origin, char status)
    {
        var writer = counts.Boundaries;
        writer.Write(origin.Address.ToString("X", CultureInfo.InvariantCulture)); writer.Write('\t');
        writer.Write(origin.FileOffset.ToString("X", CultureInfo.InvariantCulture)); writer.Write('\t');
        writer.Write(origin.Bytes.Length.ToString(CultureInfo.InvariantCulture)); writer.Write('\t'); writer.WriteLine(status);
    }
    private static void Increment(Dictionary<string, long> counts, string name) => counts[name] = counts.GetValueOrDefault(name) + 1;
    private static SortedDictionary<string, long> Sorted(Dictionary<string, long> counts) => new(counts, StringComparer.Ordinal);
    private static void Progress(ImageDocument image, ScanCounts counts)
    {
        if (counts.Candidates % 1_000_000 == 0)
            Console.Error.WriteLine($"{image.Architecture}: {counts.Candidates:N0} candidates, {counts.Validated:N0} structurally validated, {counts.Unsupported:N0} unsupported, {counts.Invalid:N0} invalid, {counts.ValidationErrors:N0} invalid MIR");
    }

    private sealed class ImageCodeReader(ReadOnlyMemory<byte> bytes, int offset, int length) : CodeReader
    {
        private int position = offset;
        private readonly int end = checked(offset + length);
        public override int ReadByte() => position < end ? bytes.Span[position++] : -1;
    }

    private sealed class ScanCounts
    {
        public StreamWriter Boundaries = StreamWriter.Null;
        public StreamWriter Contracts = StreamWriter.Null;
        public ulong ExecutableFileBytes, ExecutableMemoryBytes, BytesCovered, BytesLifted, ZeroFillBytes, BoundaryBytes;
        public long Candidates, DecodedX64, Validated, Unsupported, Invalid, ValidationErrors, Operations;
        public readonly Dictionary<string, long> Forms = new(StringComparer.Ordinal);
        public readonly Dictionary<string, long> SupportClasses = new(StringComparer.Ordinal);
        public readonly Dictionary<string, long> UnsupportedReasons = new(StringComparer.Ordinal);
        public readonly Dictionary<string, long> Limitations = new(StringComparer.Ordinal);
        public readonly Dictionary<string, long> Obligations = new(StringComparer.Ordinal);
    }
}
