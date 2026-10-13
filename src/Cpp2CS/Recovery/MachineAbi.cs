using System.Collections.Immutable;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

// AAPCS64 §6.1/§6.8/§6.9；Microsoft x64 calling convention 的普通调用接口与保存规则。
public static class MachineAbi
{
    public const string Version = "aggregate-abi/4";

    public static Architecture ArchitectureFor(MachineAbiKind abi) => abi switch
    {
        MachineAbiKind.Aapcs64 => Architecture.Arm64,
        MachineAbiKind.WindowsX64 => Architecture.X64,
        _ => throw new ArgumentOutOfRangeException(nameof(abi))
    };

    public static bool TryDescribe(FunctionContract contract, out MachineInterface? result, out string? reason)
    {
        result = null;
        reason = null;
        if (string.IsNullOrWhiteSpace(contract.Name) || !Enum.IsDefined(contract.Abi) ||
            contract.Signature is null || contract.Signature.Arguments.IsDefault || contract.Effects is null ||
            contract.Assumptions.IsDefault || contract.Assumptions.Any(string.IsNullOrWhiteSpace))
        {
            reason = "函数合同缺少名称、已知逻辑签名、ABI 或明确的前提记录";
            return false;
        }
        foreach (var type in contract.Signature.Arguments)
            if (!Supported(type, contract.Abi, out reason)) return false;
        if (contract.Signature.Result is { } returnType && !Supported(returnType, contract.Abi, out reason)) return false;
        if (!contract.Effects.MayReturn && !contract.Effects.MayThrow &&
            !contract.Effects.MayDiverge && !contract.Effects.MayTerminate)
        {
            reason = "调用合同没有允许的返回、异常、发散或终止行为";
            return false;
        }
        var arm = contract.Abi == MachineAbiKind.Aapcs64;
        string[] windowsRegisters = ["rcx", "rdx", "r8", "r9"];
        var arguments = ImmutableArray.CreateBuilder<MachineArgumentLocation>();
        var general = 0;
        var floating = 0;
        long stack = arm ? 0 : 40;
        for (var index = 0; index < contract.Signature.Arguments.Length; index++)
        {
            var type = contract.Signature.Arguments[index];
            var isFloat = type.Kind == RecoveryScalarKind.Float;
            var hfa = arm ? HomogeneousFields(type) : [];
            if (arm && !hfa.IsEmpty)
            {
                if (floating + hfa.Length <= 8)
                    arguments.Add(new CompositeArgumentLocation(type.Width, hfa.Select(field =>
                        new MachineValuePart(field.ByteOffset * 8, new SlotArgumentLocation($"v{floating++}", 0, field.Type.Width))).ToImmutableArray()));
                else
                {
                    floating = 8;
                    arguments.Add(Stack(type, type.Aggregate!.AlignmentBytes));
                }
            }
            else if (arm && type.Kind == RecoveryScalarKind.Aggregate)
            {
                var count = (type.Width + 63) / 64;
                if (general + count <= 8)
                    arguments.Add(new CompositeArgumentLocation(type.Width, Enumerable.Range(0, count).Select(part =>
                        new MachineValuePart(part * 64, new SlotArgumentLocation($"x{general++}", 0, Math.Min(64, type.Width - part * 64)))).ToImmutableArray()));
                else
                {
                    general = 8;
                    arguments.Add(Stack(type, type.Aggregate!.AlignmentBytes));
                }
            }
            else if (arm && (isFloat ? floating : general) < 8)
                arguments.Add(new SlotArgumentLocation(isFloat ? $"v{floating++}" : $"x{general++}", 0, type.Width));
            else if (!arm && index < 4)
                arguments.Add(new SlotArgumentLocation(isFloat ? $"xmm{index}" : windowsRegisters[index], 0, type.Width));
            else
            {
                arguments.Add(Stack(type, 8));
            }
        }
        result = new(arguments.ToImmutable(),
            contract.Signature.Result is { } returned ? Result(returned, arm) : null,
            arm ? "sp" : "rsp", 16, arm ? 0 : 8);
        return true;

        StackArgumentLocation Stack(RecoveryScalarType type, int alignment)
        {
            var align = Math.Max(8, alignment);
            stack = (stack + align - 1) / align * align;
            var location = new StackArgumentLocation(stack, type.Width);
            stack += (type.Width + 63) / 64 * 8;
            return location;
        }
    }

    public static MachineInterface Describe(FunctionContract contract) =>
        TryDescribe(contract, out var result, out var reason) ? result! : throw new ArgumentException(reason, nameof(contract));

    public static MachineCallSummary CreateSummary(FunctionContract contract)
    {
        var mapping = Describe(contract);
        var layout = StateLayout.For(ArchitectureFor(contract.Abi));
        var reads = layout.OrderBy(pair => pair.Key, StringComparer.Ordinal)
            .Select(pair => new MachineSlotRead(pair.Key, 0, pair.Value)).ToImmutableArray();
        var world = new MachineWorldRelation(true, contract.Effects.WritesMemory, contract.Effects.ExternalEffects, true);
        var normal = contract.Effects.MayReturn
            ? layout.OrderBy(pair => pair.Key, StringComparer.Ordinal).Select(pair => Relation(pair.Key, pair.Value)).ToImmutableArray()
            : [];
        var outcomes = ImmutableArray.CreateBuilder<MachineCallOutcome>();
        if (contract.Effects.MayThrow)
            outcomes.Add(new(MachineCallOutcomeKind.Unwind, HavocAll(layout), world));
        if (contract.Effects.MayTerminate)
            outcomes.Add(new(MachineCallOutcomeKind.Terminate, [], world));
        if (contract.Effects.MayDiverge)
            outcomes.Add(new(MachineCallOutcomeKind.Diverge, [], world));
        var prerequisites = contract.Assumptions.Add("adopted ordinary scalar or fixed-layout plain-data aggregate ABI; no variadic, nontrivial C++ object, indirect aggregate, non-local-return or floating-environment-setter interface")
            .Add("summary input is callee entry after machine call preparation; normal output is after the return protocol")
            .Add("ABI stack alignment and readable argument/return storage hold on the represented normal path");
        if (contract.Domain?.StableThreadEnvironment == true)
            prerequisites = prerequisites.Add("thread context, segment configuration and authentication/entry-check configuration remain stable across the call");
        return new(contract, mapping, reads, normal, world, prerequisites, outcomes.ToImmutable());

        MachineSlotRelation Relation(string slot, int width)
        {
            if (slot == mapping.StackPointer)
                return new(slot, width, [new(0, width, SlotRelationKind.AddConstant, slot, 0, mapping.NormalReturnSpAdjustment)]);
            var returned = mapping.Result is null ? [] : Pieces(mapping.Result)
                .Where(part => part.Location is SlotArgumentLocation location && location.Slot == slot).ToArray();
            if (returned.Length != 0)
            {
                var segments = ImmutableArray.CreateBuilder<MachineSlotSegment>();
                var position = 0;
                foreach (var part in returned.OrderBy(part => ((SlotArgumentLocation)part.Location).Offset))
                {
                    var location = (SlotArgumentLocation)part.Location;
                    if (position < location.Offset) segments.Add(new(position, location.Offset - position, SlotRelationKind.Havoc));
                    segments.Add(new(location.Offset, location.Width, SlotRelationKind.Result, ResultOffset: part.ValueBitOffset));
                    position = location.Offset + location.Width;
                }
                if (position < width) segments.Add(new(position, width - position, SlotRelationKind.Havoc));
                return new(slot, width, segments.ToImmutable());
            }
            if (contract.Abi == MachineAbiKind.Aapcs64)
            {
                if (Numbered(slot, "x", 19, 29)) return Preserved(slot, width);
                if (Numbered(slot, "v", 8, 15))
                    return new(slot, width, [new(0, 64, SlotRelationKind.Preserve, slot), new(64, 64, SlotRelationKind.Havoc)]);
            }
            else
            {
                if (slot is "rbx" or "rbp" or "rdi" or "rsi" or "r12" or "r13" or "r14" or "r15" ||
                    Numbered(slot, "xmm", 6, 15)) return Preserved(slot, width);
                if (slot == "mxcsr") return new(slot, width,
                    [new(0, 6, SlotRelationKind.Havoc), new(6, 10, SlotRelationKind.Preserve, slot, 6), new(16, 16, SlotRelationKind.Havoc)]);
                if (slot == "df") return new(slot, width, [new(0, 1, SlotRelationKind.Constant, Constant: 0)]);
            }
            if (contract.Domain?.StableThreadEnvironment == true && IsThreadEnvironment(slot)) return Preserved(slot, width);
            return new(slot, width, [new(0, width, SlotRelationKind.Havoc)]);
        }
    }

    public static IEnumerable<MachineValuePart> Pieces(MachineArgumentLocation location) =>
        location is CompositeArgumentLocation composite ? composite.Parts : [new(0, location)];

    public static bool TypeEquals(RecoveryScalarType? left, RecoveryScalarType? right) => Same(left, right, 0);

    private static bool Same(RecoveryScalarType? left, RecoveryScalarType? right, int depth)
    {
        if (depth > 32) return false;
        if (left is null || right is null) return left is null && right is null;
        if (left.Width != right.Width || left.Kind != right.Kind) return false;
        if (left.Aggregate is not { } a || right.Aggregate is not { } b) return left.Aggregate == right.Aggregate;
        return a.AlignmentBytes == b.AlignmentBytes && !a.Fields.IsDefault && !b.Fields.IsDefault &&
            a.Fields.All(field => field is not null) && b.Fields.All(field => field is not null) &&
            a.Fields.Length == b.Fields.Length && a.Fields.OrderBy(field => field.ByteOffset)
                .Zip(b.Fields.OrderBy(field => field.ByteOffset)).All(pair => pair.First.ByteOffset == pair.Second.ByteOffset &&
                    Same(pair.First.Type, pair.Second.Type, depth + 1));
    }

    private static MachineArgumentLocation Result(RecoveryScalarType type, bool arm)
    {
        if (arm && type.Kind == RecoveryScalarKind.Aggregate)
        {
            var hfa = HomogeneousFields(type);
            return !hfa.IsEmpty
                ? new CompositeArgumentLocation(type.Width, hfa.Select((field, index) =>
                    new MachineValuePart(field.ByteOffset * 8, new SlotArgumentLocation($"v{index}", 0, field.Type.Width))).ToImmutableArray())
                : new CompositeArgumentLocation(type.Width, Enumerable.Range(0, (type.Width + 63) / 64).Select(index =>
                    new MachineValuePart(index * 64, new SlotArgumentLocation($"x{index}", 0, Math.Min(64, type.Width - index * 64)))).ToImmutableArray());
        }
        return new SlotArgumentLocation(type.Kind == RecoveryScalarKind.Float ? arm ? "v0" : "xmm0" : arm ? "x0" : "rax", 0, type.Width);
    }

    private static bool Supported(RecoveryScalarType type, MachineAbiKind abi, out string? reason)
    {
        reason = null;
        if (!ValidLayout(type, 0, out reason)) return false;
        if (type.Kind != RecoveryScalarKind.Aggregate) return true;
        if (abi == MachineAbiKind.Aapcs64 && (type.Width <= 128 || !HomogeneousFields(type).IsEmpty) ||
            abi == MachineAbiKind.WindowsX64 && type.Width is 8 or 16 or 32 or 64) return true;
        reason = "聚合需要间接传参或隐藏返回存储；尚无副本、存储范围及别名合同，不能替换为普通指针";
        return false;
    }

    private static bool ValidLayout(RecoveryScalarType? type, int depth, out string? reason)
    {
        reason = null;
        if (type is null || !Enum.IsDefined(type.Kind) || depth > 32)
        { reason = "接口类型为空、种类未知或聚合嵌套超过明确支持范围"; return false; }
        if (type.Kind != RecoveryScalarKind.Aggregate)
        {
            if (type.Aggregate is null && type.Width is >= 1 and <= 64 &&
                (type.Kind != RecoveryScalarKind.Address || type.Width == 64) &&
                (type.Kind != RecoveryScalarKind.Float || type.Width is 32 or 64)) return true;
            reason = "标量接口支持 1–64 位整数、64 位地址与 binary32/64 浮点，不携带聚合布局";
            return false;
        }
        if (type.Width <= 0 || type.Width % 8 != 0 || type.Aggregate is not { } aggregate ||
            aggregate.AlignmentBytes is not (1 or 2 or 4 or 8 or 16) || aggregate.Fields.IsDefaultOrEmpty ||
            aggregate.Fields.Any(field => field is null) ||
            type.Width / 8 % aggregate.AlignmentBytes != 0)
        { reason = "聚合缺少明确的正数大小、1/2/4/8/16 字节对齐或字段布局"; return false; }
        var covered = 0L;
        var naturalAlignment = 1;
        foreach (var field in aggregate.Fields.OrderBy(field => field.ByteOffset))
        {
            if (!ValidLayout(field.Type, depth + 1, out reason)) return false;
            if (field.Type.Kind != RecoveryScalarKind.Aggregate && field.Type.Width is not (8 or 16 or 32 or 64))
            { reason = "聚合叶子只支持已知自然对齐的 8/16/32/64 位标量"; return false; }
            var fieldAlignment = field.Type.Aggregate?.AlignmentBytes ?? field.Type.Width / 8;
            if (field.ByteOffset % fieldAlignment != 0)
            { reason = "聚合字段不满足自然对齐；packed 或成员对齐修饰需要独立接口合同"; return false; }
            naturalAlignment = Math.Max(naturalAlignment, fieldAlignment);
            if (field.ByteOffset != covered || field.Type.Width % 8 != 0)
            { reason = "聚合含未建模的填充、重叠字段或非整字节字段，不能将其作为完整逻辑值"; return false; }
            covered += field.Type.Width / 8;
        }
        if (covered != type.Width / 8)
        { reason = "聚合字段没有完整覆盖存储大小；尾部填充仍需独立证据"; return false; }
        if (aggregate.AlignmentBytes != naturalAlignment)
        { reason = "聚合对齐不同于成员自然对齐；整体过度对齐或 packed 布局不能直接套用普通 ABI"; return false; }
        return true;
    }

    private static ImmutableArray<RecoveryAggregateField> HomogeneousFields(RecoveryScalarType type)
    {
        if (type.Kind != RecoveryScalarKind.Aggregate) return [];
        var fields = Flatten(type, 0).ToImmutableArray();
        return fields.Length is >= 1 and <= 4 && fields.All(field => field.Type.Kind == RecoveryScalarKind.Float &&
            field.Type.Width == fields[0].Type.Width) ? fields : [];

        static IEnumerable<RecoveryAggregateField> Flatten(RecoveryScalarType current, int offset)
        {
            if (current.Kind != RecoveryScalarKind.Aggregate) { yield return new(offset, current); yield break; }
            foreach (var field in current.Aggregate!.Fields.OrderBy(field => field.ByteOffset))
                foreach (var leaf in Flatten(field.Type, offset + field.ByteOffset)) yield return leaf;
        }
    }

    private static bool Numbered(string name, string prefix, int first, int last) =>
        name.StartsWith(prefix, StringComparison.Ordinal) && int.TryParse(name.AsSpan(prefix.Length), out var number) &&
        number >= first && number <= last;

    private static bool IsThreadEnvironment(string slot) => slot is
        "tpidr_el0" or "apia_key" or "apib_key" or "pauth_ia_enabled" or "pauth_ib_enabled" or "bti_bt0" or
        "fsbase" or "gsbase" or "cs" or "es" or "ss" or "ds" or "fs" or "gs";

    private static MachineSlotRelation Preserved(string slot, int width) => new(slot, width,
        [new(0, width, SlotRelationKind.Preserve, slot)]);

    private static ImmutableArray<MachineSlotRelation> HavocAll(IReadOnlyDictionary<string, int> layout) =>
        layout.OrderBy(pair => pair.Key, StringComparer.Ordinal)
            .Select(pair => new MachineSlotRelation(pair.Key, pair.Value, [new(0, pair.Value, SlotRelationKind.Havoc)])).ToImmutableArray();
}
