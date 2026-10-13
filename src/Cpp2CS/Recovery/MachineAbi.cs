using System.Collections.Immutable;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

// AAPCS64 §6.1/§6.8；Microsoft x64 calling convention 的标量接口与保存规则。
public static class MachineAbi
{
    public const string Version = "scalar-abi/1";

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
        if (contract.Signature.Arguments.Any(type => !Supported(type)) ||
            contract.Signature.Result is { } returnType && !Supported(returnType))
        {
            reason = "首批 ABI 接口仅支持 1–64 位整数和 64 位地址；浮点、聚合、可变参数需独立接口合同";
            return false;
        }
        if (!contract.Effects.MayReturn && !contract.Effects.MayThrow &&
            !contract.Effects.MayDiverge && !contract.Effects.MayTerminate)
        {
            reason = "调用合同没有允许的返回、异常、发散或终止行为";
            return false;
        }
        var arm = contract.Abi == MachineAbiKind.Aapcs64;
        var registerCount = arm ? 8 : 4;
        string[] windowsRegisters = ["rcx", "rdx", "r8", "r9"];
        var arguments = contract.Signature.Arguments.Select((type, index) =>
            index < registerCount
                ? (MachineArgumentLocation)new SlotArgumentLocation(arm ? $"x{index}" : windowsRegisters[index], 0, type.Width)
                : new StackArgumentLocation((arm ? 0L : 40L) + 8L * (index - registerCount), type.Width)).ToImmutableArray();
        result = new(arguments,
            contract.Signature.Result is { } returned ? new SlotArgumentLocation(arm ? "x0" : "rax", 0, returned.Width) : null,
            arm ? "sp" : "rsp", 16, arm ? 0 : 8);
        return true;
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
        var prerequisites = contract.Assumptions.Add("adopted ordinary scalar ABI; no variadic, aggregate, non-local-return or floating-environment-setter interface")
            .Add("summary input is callee entry after machine call preparation; normal output is after the return protocol")
            .Add("ABI stack alignment and readable argument/return storage hold on the represented normal path");
        if (contract.Domain?.StableThreadEnvironment == true)
            prerequisites = prerequisites.Add("thread context, segment configuration and authentication/entry-check configuration remain stable across the call");
        return new(contract, mapping, reads, normal, world, prerequisites, outcomes.ToImmutable());

        MachineSlotRelation Relation(string slot, int width)
        {
            if (slot == mapping.StackPointer)
                return new(slot, width, [new(0, width, SlotRelationKind.AddConstant, slot, 0, mapping.NormalReturnSpAdjustment)]);
            if (mapping.Result is { } returned && slot == returned.Slot)
            {
                var segments = ImmutableArray.CreateBuilder<MachineSlotSegment>();
                segments.Add(new(0, returned.Width, SlotRelationKind.Result));
                if (returned.Width < width) segments.Add(new(returned.Width, width - returned.Width, SlotRelationKind.Havoc));
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

    private static bool Supported(RecoveryScalarType type) => type is not null && Enum.IsDefined(type.Kind) &&
        type.Width is >= 1 and <= 64 && (type.Kind != RecoveryScalarKind.Address || type.Width == 64);

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
