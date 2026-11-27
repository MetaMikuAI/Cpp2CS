using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.Runtime;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>设计 16.2。按原生入口计数，共享入口的任一已知签名含经内存传递的值即计一次。</summary>
internal static class PassingAudit
{
    public static int Run(string binary, string metadataPath)
    {
        var input = Il2CppInput.Load(binary, metadataPath);
        var file = File.ReadAllBytes(binary);
        var native = new ModelNativeFacts(ModelInput.Facts(input, file), input.Code);
        var target = new Arm64Target(input.Elf, file, input.Code.Methods.Concat(input.Code.MethodInstances)
            .Where(m => m.Entry.HasValue).Select(m => m.Entry!.Value));
        int arguments = 0, returns = 0, unknown = 0, noSnapshot = 0;
        var failures = new Dictionary<string, int>();
        foreach (ulong entry in target.Entries)
        {
            var signatures = native.Signatures(entry - input.Elf.ImageBase, out _);
            bool argument = false, result = false, incomplete = signatures.IsEmpty;
            foreach (var signature in signatures)
            {
                foreach (var type in signature.Parameters)
                {
                    var placement = Aggregate(type);
                    argument |= placement == AggregatePlacement.Reference;
                    incomplete |= placement == AggregatePlacement.Unknown;
                }
                var returned = Aggregate(signature.Return);
                result |= returned == AggregatePlacement.Reference;
                incomplete |= returned == AggregatePlacement.Unknown;
            }
            if (!argument && !result && !incomplete) continue;
            if (SnapshotFailure(target, entry) is { } failure)
            {
                failures[failure] = failures.GetValueOrDefault(failure) + 1;
                noSnapshot++;
                continue;
            }
            if (argument) arguments++;
            if (result) returns++;
            if (incomplete) unknown++;
        }
        Console.WriteLine($"去重登记入口 {target.Entries.Count}，有快照且已证经内存传递的形参 {arguments}，经内存返回 {returns}");
        Console.WriteLine($"有快照但签名或放法不全 {unknown}，上述候选中无快照 {noSnapshot}");
        foreach (var (reason, count) in failures.OrderByDescending(p => p.Value)) Console.WriteLine($"  {reason} {count}");
        return 0;
    }

    private static AggregatePlacement? Aggregate(TypeShape? type) => type?.Kind == StackKind.Value
        ? AggregateConvention.Aapcs64.Classify(type.StorageBits, type.Members) : null;

    private static string? SnapshotFailure(Arm64Target target, ulong entry)
    {
        try
        {
            var lift = target.Lift(entry);
            return lift.Snapshot == null ? lift.Reason ?? "未生成快照" : null;
        }
        catch (FlowException e) { return e.Message; }
    }
}
