using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Facts;

/// <summary>设计 18.3。快照中直接以隐含入口参数为基址的内存读取。</summary>
public static class ParameterSummary
{
    public static bool ReadsHidden(MethodSnapshot snapshot, Slot hidden)
    {
        var parameter = snapshot.EntryParameters.FirstOrDefault(p => p.Slot == hidden);
        if (parameter is null) return false;
        foreach (var block in snapshot.Blocks)
            foreach (var occurrence in block.Occurrences)
            {
                if (occurrence is not ReadOccurrence read) continue;
                var address = read.Location;
                if (address == parameter) return true;
                if (address is { Kind: TermKind.Operation, Op: Op.Add } &&
                    (address.Operands[0] == parameter && address.Operands[1].IsConstant ||
                     address.Operands[1] == parameter && address.Operands[0].IsConstant)) return true;
            }
        return false;
    }
}
