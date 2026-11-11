using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

public sealed record BranchCoverage(int Offset, bool[] Directions);
public sealed record CoverageResult(int Instructions, int Visited, double Ratio, int[] Unvisited, BranchCoverage[] Branches)
{
    public bool Complete => Visited == Instructions && Branches.All(b => b.Directions.All(x => x));
}

/// <summary>只记录入口方法；分支方向由执行指令直接提供，不从目标地址反推。</summary>
internal sealed class ExecutionCoverage(MethodDefinition entry, ExecutionCoverage? parent = null)
{
    private readonly HashSet<Instruction> visited = [];
    private readonly Dictionary<Instruction, HashSet<int>> branches = [];
    public void Visit(MethodDefinition method, Instruction instruction)
    {
        if (ReferenceEquals(method, entry)) visited.Add(instruction);
        parent?.Visit(method, instruction);
    }
    public void Branch(MethodDefinition method, Instruction instruction, int direction)
    {
        if (!ReferenceEquals(method, entry)) return;
        if (!branches.TryGetValue(instruction, out var directions)) branches.Add(instruction, directions = []);
        directions.Add(direction);
        parent?.Branch(method, instruction, direction);
    }
    public void Merge(ExecutionCoverage other)
    {
        visited.UnionWith(other.visited);
        foreach (var (instruction, directions) in other.branches)
            foreach (var direction in directions) Branch(entry, instruction, direction);
    }
    public CoverageResult Result()
    {
        var instructions = entry.HasBody ? entry.Body.Instructions.ToArray() : [];
        return new(instructions.Length, visited.Count, instructions.Length == 0 ? 0 : (double)visited.Count / instructions.Length,
            instructions.Where(i => !visited.Contains(i)).Select(i => i.Offset).ToArray(),
            instructions.Where(i => i.OpCode.FlowControl == FlowControl.Cond_Branch).Select(i => new BranchCoverage(i.Offset,
                Enumerable.Range(0, i.Operand is Instruction[] targets ? targets.Length + 1 : 2)
                    .Select(d => branches.TryGetValue(i, out var seen) && seen.Contains(d)).ToArray())).ToArray());
    }
}
