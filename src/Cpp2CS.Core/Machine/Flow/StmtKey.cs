using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Flow;

/// <summary>
/// 语句稳定键：(所在块起点, 语句地址, 语句种类, 序号)。序号在“同起点、同地址、同种类”的语句中按块次序与块内次序递增，
/// 尾复制后同址的语句由序号区分。只在同一份 IR 快照上有意义；CFG 不同的比较需改用基于原生地址与路径的键。
/// 用于追踪与影子比较。
/// </summary>
public readonly record struct StmtKey(ulong Block, ulong Address, string Kind, int Ordinal)
{
    /// <summary>按位置给出每条语句的键：结果的第 i 个数组对应 <c>function.Blocks[i]</c>，与块内语句一一对应。</summary>
    public static StmtKey[][] Of(MachineFunction function)
    {
        var seen = new Dictionary<(ulong, ulong, string), int>();
        return function.Blocks.Select(block => block.Statements.Select(statement =>
        {
            var kind = statement.GetType().Name;
            var key = (block.Start, statement.Address, kind);
            var ordinal = seen.GetValueOrDefault(key);
            seen[key] = ordinal + 1;
            return new StmtKey(block.Start, statement.Address, kind, ordinal);
        }).ToArray()).ToArray();
    }

    public override string ToString() => $"0x{Block:x}/0x{Address:x}/{Kind}#{Ordinal}";
}
