using System.Collections.Immutable;
using System.Text;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel;

/// <summary>
/// 效果分量的标识（设计 7.5）：一个出现，或一条边。边用于条件抛出——通往只抛出尾的那条边，
/// 只抛出尾按进入它的边计入各自的检查。
/// </summary>
public readonly record struct EffectRef(BlockId Block, int Index, int Exit) : IComparable<EffectRef>
{
    public static EffectRef Of(OccurrenceId occurrence) => new(occurrence.Block, occurrence.Index, -1);
    public static EffectRef Of(EdgeId edge) => new(edge.Source, -1, edge.Exit);
    public bool IsEdge => Exit >= 0;
    public OccurrenceId Occurrence => new(Block, Index);
    public EdgeId Edge => new(Block, Exit);
    public int CompareTo(EffectRef other) =>
        Block.Index != other.Block.Index ? Block.Index.CompareTo(other.Block.Index)
        : Index != other.Index ? Index.CompareTo(other.Index) : Exit.CompareTo(other.Exit);
    public override string ToString() => IsEdge ? $"B{Block.Index}→出口{Exit}" : $"B{Block.Index}.{Index}";
}

/// <summary>
/// 声明（设计 9.2）：一条不含语义的记录。操作是目录项的标识加它引用的元数据实体；操作数是模板各形参对应的项，
/// 按求值栈上的位宽；落点是这个操作写出的程序点（该序号的出现之前）；占用是它解释的效果分量；
/// 定义是操作的结果代表的原生值。操作的含义来自目录，前提由引擎从模板推出，这里没有地方写。
/// </summary>
public sealed class Claim
{
    public string Operation { get; }
    public EntityRef? Entity { get; }
    public ImmutableArray<Term> Operands { get; }
    public ProgramPoint Landing { get; }
    public ImmutableArray<EffectRef> Occupied { get; }
    public Term? Definition { get; }
    /// <summary>稳定键：只取决于声明的内容。</summary>
    public string Key { get; }

    public Claim(string operation, EntityRef? entity, ImmutableArray<Term> operands, ProgramPoint landing,
        IEnumerable<EffectRef> occupied, Term? definition)
    {
        Operation = operation;
        Entity = entity;
        Operands = operands;
        Landing = landing;
        Occupied = [.. occupied.Distinct().Order()];
        Definition = definition;
        var key = new StringBuilder();
        key.Append(operation).Append('|').Append(entity?.ToString() ?? "-").Append('|').Append(landing.Block.Index).Append('.').Append(landing.Index);
        foreach (var effect in Occupied) key.Append('|').Append(effect);
        foreach (var operand in operands) key.Append("|#").Append(operand.StructuralHash.ToString("x")).Append(':').Append(operand.Width);
        key.Append("|=").Append(definition is null ? "-" : definition.StructuralHash.ToString("x"));
        Key = key.ToString();
    }

    public override string ToString() =>
        $"{Operation}{(Entity is { } e ? " " + e : "")}({string.Join(", ", Operands)}) 落点 B{Landing.Block.Index}.{Landing.Index} 占用 {{{string.Join(", ", Occupied)}}}"
        + (Definition is null ? "" : $" 定义 {Definition}");
}

/// <summary>五项义务（设计 9.3）。</summary>
public enum Obligation : byte { Coverage, Correspondence, Motion, Destination, Legality }

/// <summary>反驳出自哪一层：缺目录项、缺事实（未命名、未定位）、解释层的义务不成立、引擎尚未实现的部分（环、展开出口）、预算耗尽。</summary>
public enum RefutationLayer : byte { Catalog, Fact, Explanation, Engine, Budget }

/// <summary>反驳：第一处不成立的义务与位置。Row 是没能证明独立的那一对效果在独立关系里的行（没有登记时写明这一对）。</summary>
public sealed record Refutation(RefutationLayer Layer, Obligation? Obligation, string Detail, string? Row = null)
{
    public override string ToString() => Layer switch
    {
        RefutationLayer.Explanation => $"{Name(Obligation!.Value)}：{Detail}",
        RefutationLayer.Catalog => $"缺目录项：{Detail}",
        RefutationLayer.Fact => $"缺事实：{Detail}",
        RefutationLayer.Engine => $"引擎未实现：{Detail}",
        _ => $"预算：{Detail}",
    };

    public static string Name(Obligation obligation) => obligation switch
    {
        Kernel.Obligation.Coverage => "覆盖",
        Kernel.Obligation.Correspondence => "对应",
        Kernel.Obligation.Motion => "搬移",
        Kernel.Obligation.Destination => "去向",
        _ => "合法",
    };
}

/// <summary>
/// 凭据（设计 9.3、9.4）：等价引擎签发的证明，五项义务都成立。只有内核能构造。
/// 凭据绑定声明的键与快照的摘要；Before 与 After 是它所附的落点约束，由选择核对：
/// Before 里各块末的分支（确立了证明用到的路径条件）的落点不晚于本声明的落点；
/// After 里各旁观效果的落点不早于本声明的落点。
/// </summary>
public sealed class Certificate
{
    public Claim Claim { get; }
    public string SnapshotDigest { get; }
    public ImmutableArray<BlockId> Before { get; }
    public ImmutableArray<EffectRef> After { get; }
    /// <summary>查询过的独立关系的行。</summary>
    public ImmutableArray<string> Rows { get; }
    /// <summary>用到的有定义条件（设计 9.1）。</summary>
    public ImmutableArray<string> Assumptions { get; }
    /// <summary>各操作数与结果在输出里的静态类型，取自目录与元数据。</summary>
    public ImmutableArray<TypeShape> OperandTypes { get; }
    public TypeShape? ResultType { get; }
    /// <summary>操作把第 0 个操作数当作数组使用时，是元素的存储位宽；否则为 0。</summary>
    public int ElementBits { get; }
    public int Paths { get; }
    public int Steps { get; }

    internal Certificate(Claim claim, string snapshotDigest, ImmutableArray<BlockId> before, ImmutableArray<EffectRef> after,
        ImmutableArray<string> rows, ImmutableArray<string> assumptions, ImmutableArray<TypeShape> operandTypes, TypeShape? resultType,
        int elementBits, int paths, int steps)
    {
        Claim = claim;
        SnapshotDigest = snapshotDigest;
        Before = before;
        After = after;
        Rows = rows;
        Assumptions = assumptions;
        OperandTypes = operandTypes;
        ResultType = resultType;
        ElementBits = elementBits;
        Paths = paths;
        Steps = steps;
    }
}

/// <summary>证明的结论：凭据，或反驳。Rows 是这次证明查询过的独立关系的行，成功与失败都记（设计第 12 节）。</summary>
public sealed record ProofOutcome(Claim Claim, Certificate? Certificate, Refutation? Refutation, ImmutableArray<string> Rows, int Paths, int Steps);

/// <summary>
/// 内核按实体提问的元数据（设计第 8 节）：形状之外，解释层还要问的几件事。
/// Accessible：成员在 from 这个类的方法里能否合法访问；Assignable：一个类型的值能否不经转换当作另一个类型使用；
/// ElementOf：一维零基数组类型的元素类型；FieldAt：类型（含基类）里位于该字节偏移的实例字段；
/// StaticFieldAt：类型自己声明的、位于普通静态区该字节偏移的静态字段。回答不了时为假或为空。
/// </summary>
public interface IEntityMetadata : IMetadataView
{
    bool Accessible(EntityRef member, EntityRef from);
    bool Assignable(EntityRef from, EntityRef to);
    TypeShape? ElementOf(EntityRef array);
    FieldShape? FieldAt(EntityRef type, int offset);
    FieldShape? StaticFieldAt(EntityRef type, int offset);
}

/// <summary>
/// 一个方法的恢复所读的东西：它的快照、它的签名与所属的类、全局事实与元数据。
/// InitializerOf：这个方法是某个类的类型初始化器时，是那个类。Snapshots 按入口给出别的方法的快照。
/// </summary>
public sealed record RecoveryContext(MethodSnapshot Snapshot, MethodShape Host, EntityRef? InitializerOf, Engine.INativeFacts Facts,
    IEntityMetadata Metadata, Func<ulong, MethodSnapshot?>? Snapshots = null);
