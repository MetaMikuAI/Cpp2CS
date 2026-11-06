using Cpp2CS.Ir;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Effects;

/// <summary>机器语句在托管语义下的效果；地址与类型事实由 TypeOracle 提供。</summary>
internal sealed class MachineEffects(ValueModel values, TypeOracle oracle)
{
    public (EffectSummary Effects, Sym? Root) Read(ReadSym read, IReadOnlySet<Sym> nonNull)
    {
        var location = oracle.Locate(read.Address, read.Width);
        var (root, offset, index, _) = oracle.Decompose(read.Address);
        root = SymTable.Resolve(root);
        var metadata = root is ResultSym { Site: Call { Op.Kind: OpKind.InterfaceInvokeData or OpKind.ResolveGenericVirtual } }
            || oracle.ClassOwner(root) is not null;
        var header = location is null && offset == 0 && index is null && read.Width == 64
            && oracle.TypeOf(root) is { } type && ManagedTypes.IsReferenceType(type);
        var kind = metadata ? MemoryKind.Metadata : location?.Kind switch
        {
            LocationKind.Local => MemoryKind.Local,
            LocationKind.Instance or LocationKind.Length or LocationKind.StringLength => MemoryKind.Instance,
            LocationKind.Element or LocationKind.StringChar => MemoryKind.Element,
            LocationKind.Static or LocationKind.ThreadStatic => MemoryKind.Static,
            LocationKind.Reference => MemoryKind.Reference,
            _ when header => MemoryKind.Instance,
            _ => MemoryKind.Unknown,
        };
        // beforefieldinit 类型的初始化可以在首次访问之前的任何时刻发生（ECMA-335 II.10.5.3.2），读取不构成时序约束。
        if (location is { Kind: LocationKind.Static, Owner: DefinitionRef owner } && (owner.Definition.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) != 0)
            return (new(EffectKind.Read), root);
        return (EffectSummary.Access(kind, nonNull: nonNull.Contains(root)), kind is MemoryKind.Local or MemoryKind.Metadata ? null : root);
    }

    public static EffectSummary Operation(Stmt statement) => statement switch
    {
        Define or Phi or Nop or Jump or Branch or Return or IndirectJump => EffectSummary.None,
        Store => new(EffectKind.Write, ExceptionEffect.Any),
        Call { Op: { } op } => RuntimeOps.Of(op.Kind)?.Behavior ?? EffectSummary.Unknown,
        _ => EffectSummary.Unknown,
    };

    public EffectSummary Statement(Stmt statement, IReadOnlySet<Sym> nonNull)
    {
        var effect = Operation(statement);
        foreach (var read in values.ReadsAt(statement)) effect |= Read(read, nonNull).Effects;
        foreach (var value in values.Operands(statement)) effect |= Computation(value);
        return effect;
    }

    private static EffectSummary Computation(Sym value) => SymTable.Resolve(value) switch
    {
        UnknownSym or UndefSym => EffectSummary.Unknown,
        OpSym op => op.Args.Aggregate(op.Op.Kind == OperatorKind.Binary && op.Op.Binary is BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem
            ? new EffectSummary(EffectKind.None, ExceptionEffect.Other) : EffectSummary.None, (effect, arg) => effect | Computation(arg)),
        SliceSym slice => Computation(slice.Base),
        ConcatSym concat => concat.Parts.Aggregate(EffectSummary.None, (effect, part) => effect | Computation(part)),
        _ => EffectSummary.None,
    };
}
