using System.Buffers.Binary;
using System.Collections.Frozen;
using System.Collections.Immutable;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.IL;

namespace Cpp2CS.Kernel;

/// <summary>IL 字节的拼装（ECMA-335 III.1.2）。转移一律用长形式，目标用标号，最后回填。</summary>
internal sealed class IlWriter
{
    private static readonly FrozenDictionary<string, OpcodeInfo> byName = Opcodes.All.ToFrozenDictionary(o => o.Name);
    private readonly List<byte> bytes = [];
    private readonly List<(int At, int From, int Label)> fixups = [];
    private readonly Dictionary<int, int> labels = [];

    public int Offset => bytes.Count;
    public static OpcodeInfo? Find(string name) => byName.GetValueOrDefault(name);

    private void Code(string name)
    {
        var opcode = byName[name];
        if (opcode.Size == 2) bytes.Add(0xFE);
        bytes.Add((byte)opcode.Code);
    }

    private void Word(int value)
    {
        Span<byte> buffer = stackalloc byte[4];
        BinaryPrimitives.WriteInt32LittleEndian(buffer, value);
        bytes.AddRange(buffer);
    }

    public void Plain(string name) => Code(name);
    public void Int32(string name, int value) { Code(name); Word(value); }
    public void Variable(string name, int index) { Code(name); bytes.Add((byte)index); bytes.Add((byte)(index >> 8)); }
    public void Branch(string name, int label) { Code(name); fixups.Add((bytes.Count, bytes.Count + 4, label)); Word(0); }
    public void Mark(int label) => labels[label] = bytes.Count;

    public void Switch(IReadOnlyList<int> targets)
    {
        Code("switch");
        Word(targets.Count);
        int end = bytes.Count + 4 * targets.Count;
        foreach (int target in targets) { fixups.Add((bytes.Count, end, target)); Word(0); }
    }

    public ImmutableArray<byte> Build()
    {
        byte[] result = [.. bytes];
        foreach (var (at, from, label) in fixups)
            BinaryPrimitives.WriteInt32LittleEndian(result.AsSpan(at), labels[label] - from);
        return [.. result];
    }
}

/// <summary>声明的格式不对：目录项不能作为声明的操作，或操作数与目录项不符。</summary>
internal sealed class ClaimFormatException(string detail) : Exception(detail);

/// <summary>
/// 声明的模板（设计 9.2：操作的含义来自目录）。内核按声明里的标识自己取：把“各操作数入栈，这一条指令”按目录展开，
/// 得到模板一侧的效果图。Result 是代表操作结果的项；OperandTypes 与 ResultType 是各操作数与结果在求值栈上的类型。
/// </summary>
internal sealed record ClaimTemplate(FlowGraph<TemplateEffect> Graph, MethodBody Body, Term? Result, CatalogEntry Entry,
    ImmutableArray<TypeShape> OperandTypes, TypeShape? ResultType)
{
    /// <summary>类型在求值栈上的形状：不超过 32 位的整数是 int32（ECMA-335 III.1.1）。</summary>
    public static TypeShape OnStack(TypeShape type) =>
        type.Kind == StackKind.Int32 && (type.StorageBits != 32 || type.TwoValued) ? new TypeShape(StackKind.Int32, 32, true, type.Entity) : type;

    public static int StackBits(TypeShape type) => type.Kind == StackKind.Int32 ? 32 : type.StorageBits;

    /// <summary>模板方法体里唯一的记号指向声明给出的实体。</summary>
    private sealed class Tokens(Claim claim) : ITokenResolver
    {
        private EntityRef Entity => claim.Entity ?? throw new ExpansionException("元数据解析不了", "声明没有给出实体");
        public EntityRef Method(int token) => Entity;
        public EntityRef Field(int token) => Entity;
        public EntityRef Type(int token) => Entity;
        public EntityRef String(int token) => Entity;
    }

    public static ClaimTemplate Build(Claim claim, IEntityMetadata metadata, TermPool terms, int pointerBits)
    {
        var entry = OperationCatalog.Entries.FirstOrDefault(e => e.Id == claim.Operation)
            ?? throw new ExpansionException("目录里没有这一项", claim.Operation);
        foreach (var step in entry.Steps)
            if (step.Kind is not (StepKind.ThrowIf or StepKind.Read or StepKind.Write or StepKind.Call or StepKind.RuntimeCall
                or StepKind.ClassInitialize or StepKind.Require))
                throw new ClaimFormatException($"{entry.Id} 是数据搬动或控制转移，不是声明的操作");
        var opcode = IlWriter.Find(entry.Il) ?? throw new ExpansionException("目录项的指令不在指令表里", entry.Il);
        var tokens = new Tokens(claim);
        MethodShape? method = opcode.Operand == OperandKind.Method ? metadata.Method(tokens.Method(0)) : null;
        FieldShape? field = opcode.Operand == OperandKind.Field ? metadata.Field(tokens.Field(0)) : null;
        TypeShape? subject = field?.Type ?? method?.Return;
        if (entry.ImpliedBits > 0) subject = new TypeShape(StackKind.Int32, entry.ImpliedBits, true, default);
        if (opcode.Operand is not (OperandKind.None or OperandKind.Method or OperandKind.Field or OperandKind.Type))
            throw new ClaimFormatException($"{entry.Id} 的内联操作数不是实体");

        // 各操作数在求值栈上的类型：取自被调方法的签名，或目录项对操作数的要求。
        var operands = ImmutableArray.CreateBuilder<TypeShape>();
        if (entry.OperandsFromSignature) operands.AddRange(method!.Parameters.Select(OnStack));
        else
        {
            if (claim.Operands.Length != entry.Operands.Length)
                throw new ClaimFormatException($"{entry.Id} 需要 {entry.Operands.Length} 个操作数，声明给了 {claim.Operands.Length} 个");
            for (int i = 0; i < entry.Operands.Length; i++)
            {
                int width = claim.Operands[i].Width;
                TypeShape Integer(int bits) => new(bits == 32 ? StackKind.Int32 : StackKind.Int64, bits, true, default);
                TypeShape Float(int bits) => new(bits == 32 ? StackKind.Float32 : StackKind.Float64, bits, true, default);
                operands.Add(entry.Operands[i] switch
                {
                    StackClass.Object => new TypeShape(StackKind.Object, pointerBits, false, i == 0 && field is not null ? field.DeclaringType : default),
                    StackClass.Int32 => Integer(32),
                    StackClass.Int64 => Integer(64),
                    StackClass.Integer or StackClass.Scalar when width is 32 or 64 => Integer(width),
                    StackClass.Float32 => Float(32),
                    StackClass.Float64 => Float(64),
                    StackClass.Float when width is 32 or 64 => Float(width),
                    StackClass.ByRef => new TypeShape(StackKind.ByRef, pointerBits, false, default),
                    StackClass.Assignable when subject is not null && subject.Kind != StackKind.Value => OnStack(subject),
                    _ => throw new ClaimFormatException($"{entry.Id} 的第 {i} 个操作数（{entry.Operands[i]}，{width} 位）不在首批范围内"),
                });
            }
        }
        if (claim.Operands.Length != operands.Count)
            throw new ClaimFormatException($"{entry.Id} 需要 {operands.Count} 个操作数，声明给了 {claim.Operands.Length} 个");
        for (int i = 0; i < operands.Count; i++)
            if (claim.Operands[i].Width != StackBits(operands[i]))
                throw new ClaimFormatException($"第 {i} 个操作数是 {claim.Operands[i].Width} 位，{entry.Id} 在栈上需要 {StackBits(operands[i])} 位");

        bool pushes = entry.OperandsFromSignature ? method!.Return is not null : entry.ResultKind != ResultKind.None;
        TypeShape? result = !pushes ? null : entry.ResultKind switch
        {
            ResultKind.Subject => subject is null ? null : OnStack(subject),
            ResultKind.Int32 => new TypeShape(StackKind.Int32, 32, true, default),
            ResultKind.Int64 => new TypeShape(StackKind.Int64, 64, true, default),
            ResultKind.NativeInt => new TypeShape(StackKind.NativeInt, pointerBits, true, default),
            ResultKind.Float32 => new TypeShape(StackKind.Float32, 32, true, default),
            ResultKind.Float64 => new TypeShape(StackKind.Float64, 64, true, default),
            ResultKind.Object => new TypeShape(StackKind.Object, pointerBits, false, opcode.Operand == OperandKind.Type ? claim.Entity ?? default : default),
            ResultKind.ByRef => new TypeShape(StackKind.ByRef, pointerBits, false, default),
            ResultKind.SameAsOperand => operands[0],
            _ => null,
        };
        if (pushes && result is null) throw new ClaimFormatException($"{entry.Id} 的结果类型不能确定");
        if (!pushes && claim.Definition is not null) throw new ClaimFormatException($"{entry.Id} 没有结果，声明却给了定义");

        // 方法体：各操作数入栈，这条指令；有结果时把它留在栈上带过一次转移，使它成为下一个块的参数。
        var il = new IlWriter();
        for (int i = 0; i < operands.Count; i++) il.Variable("ldarg", i);
        int at = il.Offset, after = -1;
        if (opcode.Operand == OperandKind.None) il.Plain(opcode.Name);
        else il.Int32(opcode.Name, 1);
        if (pushes)
        {
            il.Branch("br", 0);
            il.Mark(0);
            after = il.Offset;
            il.Plain("pop");
        }
        il.Plain("ret");
        var shape = new MethodShape(default, false, operands.ToImmutable(), null, VariantCondition.StaticMethod);
        var body = new MethodBody(shape, [], il.Build(), 0, true);
        var expansion = IlExpander.Expand(body, metadata, tokens, terms, 1, pointerBits);
        if (!expansion.Entries.Contains((at, entry.Id)))
            throw new ClaimFormatException($"这条指令按元数据展开成 {expansion.Entries.FirstOrDefault(e => e.Offset == at).Entry}，不是声明的 {entry.Id}");
        Term? value = null;
        if (pushes)
        {
            int block = expansion.BlockOffsets.IndexOf(after);
            value = expansion.Graph.Parameters(new BlockId(block))[^1];
        }
        return new ClaimTemplate(expansion.Graph, body, value, entry, operands.ToImmutable(), result);
    }
}
