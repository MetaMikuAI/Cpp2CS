using System.Collections.Frozen;
using System.Collections.Immutable;
using System.Reflection.Metadata;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.IL;

namespace Cpp2CS.Output;

/// <summary>宿主模块内的元数据记号。无法解析时给出原因。</summary>
public interface IEntityTokens
{
    int Method(EntityRef entity);
    int Field(EntityRef entity);
    int Type(EntityRef entity);
}

/// <summary>方法头及指令的完整字节。无局部变量时签名为空。</summary>
public sealed record CilMethodBody(ImmutableArray<byte> Bytes, ImmutableArray<byte> LocalSignature);
public sealed record CilWriteResult(CilMethodBody? Body, string? Reason, ImmutableArray<Hole> Holes);

/// <summary>ECMA-335 III.1.2、II.25.4。只接受下降构造的方法体。</summary>
public static class CilWriter
{
    private static readonly FrozenDictionary<string, OpcodeInfo> opcodes = Opcodes.All.ToFrozenDictionary(o => o.Name);
    internal sealed record Item(ManagedInstruction Input, OpcodeInfo Form)
    {
        public int Size => Form.Size + (Form.Operand switch
        {
            OperandKind.None => 0,
            OperandKind.Variable8 or OperandKind.Int8 or OperandKind.Branch8 => 1,
            OperandKind.Variable16 => 2,
            OperandKind.Int32 or OperandKind.Branch32 or OperandKind.Method or OperandKind.Field or OperandKind.Type => 4,
            _ => throw new InvalidDataException($"不能写出 {Form.Name} 的操作数 {Form.Operand}"),
        });
    }

    /// <summary>registerLocals 返回 LocalVarSig 在宿主模块里的 StandAloneSig 记号。
    /// typeSignature 提供具名类型在该模块中的完整类型签名（含数组、泛型实例和基元的短编码）。</summary>
    public static CilWriteResult Write(ManagedBody body, IEntityTokens tokens, IMetadataView metadata,
        Func<ImmutableArray<byte>, int> registerLocals, Func<EntityRef, ImmutableArray<byte>> typeSignature)
    {
        if (!body.Complete) return new(null, $"方法体有 {body.Holes.Length} 个洞", body.Holes);
        var code = new List<Item>();
        var labels = new Dictionary<int, int>();
        foreach (var input in body.Instructions)
        {
            if (input.Opcode == ".label")
            {
                if (!labels.TryAdd(checked((int)input.Operand), code.Count)) throw new InvalidDataException($"重复标号 {input.Operand}");
                continue;
            }
            if (!opcodes.TryGetValue(input.Opcode, out var opcode)) throw new InvalidDataException($"未知指令 {input.Opcode}");
            if ((opcode.Flow is FlowKind.Branch or FlowKind.ConditionalBranch) != (input.Target >= 0))
                throw new InvalidDataException($"{input.Opcode} 的转移标号无效");
            if (opcode.Operand == OperandKind.Variable16)
            {
                int count = input.Opcode is "ldarg" or "starg" or "ldarga" ? body.Host.Parameters.Length : body.Locals.Length;
                if (input.Operand < 0 || input.Operand >= count || input.Operand > ushort.MaxValue)
                    throw new InvalidDataException($"{input.Opcode} 的序号 {input.Operand} 越界");
            }
            code.Add(new(input, ShortForm(opcode, input.Operand)));
        }

        int maxStack = StackDepth.Maximum(code, labels, body.Host, metadata);
        if (maxStack > ushort.MaxValue) throw new InvalidDataException($"最大栈深 {maxStack} 超出大头字段的范围");
        int[] offsets = Layout(code, labels);
        var il = new BlobBuilder();
        for (int i = 0; i < code.Count; i++)
        {
            var (input, form) = code[i];
            if (form.Size == 2) il.WriteByte(0xfe);
            il.WriteByte((byte)form.Code);
            switch (form.Operand)
            {
                case OperandKind.None: break;
                case OperandKind.Int8: il.WriteSByte(checked((sbyte)input.Operand)); break;
                case OperandKind.Int32: il.WriteInt32(checked((int)input.Operand)); break;
                case OperandKind.Variable8: il.WriteByte(checked((byte)input.Operand)); break;
                case OperandKind.Variable16: il.WriteUInt16(checked((ushort)input.Operand)); break;
                case OperandKind.Branch8: il.WriteSByte(checked((sbyte)(offsets[labels[input.Target]] - offsets[i + 1]))); break;
                case OperandKind.Branch32: il.WriteInt32(offsets[labels[input.Target]] - offsets[i + 1]); break;
                case OperandKind.Method or OperandKind.Field or OperandKind.Type:
                    il.WriteInt32(Token(input.Entity, form.Operand, tokens));
                    break;
                default: throw new InvalidDataException($"不能写出 {form.Name} 的操作数 {form.Operand}");
            }
        }

        var signature = LocalSignature.Encode(body.Locals, metadata, typeSignature);
        var result = new BlobBuilder();
        // 小头隐含最大栈深 8。局部为空时无需初始化；其余情况用大头保留精确峰值和 InitLocals。
        if (il.Count < 64 && signature.IsEmpty && maxStack == 8)
            result.WriteByte((byte)((il.Count << 2) | 2));
        else
        {
            result.WriteUInt16(0x3013);
            result.WriteUInt16(checked((ushort)maxStack));
            result.WriteInt32(il.Count);
            int token = signature.IsEmpty ? 0 : registerLocals(signature);
            if (!signature.IsEmpty && ((token >>> 24) != 0x11 || (token & 0xffffff) == 0))
                throw new InvalidDataException($"无效的 StandAloneSig 记号 0x{token:x8}");
            result.WriteInt32(token);
        }
        result.LinkSuffix(il);
        return new(new(result.ToImmutableArray(), signature), null, []);
    }

    private static OpcodeInfo ShortForm(OpcodeInfo opcode, long value)
    {
        if (opcode.Name == "ldc.i4" && value is >= -1 and <= 8)
            return opcodes[value == -1 ? "ldc.i4.m1" : $"ldc.i4.{value}"];
        if (opcode.Name is "ldarg" or "ldloc" or "stloc" && value is >= 0 and <= 3)
            return opcodes[$"{opcode.Name}.{value}"];
        if (opcode.Operand == OperandKind.Branch32 || opcode.Operand == OperandKind.Variable16 && value <= byte.MaxValue
            || opcode.Name == "ldc.i4" && value is >= sbyte.MinValue and <= sbyte.MaxValue)
            return opcodes[opcode.Name + ".s"];
        return opcode;
    }

    // 从全短出发，越界的转移加长。加长只会增加跨过它的距离，达到不动点时剩下的短转移全部可编码。
    private static int[] Layout(List<Item> code, Dictionary<int, int> labels)
    {
        var offsets = new int[code.Count + 1];
        bool changed;
        do
        {
            for (int i = 0; i < code.Count; i++) offsets[i + 1] = checked(offsets[i] + code[i].Size);
            changed = false;
            for (int i = 0; i < code.Count; i++)
            {
                var item = code[i];
                if (item.Form.Operand != OperandKind.Branch8) continue;
                int distance = offsets[labels[item.Input.Target]] - offsets[i + 1];
                if (distance is >= sbyte.MinValue and <= sbyte.MaxValue) continue;
                code[i] = item with { Form = opcodes[item.Input.Opcode] };
                changed = true;
            }
        } while (changed);
        return offsets;
    }

    private static int Token(EntityRef? entity, OperandKind kind, IEntityTokens tokens)
    {
        int token = (kind, entity) switch
        {
            (OperandKind.Method, { Kind: EntityKind.Method } m) => tokens.Method(m),
            (OperandKind.Field, { Kind: EntityKind.Field } f) => tokens.Field(f),
            (OperandKind.Type, { Kind: EntityKind.Type } t) => tokens.Type(t),
            _ => throw new InvalidDataException($"{kind} 缺少匹配的实体 {entity}"),
        };
        int table = token >>> 24;
        bool valid = kind switch
        {
            OperandKind.Method => table is 0x06 or 0x0a or 0x2b,
            OperandKind.Field => table is 0x04 or 0x0a,
            _ => table is 0x01 or 0x02 or 0x1b,
        };
        if (!valid || (token & 0xffffff) == 0) throw new InvalidDataException($"{entity} 对应的 {kind} 记号 0x{token:x8} 无效");
        return token;
    }
}
