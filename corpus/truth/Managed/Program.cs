using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

if (args.Length != 1) throw new ArgumentException("用法：Managed <ManagedStripped 目录>");
var rows = new List<object>();
foreach (var path in Directory.GetFiles(args[0], "*.dll").Order(StringComparer.Ordinal))
{
    using var module = Mono.Cecil.ModuleDefinition.ReadModule(path);
    using var stream = File.OpenRead(path);
    using var pe = new PEReader(stream);
    var metadata = pe.GetMetadataReader();
    foreach (var handle in metadata.MethodDefinitions)
    {
        var def = metadata.GetMethodDefinition(handle);
        var token = MetadataTokens.GetToken(handle);
        var method = (Mono.Cecil.MethodDefinition)module.LookupToken(token);
        var il = def.RelativeVirtualAddress == 0 ? null : pe.GetMethodBody(def.RelativeVirtualAddress).GetILBytes()!;
        rows.Add(new {
            id = $"{Path.GetFileName(path)}:0x{token:x8}", assembly = Path.GetFileName(path),
            assembly_identity = module.Assembly.Name.FullName, module_mvid = module.Mvid,
            token = $"0x{token:x8}", declaring_type = method.DeclaringType.FullName,
            name = method.Name, signature = method.FullName,
            signature_blob = Convert.ToHexString(metadata.GetBlobBytes(def.Signature)).ToLowerInvariant(),
            generic_arity = method.GenericParameters.Count, generic_type = method.DeclaringType.HasGenericParameters,
            has_body = il != null, rva = def.RelativeVirtualAddress,
            il_size = il?.Length, il_sha256 = il == null ? null : Convert.ToHexString(SHA256.HashData(il)).ToLowerInvariant(),
            il_hex = il == null ? null : Convert.ToHexString(il).ToLowerInvariant(),
            cecil_il_hex = il == null || method.Body.Instructions.Any(i => i.OpCode.OperandType == OperandType.InlineString || i.Operand is Mono.Cecil.GenericParameter) ? null : Convert.ToHexString(Encode(method)).ToLowerInvariant()
        });
    }
}
Console.WriteLine(JsonSerializer.Serialize(rows));

// 独立解码器重编码指令，用于和 PEReader 返回的原始 IL 逐字节交叉核对。
static byte[] Encode(Mono.Cecil.MethodDefinition method)
{
    using var stream = new MemoryStream();
    using var w = new BinaryWriter(stream);
    foreach (var i in method.Body.Instructions)
    {
        if (i.OpCode.Size == 2) w.Write(i.OpCode.Op1);
        w.Write(i.OpCode.Op2);
        var o = i.Operand;
        switch (i.OpCode.OperandType)
        {
            case OperandType.InlineNone: break;
            case OperandType.ShortInlineI: w.Write(unchecked((byte)Convert.ToInt32(o))); break;
            case OperandType.InlineI: w.Write((int)o); break;
            case OperandType.InlineI8: w.Write((long)o); break;
            case OperandType.ShortInlineR: w.Write((float)o); break;
            case OperandType.InlineR: w.Write((double)o); break;
            case OperandType.ShortInlineBrTarget: w.Write(unchecked((byte)(((Instruction)o).Offset - i.Offset - i.GetSize()))); break;
            case OperandType.InlineBrTarget: w.Write(((Instruction)o).Offset - i.Offset - i.GetSize()); break;
            case OperandType.InlineSwitch:
                var targets = (Instruction[])o;
                w.Write(targets.Length);
                foreach (var t in targets) w.Write(t.Offset - i.Offset - i.GetSize());
                break;
            case OperandType.ShortInlineVar: w.Write((byte)((VariableDefinition)o).Index); break;
            case OperandType.InlineVar: w.Write((ushort)((VariableDefinition)o).Index); break;
            case OperandType.ShortInlineArg: w.Write((byte)ArgIndex(method, (ParameterDefinition)o)); break;
            case OperandType.InlineArg: w.Write((ushort)ArgIndex(method, (ParameterDefinition)o)); break;
            case OperandType.InlineString:
                // Cecil 的字符串操作数不保留原标记；由原方法体位置取标记只用于该操作数。
                throw new NotSupportedException("字符串需独立比较解码值");
            default: w.Write(((IMetadataTokenProvider)o).MetadataToken.ToUInt32()); break;
        }
    }
    return stream.ToArray();
}
static int ArgIndex(Mono.Cecil.MethodDefinition m, ParameterDefinition p) => p.Index + (m.HasThis ? 1 : 0);
