using System.Buffers.Binary;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using Cpp2CS.Model;
using static Cpp2CS.Input.MetadataFile;

namespace Cpp2CS.Input;

internal static class AssemblyTables
{
    public static AssemblyMetadata Read(MetadataFile file, MetadataModel model, Func<int, byte> typeCode,
        Func<int, uint> instanceSize, Func<int, int> nativeSize)
    {
        var assemblies = new AssemblyIdentity[model.Assemblies.Count];
        for (int i = 0; i < assemblies.Length; i++)
        {
            var row = file.Row(Table.Assembly, i);
            var data = file.Data(Table.String, Int(row, 24));
            int length = checked((int)Unsigned(ref data));
            byte[] key = data[..length].ToArray();
            byte[] token = length == 0 ? [] : SHA1.HashData(key)[^8..].Reverse().ToArray();
            if (!row[56..64].SequenceEqual(length == 0 ? new byte[8] : token))
                throw new InvalidDataException($"程序集 {i} 的公钥标记不符");
            int start = Int(row, 8), count = Int(row, 12);
            file.Range(Table.AssemblyRef, start, count);
            var refs = Enumerable.Range(0, count).Select(k => Int(file.Row(Table.AssemblyRef, start + k))).ToArray();
            assemblies[i] = new(key, token, (AssemblyFlags)Int(row, 36), (AssemblyHashAlgorithm)Int(row, 28), refs);
        }
        object? Value(ReadOnlySpan<byte> row) => Int(row, 8) == -1 ? null :
            Constant(typeCode(Int(row, 4)), file.Data(Table.DefaultData, Int(row, 8)));
        var fields = new Dictionary<int, object?>();
        var dataFields = new Dictionary<int, byte[]>();
        for (int i = 0; i < file.Count(Table.FieldDefault); i++)
        {
            var row = file.Row(Table.FieldDefault, i);
            int field = Int(row);
            if (model.Fields[field].Flags.HasFlag(FieldAttributes.HasDefault)) fields.Add(field, Value(row));
            if (model.Fields[field].Flags.HasFlag(FieldAttributes.HasFieldRVA))
            {
                if (model.Fields[field].Type is not NamedType { Arguments.Count: 0 } n || !model.Types[n.Definition].ValueType)
                    throw new InvalidDataException($"RVA 字段 {field} 缺少值类型大小");
                int size = checked((int)instanceSize(n.Definition) - 16);
                dataFields.Add(field, file.Data(Table.DefaultData, Int(row, 8))[..size].ToArray());
            }
        }
        var parameters = new Dictionary<int, object?>();
        var missing = new Dictionary<int, string>();
        var core = model.Images.Single(im => Enumerable.Range(im.FirstType, im.TypeCount)
            .Any(i => model.Types[i] is { Namespace: "System", Name: "Object", Parent: null, DeclaringType: null }));
        for (int i = 0; i < file.Count(Table.ParameterDefault); i++)
        {
            var row = file.Row(Table.ParameterDefault, i);
            int index = Int(row);
            var parameter = model.RuntimeTypes[Int(file.Row(Table.Parameter, index), 8)];
            // vm/Parameter.cpp::GetDefaultParameterValueObject 按 Nullable<T> 的 T 解读非空默认值。
            if (Int(row, 8) != -1 && parameter is NamedType { Arguments.Count: 1 } n &&
                n.Definition >= core.FirstType && n.Definition < core.FirstType + core.TypeCount &&
                model.Types[n.Definition] is { Namespace: "System", Name: "Nullable`1", DeclaringType: null } &&
                n.Arguments[0] is NamedType { Arguments.Count: 0 } element)
            {
                byte code = typeCode(Int(file.Row(Table.Type, element.Definition), 8));
                if (code == 0x11)
                    missing.Add(index, "Nullable 的非空默认值指向值类型，BlobReader 对该类型码没有常量解码规则");
                else parameters.Add(index, Constant(code, file.Data(Table.DefaultData, Int(row, 8))));
            }
            else parameters.Add(index, Value(row));
        }
        var defaults = new Dictionary<(int, int), object?>();
        var unknown = new Dictionary<(int, int), string>();
        for (int i = 0; i < model.Methods.Count; i++)
        {
            int start = Int(file.Row(Table.Method, i), 16);
            for (int j = 0; j < model.Methods[i].Parameters.Count; j++)
            {
                if (parameters.TryGetValue(start + j, out var value)) defaults.Add((i, j + 1), value);
                if (missing.TryGetValue(start + j, out var reason)) unknown.Add((i, j + 1), reason);
            }
        }
        // RuntimeType::GetPacking 读取指定位与 native_size；CLI 默认的打包大小编码为零。
        var layouts = new Dictionary<int, (ushort, uint)>();
        for (int i = 0; i < model.Types.Count; i++)
        {
            int bits = Int(file.Row(Table.Type, i), 80);
            int exponent = (bits >> 12) & 15;
            if (exponent > 8) throw new InvalidDataException($"类型 {i} 的打包大小编码越界");
            ushort pack = (ushort)((bits & 1024) != 0 || exponent == 0 ? 0 : 1 << (exponent - 1));
            int size = (bits & 2048) == 0 ? nativeSize(i) : 0;
            if (pack > 0 || size > 0) layouts.Add(i, (pack, (uint)Math.Max(0, size)));
        }
        return new(assemblies, fields, defaults, layouts, dataFields, unknown);
    }

    // utils/MemoryRead.cpp。扩展的五字节形式把剩余四字节按目标小端序存放。
    private static uint Unsigned(ref ReadOnlySpan<byte> bytes)
    {
        byte first = bytes[0];
        uint result;
        int size;
        if (first < 0x80) { result = first; size = 1; }
        else if (first < 0xc0) { result = (uint)((first & 63) << 8 | bytes[1]); size = 2; }
        else if (first < 0xe0) { result = BinaryPrimitives.ReadUInt32BigEndian(bytes) & 0x1fffffff; size = 4; }
        else if (first == 0xf0) { result = BinaryPrimitives.ReadUInt32LittleEndian(bytes[1..]); size = 5; }
        else if (first >= 0xfe) { result = uint.MaxValue - (uint)(0xff - first); size = 1; }
        else throw new InvalidDataException($"压缩整数前缀无效 0x{first:x2}");
        bytes = bytes[size..];
        return result;
    }
    private static int Signed(ref ReadOnlySpan<byte> bytes)
    {
        uint v = Unsigned(ref bytes);
        return (int)(v >> 1) ^ -(int)(v & 1);
    }

    // vm-utils/BlobReader.cpp::GetConstantValueFromBlob。
    private static object? Constant(byte type, ReadOnlySpan<byte> b) => type switch
    {
        2 => b[0] != 0, 3 => (char)BinaryPrimitives.ReadUInt16LittleEndian(b),
        4 => (sbyte)b[0], 5 => b[0], 6 => BinaryPrimitives.ReadInt16LittleEndian(b),
        7 => BinaryPrimitives.ReadUInt16LittleEndian(b), 8 => Signed(ref b), 9 => Unsigned(ref b),
        10 => BinaryPrimitives.ReadInt64LittleEndian(b), 11 => BinaryPrimitives.ReadUInt64LittleEndian(b),
        12 => BinaryPrimitives.ReadSingleLittleEndian(b), 13 => BinaryPrimitives.ReadDoubleLittleEndian(b),
        14 => StringConstant(b),
        _ => throw new InvalidDataException($"字段或参数常量的类型码无效 0x{type:x}"),
    };
    private static string? StringConstant(ReadOnlySpan<byte> bytes)
    {
        int length = Signed(ref bytes);
        return length == -1 ? null : new UTF8Encoding(false, true).GetString(bytes[..length]);
    }
}
