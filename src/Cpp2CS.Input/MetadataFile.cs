using System.Text;
using Cpp2CS.Model;

namespace Cpp2CS.Input;

// vm/GlobalMetadataFileInternals.h。表的编号是 v31 文件头中 offset/size 对的序号。
internal enum Table
{
    Literal, LiteralData, String, Event, Property, Method, ParameterDefault, FieldDefault, DefaultData,
    FieldSize, Parameter, Field, GenericParameter, Constraint, Container, Nested, Interface, Vtable,
    InterfaceOffset, Type, Image, Assembly, FieldRef, AssemblyRef, AttributeData, AttributeRange,
    UnresolvedType, UnresolvedRange, WindowsType, WindowsString, ExportedType
}

internal sealed class MetadataFile
{
    private readonly byte[] bytes;
    private readonly (int Offset, int Count, int Stride)[] tables;
    private readonly Dictionary<int, string> names = new();
    internal MetadataFile(string path)
    {
        bytes = File.ReadAllBytes(path);
        int[] strides = [8, 1, 1, 24, 20, 36, 12, 12, 1, 12, 12, 12, 16, 4, 16, 4, 4, 4, 8, 88, 40, 64, 8, 4, 1, 8, 4, 8, 8, 1, 4];
        int header = 8 + strides.Length * 8;
        if (bytes.Length < header || Elf64.U32(bytes) != 0xfab11baf || Elf64.U32(bytes, 4) != 31)
            throw new InvalidDataException("需要 v31 全局元数据文件");
        tables = new (int, int, int)[strides.Length];
        for (int i = 0; i < strides.Length; i++)
        {
            int at = Int(bytes, 8 + i * 8), size = Int(bytes, 12 + i * 8);
            if (at < 0 || size < 0 || size % strides[i] != 0 || size > bytes.Length - at || (size != 0 && at < header))
                throw new InvalidDataException($"元数据表 {(Table)i} 的范围无效 0x{at:x}+0x{size:x}");
            tables[i] = (at, size / strides[i], strides[i]);
        }
    }

    internal static int Int(ReadOnlySpan<byte> row, int at = 0) => unchecked((int)Elf64.U32(row, at));
    internal int Count(Table table) => tables[(int)table].Count;
    internal ReadOnlySpan<byte> Data(Table table, int start)
    {
        Range(table, start, 0);
        var (at, size, stride) = tables[(int)table];
        if (stride != 1) throw new InvalidDataException($"{table} 不是字节表");
        return bytes.AsSpan(at + start, size - start);
    }
    internal ReadOnlySpan<byte> Row(Table table, int index)
    {
        var (at, count, stride) = tables[(int)table];
        if ((uint)index >= (uint)count) throw new InvalidDataException($"{table}[{index}] 超出 {count} 行");
        return bytes.AsSpan(at + index * stride, stride);
    }
    internal void Range(Table table, int start, int count)
    {
        if (start == -1 && count == 0) return;
        if (count < 0 || start < 0 || start > Count(table) - count)
            throw new InvalidDataException($"{table} 的行区间无效：{start}+{count}");
    }
    internal string Name(int index)
    {
        if (names.TryGetValue(index, out var value)) return value;
        var (at, size, _) = tables[(int)Table.String];
        value = Elf64.CString(bytes.AsSpan(at, size), checked((uint)index));
        names.Add(index, value);
        return value;
    }
    internal string StringLiteral(int index)
    {
        var row = Row(Table.Literal, index);
        int start = Int(row, 4), size = Int(row);
        Range(Table.LiteralData, start, size);
        return new UTF8Encoding(false, true).GetString(bytes, checked(tables[(int)Table.LiteralData].Offset + start), size);
    }
    internal ImageDefinition Image(int i)
    {
        var row = Row(Table.Image, i);
        int first = Int(row, 8), count = Int(row, 12);
        Range(Table.Type, first, count);
        return new(Name(Int(row)), Int(row, 4), first, count);
    }
    internal AssemblyDefinition Assembly(int i)
    {
        var row = Row(Table.Assembly, i);
        return new(Name(Int(row, 16)), Name(Int(row, 20)), Int(row, 40), Int(row, 44), Int(row, 48), Int(row, 52), Int(row));
    }
}
