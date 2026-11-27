using System.Reflection;
using Cpp2CS.Model;
using static Cpp2CS.Input.MetadataFile;

namespace Cpp2CS.Input;

public sealed class Il2CppInput
{
    public Elf64 Elf { get; }
    public MetadataModel Model { get; }
    public CodeMap Code { get; }
    public Lazy<AssemblyMetadata> AssemblyMetadata { get; }
    private readonly MetadataFile metadata;
    private readonly ulong[] fieldTables;

    // vm/GlobalMetadata.cpp::FromTypeDefinition、StructLayoutSizeIsDefault。
    // 第 7 至 10 位给运行时的 packingSize；第 13 至 16 位给反射的显式 packing。
    public (int? Packing, bool DefaultSize) RuntimeLayout(int definition)
    {
        uint bits = Elf64.U32(metadata.Row(Table.Type, definition), 80);
        int code = (int)((bits >> 6) & 15);
        int? packing = code switch { 0 => 0, <= 8 => 1 << (code - 1), _ => null };
        return (packing, (bits & (1u << 11)) != 0);
    }

    /// <summary>已注册字段槽的链接地址；零填充段内的槽也有地址。</summary>
    public (ulong Address, int? FileOffset, int Value)? FieldOffsetSource(int field)
    {
        var f = Model.Fields[field];
        var table = fieldTables[f.Owner];
        if (table == 0) return null;
        ulong slot = table + (ulong)f.Ordinal * 4;
        return (slot, Elf.FileOffset(slot, 4), unchecked((int)Elf.Word(slot)));
    }

    public static Il2CppInput Load(string binary, string metadata) => new(Elf64.Load(binary), new MetadataFile(metadata));

    private Il2CppInput(Elf64 elf, MetadataFile metadata)
    {
        Elf = elf;
        this.metadata = metadata;
        var images = Enumerable.Range(0, metadata.Count(Table.Image)).Select(metadata.Image).ToArray();
        var assemblies = Enumerable.Range(0, metadata.Count(Table.Assembly)).Select(metadata.Assembly).ToArray();
        var reg = Registrations.Locate(elf, metadata, images);
        ulong mr = reg.Metadata;
        var pointers = reg.Vector(elf, mr + 48);
        var runtime = new RuntimeTypes(elf, metadata, pointers);
        fieldTables = reg.Vector(elf, mr + 80);
        var types = new TypeDefinition[metadata.Count(Table.Type)];
        var fields = new FieldDefinition[metadata.Count(Table.Field)];
        var methods = new MethodDefinition[metadata.Count(Table.Method)];
        for (int i = 0; i < images.Length; i++)
        {
            var img = images[i];
            if (assemblies[img.Assembly].Image != i) throw new InvalidDataException($"映像 {i} 的程序集反向索引不符");
            for (int k = 0; k < img.TypeCount; k++)
            {
                int t = img.FirstType + k;
                if (types[t] != null) throw new InvalidDataException($"类型 {t} 从属于两个映像");
                var row = metadata.Row(Table.Type, t);
                if (runtime.At(Int(row, 8)) is not NamedType byValue || byValue.Definition != t || byValue.Arguments.Count != 0)
                    throw new InvalidDataException($"类型 {t} 的 byvalTypeIndex 未指回定义");
                int firstMethod = Int(row, 36), nMethods = Elf64.U16(row, 64);
                int firstField = Int(row, 32), nFields = Elf64.U16(row, 68);
                int firstInterface = Int(row, 52), nInterfaces = Elf64.U16(row, 76);
                metadata.Range(Table.Interface, firstInterface, nInterfaces);
                metadata.Range(Table.Field, firstField, nFields);
                metadata.Range(Table.Method, firstMethod, nMethods);
                int declaring = Int(row, 12), parent = Int(row, 16), container = Int(row, 24);
                bool valueType = (Elf64.U32(row, 80) & 1) != 0;
                int? declaringType = declaring == -1 ? null : runtime.At(declaring) is NamedType d ? d.Definition :
                    throw new InvalidDataException($"类型 {t} 的声明者无类型定义");
                types[t] = new(metadata.Name(Int(row, 4)), metadata.Name(Int(row)), declaringType,
                    parent == -1 ? null : runtime.At(parent), (TypeAttributes)Elf64.U32(row, 28), valueType,
                    Enumerable.Range(0, nInterfaces).Select(j => runtime.At(Int(metadata.Row(Table.Interface, firstInterface + j)))).ToArray(),
                    runtime.Parameters(container, false, t), firstField, nFields, firstMethod, nMethods, Elf64.U32(row, 84));
                for (int j = 0; j < nFields; j++)
                {
                    int index = firstField + j;
                    if (fields[index] != null) throw new InvalidDataException($"字段 {index} 所有权重复");
                    var f = metadata.Row(Table.Field, index);
                    int type = Int(f, 4);
                    var flags = (FieldAttributes)runtime.Flags(type);
                    var (storage, offset) = FieldLayout(elf, fieldTables[t], j, flags, valueType, container != -1);
                    fields[index] = new(t, j, metadata.Name(Int(f)), runtime.At(type), flags, storage, offset, Elf64.U32(f, 8));
                }
                for (int j = 0; j < nMethods; j++)
                {
                    int index = firstMethod + j;
                    var m = metadata.Row(Table.Method, index);
                    if (methods[index] != null || Int(m, 4) != t) throw new InvalidDataException($"方法 {index} 的所有权不符");
                    int start = Int(m, 16), n = Elf64.U16(m, 34);
                    metadata.Range(Table.Parameter, start, n);
                    var ps = new ParameterDefinition[n];
                    for (int p = 0; p < n; p++)
                    {
                        var argument = metadata.Row(Table.Parameter, start + p);
                        int type = Int(argument, 8);
                        ps[p] = new(metadata.Name(Int(argument)), runtime.At(type), (ParameterAttributes)runtime.Flags(type));
                    }
                    methods[index] = new(t, metadata.Name(Int(m)), Elf64.U32(m, 24), (MethodAttributes)Elf64.U16(m, 28),
                        (MethodImplAttributes)Elf64.U16(m, 30), runtime.At(Int(m, 8)), ps, runtime.Parameters(Int(m, 20), true, index));
                }
            }
        }
        if (types.Contains(null!) || fields.Contains(null!) || methods.Contains(null!))
            throw new InvalidDataException("元数据中存在无所有者的定义");

        var insts = reg.Vector(elf, mr + 16);
        TypeReference[] Args(int index) => index == -1 ? [] : runtime.Arguments(insts[index]);
        int count = checked((int)elf.Word(mr + 64));
        var specs = new MethodInstance[count];
        ulong specTable = elf.Pointer(mr + 72);
        for (int i = 0; i < count; i++)
        {
            ulong at = specTable + (ulong)i * 12;
            uint method = elf.Word(at);
            if (method >= methods.Length) throw new InvalidDataException($"方法规格 {i} 的定义下标越界");
            specs[i] = new((int)method, Args(unchecked((int)elf.Word(at + 4))), Args(unchecked((int)elf.Word(at + 8))));
        }

        Model = new(assemblies, images, types, fields, methods, Enumerable.Range(0, pointers.Length).Select(runtime.At).ToArray(),
            Array.ConvertAll(reg.Vector(elf, mr), p => p == 0 ? null : runtime.GenericClass(p)), specs,
            Enumerable.Range(0, metadata.Count(Table.Literal)).Select(metadata.StringLiteral).ToArray());
        Code = reg.ReadCode(elf, Model);
        AssemblyMetadata = new(() =>
        {
            ulong sizes = elf.Pointer(mr + 104);
            return AssemblyTables.Read(metadata, Model, t => (byte)(elf.Word(pointers[t] + 8) >> 16),
                t => elf.Word(elf.Pointer(sizes + (ulong)t * 8)),
                t => (int)elf.Word(elf.Pointer(sizes + (ulong)t * 8) + 4));
        });
    }

    // vm/MetadataCache.cpp::GetFieldOffsetFromIndexLocked；vm/Class.cpp::LayoutFieldsLocked。
    private static (FieldStorage, int?) FieldLayout(Elf64 elf, ulong table, int ordinal, FieldAttributes flags, bool valueType, bool generic)
    {
        if ((flags & FieldAttributes.Literal) != 0) return (FieldStorage.Literal, null);
        bool isStatic = (flags & FieldAttributes.Static) != 0;
        var storage = isStatic ? FieldStorage.Static : FieldStorage.Instance;
        if (table == 0 || generic) return (storage, null);
        int raw = unchecked((int)elf.Word(table + (ulong)ordinal * 4));
        if (isStatic && raw < 0) return (FieldStorage.ThreadStatic, raw & int.MaxValue);
        // Il2CppObject 含 klass 与 monitor 两个指针；值类型的字段以未装箱数据起点为准。
        int offset = valueType && !isStatic ? checked(raw - 16) : raw;
        if (offset < 0) throw new InvalidDataException($"实例字段偏移无效 0x{table + (ulong)ordinal * 4:x}");
        return (storage, offset);
    }
}
