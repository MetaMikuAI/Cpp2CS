#nullable enable
using System.Reflection;
using System.Text;
using Cpp2CS.Native.Images;
using Cpp2CS.Runtime;
using Il2CppDumper;

namespace Cpp2CS.Input;

// 只使用规格中的布局；Dumper 的类在这里仅作为元数据适配的数据容器。
internal sealed class RuntimeData(IImage image, RuntimeSpec spec)
{
    internal IImage Image { get; } = image;
    internal RuntimeSpec Spec { get; } = spec;
    internal Il2CppType[] types = [];
    internal Il2CppMethodSpec[] methodSpecs = [];
    internal Il2CppGenericInst[] genericInsts = [];
    private ulong[] fieldOffsets = [];
    private readonly Dictionary<ulong, Il2CppType> runtimeTypes = [];
    internal double Version => 31;
    internal ulong Offset(string record, string field) => checked((ulong)Spec.Layout.Field(record, field).ByteOffset);
    internal ulong Size(string record) => checked((ulong)Spec.Layout.Record(record).Size);
    internal ulong Number(ulong address, string record, string field)
    {
        var f = Spec.Layout.Field(record, field);
        if (f.BitWidth is not null)
        {
            var b = f.BitStorage;
            return (Image.ReadUnsigned(checked(address + (ulong)b.ByteOffset), checked((int)b.ByteSize)) >> (int)b.BitOffset)
                & ((1UL << (int)b.BitWidth) - 1);
        }
        return Image.ReadUnsigned(checked(address + (ulong)f.ByteOffset), checked((int)f.Size));
    }
    internal ulong Pointer(ulong address) => Image.ReadPointer(address) switch
    {
        PointerTarget.Internal p => p.Offset,
        PointerTarget.Null => 0,
        var target => throw new InvalidDataException($"注册数据 0x{address:x} 不是内部指针：{target}。")
    };
    internal ulong Pointer(ulong address, string record, string field) => Pointer(checked(address + Offset(record, field)));
    internal ulong[] Pointers(ulong address, long count)
    {
        if (count < 0 || count > int.MaxValue) throw new InvalidDataException($"数组长度无效：{count}。");
        if (count == 0) return [];
        if (address == 0 || Image.Query(address).AvailableBytes / (ulong)Image.PointerWidth < (ulong)count)
            throw new InvalidDataException($"注册数组 0x{address:x} 无法容纳 {count} 个指针。");
        var values = new ulong[count];
        for (var i = 0; i < values.Length; i++) values[i] = Pointer(address + (ulong)i * (ulong)Image.PointerWidth);
        return values;
    }
    internal string CString(ulong address)
    {
        var available = Math.Min(Image.Query(address).AvailableBytes, 4096);
        var bytes = new byte[available];
        Image.ReadBytes(address, bytes);
        var end = Array.IndexOf(bytes, (byte)0);
        if (end < 0) throw new InvalidDataException($"注册字符串 0x{address:x} 未终止。");
        return Encoding.UTF8.GetString(bytes, 0, end);
    }
    internal T Read<T>(ulong address) where T : new() => (T)Read(typeof(T), address);
    private object Read(Type type, ulong address)
    {
        if (type == typeof(ulong)) return Pointer(address);
        if (type == typeof(uint)) return (uint)Image.ReadUnsigned(address, sizeof(uint));
        var record = Spec.Layout.Record(type.Name);
        var result = Activator.CreateInstance(type)!;
        foreach (var field in type.GetFields())
        {
            var versions = field.GetCustomAttributes<VersionAttribute>().ToArray();
            if (versions.Length > 0 && !versions.Any(v => Version >= v.Min && Version <= v.Max)) continue;
            var name = field.Name == "adjustorThunk" ? "adjustorThunkIndex" : field.Name;
            var layout = record.Field(name);
            var at = checked(address + (ulong)layout.ByteOffset);
            object value;
            if (!field.FieldType.IsPrimitive) value = Read(field.FieldType, at);
            else if (field.FieldType == typeof(ulong)) value = name.EndsWith("Count", StringComparison.Ordinal)
                ? Number(address, type.Name, name) : Pointer(at);
            else
            {
                var n = Number(address, type.Name, name);
                value = field.FieldType == typeof(long) ? (object)(long)(int)n
                    : field.FieldType == typeof(int) ? (int)n
                    : field.FieldType == typeof(byte) ? (byte)n
                    : (object)(uint)n;
            }
            field.SetValue(result, value);
        }
        return result;
    }
    internal T[] Read<T>(ulong address, long count) where T : new()
    {
        if (typeof(T) == typeof(ulong)) return (T[])(object)Pointers(address, count);
        if (count < 0 || count > int.MaxValue) throw new InvalidDataException($"数组长度无效：{count}。");
        var stride = Size(typeof(T).Name);
        if (count > 0 && (address == 0 || Image.Query(address).AvailableBytes / stride < (ulong)count))
            throw new InvalidDataException($"{typeof(T).Name} 数组越界。");
        var result = new T[count];
        for (var i = 0; i < result.Length; i++) result[i] = Read<T>(address + (ulong)i * stride);
        return result;
    }
    internal Il2CppType GetIl2CppType(ulong pointer)
    {
        if (runtimeTypes.TryGetValue(pointer, out var value)) return value;
        var modifiers = Number(pointer, "Il2CppType", "num_mods");
        if (modifiers != 0) throw new NotSupportedException($"Il2CppType 含 {modifiers} 个未支持的签名修饰符。");
        var type = (Il2CppTypeEnum)Number(pointer, "Il2CppType", "type");
        var dataAddress = pointer + Offset("Il2CppType", "data");
        var data = type is Il2CppTypeEnum.IL2CPP_TYPE_PTR or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY
            or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST
            ? Pointer(dataAddress) : Image.ReadUnsigned(dataAddress, Image.PointerWidth);
        value = new Il2CppType
        {
            type = type, data = new Il2CppType.Union { dummy = data },
            attrs = (uint)Number(pointer, "Il2CppType", "attrs"),
            byref = (uint)Number(pointer, "Il2CppType", "byref"),
            pinned = (uint)Number(pointer, "Il2CppType", "pinned"),
            valuetype = (uint)Number(pointer, "Il2CppType", "valuetype")
        };
        runtimeTypes.Add(pointer, value);
        return value;
    }
    internal void Initialize(ulong address, Metadata metadata)
    {
        var r = Read<Il2CppMetadataRegistration>(address);
        if (r.fieldOffsetsCount != metadata.typeDefs.Length || r.typeDefinitionsSizesCount != metadata.typeDefs.Length)
            throw new InvalidDataException("映像与元数据不匹配：类型定义数量不同。");
        types = Pointers(r.types, r.typesCount).Select(GetIl2CppType).ToArray();
        genericInsts = Pointers(r.genericInsts, r.genericInstsCount).Select(p => Read<Il2CppGenericInst>(p)).ToArray();
        methodSpecs = Read<Il2CppMethodSpec>(r.methodSpecs, r.methodSpecsCount);
        fieldOffsets = Pointers(r.fieldOffsets, r.fieldOffsetsCount);
        if (metadata.fieldDefs.Any(f => f.typeIndex < 0 || f.typeIndex >= types.Length)
            || methodSpecs.Any(m => m.methodDefinitionIndex < 0 || m.methodDefinitionIndex >= metadata.methodDefs.Length))
            throw new InvalidDataException("映像与元数据不匹配：类型或方法规格索引越界。");
    }
    internal int GetFieldOffsetFromIndex(int type, int field, int unused, bool valueType, bool isStatic)
    {
        if (fieldOffsets[type] == 0) return -1;
        var offset = unchecked((int)Image.ReadUnsigned(fieldOffsets[type] + (ulong)field * sizeof(int), sizeof(int)));
        return offset > 0 && valueType && !isStatic ? checked(offset - (int)Spec.Layout.ObjectHeaderSize) : offset;
    }
}
