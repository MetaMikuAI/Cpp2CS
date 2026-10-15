#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text.Json;
using Il2CppDumper;

// 解析登记表与编码槽位；名称只用于展示，绑定使用定义索引和泛型实例。
if (args.Length != 4) throw new ArgumentException("MetadataProbe <ELF> <metadata> <script.json> <output.json>");
var binaryBytes = File.ReadAllBytes(args[0]);
var metadataBytes = File.ReadAllBytes(args[1]);
var binarySha256 = Convert.ToHexString(SHA256.HashData(binaryBytes));
var metadataSha256 = Convert.ToHexString(SHA256.HashData(metadataBytes));
using var metadataStream = new MemoryStream(metadataBytes);
using var binaryStream = new MemoryStream(binaryBytes);
var metadata = new Metadata(metadataStream);
if (metadata.Version < 27) throw new NotSupportedException("编码槽位目前只支持 metadata v27+");
var binary = new Elf64(binaryStream);
binary.SetProperties(metadata.Version, metadata.metadataUsagesCount);
if (!binary.PlusSearch(metadata.methodDefs.Count(m => m.methodIndex >= 0), metadata.typeDefs.Length, metadata.imageDefs.Length))
    throw new InvalidOperationException("未找到匹配的 IL2CPP 登记表");
var executor = new Il2CppExecutor(metadata, binary);
var images = new string[metadata.typeDefs.Length];
foreach (var image in metadata.imageDefs)
    for (int i = image.typeStart; i < image.typeStart + image.typeCount; i++) images[i] = metadata.GetStringFromIndex(image.nameIndex);
var typeDefinitionIndexes = metadata.typeDefs.Select((t,i) => (t,i)).ToDictionary(x => x.t, x => x.i);
var shapeIndexes = new Dictionary<Il2CppType,int>();
var shapes = new List<object?>();
int Shape(Il2CppType t)
{
    if (shapeIndexes.TryGetValue(t,out int existing)) return existing;
    int index = shapes.Count;
    shapeIndexes.Add(t,index);
    shapes.Add(null);
    int definition = -1, position = -1, element = -1, rank = 0;
    int[] arguments = [];
    switch (t.type)
    {
        case Il2CppTypeEnum.IL2CPP_TYPE_VAR:
        case Il2CppTypeEnum.IL2CPP_TYPE_MVAR:
            position = executor.GetGenericParameteFromIl2CppType(t).num;
            break;
        case Il2CppTypeEnum.IL2CPP_TYPE_CLASS:
        case Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE:
            definition = typeDefinitionIndexes[executor.GetTypeDefinitionFromIl2CppType(t)];
            break;
        case Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST:
            var generic = binary.MapVATR<Il2CppGenericClass>(t.data.generic_class);
            definition = typeDefinitionIndexes[executor.GetGenericClassTypeDefinition(generic)];
            var instance = binary.MapVATR<Il2CppGenericInst>(generic.context.class_inst);
            arguments = binary.ReadClassArray<ulong>(binary.MapVATR(instance.type_argv),instance.type_argc)
                .Select(p => Shape(binary.GetIl2CppType(p))).ToArray();
            break;
        case Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY:
        case Il2CppTypeEnum.IL2CPP_TYPE_PTR:
            element = Shape(binary.GetIl2CppType(t.data.type));
            rank = t.type == Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY ? 1 : 0;
            break;
        case Il2CppTypeEnum.IL2CPP_TYPE_ARRAY:
            var array = binary.MapVATR<Il2CppArrayType>(t.data.array);
            element = Shape(binary.GetIl2CppType(array.etype));
            rank = array.rank;
            break;
    }
    shapes[index] = new { index, kind = (int)t.type, byRef = t.byref, definition, position, element, rank, arguments };
    return index;
}
var typeDefinitions = metadata.typeDefs.Select((t,i) => new
{
    index = i, assembly = images[i], token = t.token, name = executor.GetTypeDefName(t,true,false),
    valueType = t.IsValueType, isEnum = t.IsEnum,
    genericArity = t.genericContainerIndex < 0 ? 0 : metadata.genericContainers[t.genericContainerIndex].type_argc,
    type = t.byvalTypeIndex, enumStorage = t.IsEnum ? t.elementTypeIndex : -1
}).ToArray();

var definitions = metadata.methodDefs.Select((m, i) => new
{
    index = i, assembly = images[m.declaringType], token = m.token,
    declaringType = m.declaringType, name = metadata.GetStringFromIndex(m.nameIndex),
    owner = executor.GetTypeDefName(metadata.typeDefs[m.declaringType], true, false),
    address = binary.GetRVA(binary.GetMethodPointer(images[m.declaringType], m)),
    flags = m.flags, returnType = m.returnType,
    genericArity = m.genericContainerIndex < 0 ? 0 : metadata.genericContainers[m.genericContainerIndex].type_argc,
    parameterTypes = Enumerable.Range(m.parameterStart, m.parameterCount).Select(p => metadata.parameterDefs[p].typeIndex).ToArray()
}).ToArray();

object[] TypeArguments(int index)
{
    if (index < 0) return [];
    var instance = binary.genericInsts[index];
    return binary.ReadClassArray<ulong>(binary.MapVATR(instance.type_argv), instance.type_argc).Select(pointer =>
    {
        var type = binary.GetIl2CppType(pointer);
        return (object)new { pointer, name = executor.GetTypeName(type, true, false), kind = (int)type.type, byRef = type.byref, shape = Shape(type) };
    }).ToArray();
}
var specs = binary.methodSpecs.Select((m, i) => new
{
    index = i, definition = m.methodDefinitionIndex,
    typeArguments = TypeArguments(m.classIndexIndex), methodArguments = TypeArguments(m.methodIndexIndex),
    address = binary.methodSpecGenericMethodPointers.TryGetValue(m, out var pointer) ? binary.GetRVA(pointer) : 0
}).ToArray();
var runtimeTypes = binary.types.Select((t, i) => new
{
    index = i, name = executor.GetTypeName(t, true, false), kind = (int)t.type, byRef = t.byref, shape = Shape(t)
}).ToArray();
var contexts = binary.rgctxsDictionary.SelectMany(assembly => assembly.Value.Select(owner => new
{
    assembly = assembly.Key, token = owner.Key,
    entries = owner.Value.Select((entry,i) => new
    {
        index = i, kind = (int)entry.type,
        data = (binary.Version >= 27.2 ? binary.MapVATR<Il2CppRGCTXDefinitionData>(entry._data) : entry.data).rgctxDataDummy
    }).ToArray()
})).ToArray();

using var script = JsonDocument.Parse(File.ReadAllText(args[2]));
var slots = new List<object>();
foreach (var item in script.RootElement.GetProperty("ScriptMetadataMethod").EnumerateArray())
{
    ulong address = item.GetProperty("Address").GetUInt64();
    binary.Position = binary.MapVATR(address);
    ulong value = binary.ReadUInt64();
    uint kind = (uint)(value >> 29), index = (uint)((value & 0x1fffffff) >> 1);
    bool valid = value <= uint.MaxValue && (value & 1) == 1 &&
        (kind == 3 && index < definitions.Length || kind == 6 && index < specs.Length);
    slots.Add(new { address, raw = value, kind, index, valid,
        definition = valid ? (kind == 3 ? (int)index : specs[index].definition) : -1,
        displayName = item.GetProperty("Name").GetString() });
}
var result = new
{
    schema = 2,
    binarySha256, metadataSha256,
    metadataVersion = metadata.Version, binaryVersion = binary.Version,
    definitions, specs, runtimeTypes, typeDefinitions, shapes, contexts, slots
};
File.WriteAllText(args[3], JsonSerializer.Serialize(result));
Console.WriteLine($"definitions: {definitions.Length}, specs: {specs.Length}, slots: {slots.Count}");
