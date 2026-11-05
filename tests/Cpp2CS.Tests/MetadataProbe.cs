#nullable enable
using Cpp2CS.Input.Portable;

namespace Cpp2CS.Tests;

/// <summary>元数据读取的最小核对：数量、索引宽度与首尾样本。</summary>
internal static class MetadataProbe
{
    public static int Run(string path)
    {
        var metadata = PortableMetadata.Read(path);
        Console.WriteLine($"version {metadata.Version}, typeIndexWidth {metadata.TypeIndexSize}");
        Console.WriteLine($"types {metadata.typeDefs.Length}, methods {metadata.methodDefs.Length}, fields {metadata.fieldDefs.Length}, parameters {metadata.parameterDefs.Length}");
        Console.WriteLine($"images {metadata.imageDefs.Length}, assemblies {metadata.assemblyDefs.Length}, fieldRefs {metadata.fieldRefs.Length}");
        Console.WriteLine($"genericContainers {metadata.genericContainers.Length}, genericParameters {metadata.genericParameters.Length}");
        Console.WriteLine($"stringLiterals {metadata.stringLiterals.Length}, attributeRanges {metadata.attributeDataRanges.Length}");
        Console.WriteLine($"assembliesOffset 0x{metadata.header.assembliesOffset:x} size {metadata.header.assembliesSize}");
        Console.WriteLine($"attributeDataOffset 0x{metadata.header.attributeDataOffset:x} size {metadata.header.attributeDataSize}");

        for (var i = 0; i < Math.Min(3, metadata.typeDefs.Length); i++)
        {
            var type = metadata.typeDefs[i];
            Console.WriteLine($"type[{i}] {metadata.GetStringFromIndex(type.namespaceIndex)}.{metadata.GetStringFromIndex(type.nameIndex)} fields {type.fieldStart}+{type.field_count} methods {type.methodStart}+{type.method_count}");
        }
        for (var i = 0; i < Math.Min(3, metadata.methodDefs.Length); i++)
        {
            var method = metadata.methodDefs[i];
            Console.WriteLine($"method[{i}] {metadata.GetStringFromIndex(method.nameIndex)} decl {method.declaringType} params {method.parameterStart}+{method.parameterCount} token 0x{method.token:x8}");
        }
        for (var i = 0; i < Math.Min(3, metadata.fieldDefs.Length); i++)
        {
            var field = metadata.fieldDefs[i];
            Console.WriteLine($"field[{i}] {metadata.GetStringFromIndex(field.nameIndex)} type {field.typeIndex} token 0x{field.token:x8}");
        }
        for (var i = 0; i < Math.Min(3, metadata.stringLiterals.Length); i++)
            Console.WriteLine($"literal[{i}] {metadata.GetStringLiteralFromIndex((uint)i)}");
        for (var i = 0; i < Math.Min(3, metadata.imageDefs.Length); i++)
        {
            var image = metadata.imageDefs[i];
            Console.WriteLine($"image[{i}] name {metadata.GetStringFromIndex(image.nameIndex)} types {image.typeStart}+{image.typeCount} attrs {image.customAttributeStart}+{image.customAttributeCount}");
        }
        for (var i = 0; i < Math.Min(3, metadata.attributeDataRanges.Length); i++)
            Console.WriteLine($"attrRange[{i}] token 0x{metadata.attributeDataRanges[i].token:x8} start {metadata.attributeDataRanges[i].startOffset}");
        for (var i = 0; i < Math.Min(5, metadata.assemblyDefs.Length); i++)
        {
            var name = metadata.assemblyDefs[i].aname;
            Console.WriteLine($"assembly[{i}] name {name.nameIndex} culture {name.cultureIndex} keyIndex {name.publicKeyIndex} alg {name.hash_alg} len {name.hash_len} flags {name.flags} token {BitConverter.ToString(name.public_key_token)} version {name.major}.{name.minor}.{name.build}.{name.revision}");
        }
        return 0;
    }
}
