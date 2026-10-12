using System.Diagnostics;
using System.Text.RegularExpressions;
using Cpp2CS.Abi;

namespace Cpp2CS.Native;

public sealed record HeaderField(string Name, string Type, int Offset, int Size, string DeclaringRecord)
{
    public string[] Path { get; init; } = [];
}
public sealed record HeaderRecord(string Name, string? Base, string Source, string Kind, (string Name, string Type, int Count)[] Fields);
public sealed class HeaderLayout
{
    private readonly Dictionary<string, HeaderRecord> records = [];
    private readonly Dictionary<string, (int Size, int Align, Dictionary<string, int> Offsets, int Base)> layouts = [];
    private readonly string compiler;
    private readonly HashSet<string> rejectedPacking = [];
    private readonly string scalarAliases;
    private readonly HashSet<string> floatingScalars = ["float", "double"];
    public HeaderLayout(string path, string compiler)
    {
        this.compiler = compiler;
        var text = File.ReadAllText(path);
        var aliases = new List<string>();
        foreach (Match alias in Regex.Matches(text, @"typedef\s+(\w+)\s+(\w+)\s*;"))
            if (Scalars.TryGetValue(alias.Groups[1].Value, out var size) && !Scalars.ContainsKey(alias.Groups[2].Value))
            {
                Scalars.Add(alias.Groups[2].Value, size); aliases.Add(alias.Value);
                if (floatingScalars.Contains(alias.Groups[1].Value)) floatingScalars.Add(alias.Groups[2].Value);
            }
        scalarAliases = string.Join('\n', aliases) + "\n";
        var directives = Regex.Matches(text, @"#\s*pragma\s+pack\s*\(([^)]*)\)").Cast<Match>().ToArray();
        var directiveIndex = 0;
        string? pack = null;
        var packStack = new Stack<string?>();
        foreach (Match m in Regex.Matches(text, @"\b(struct|union)\s+(\w+)\s*(?::\s*(\w+)\s*)?\{([^{}]*)\}\s*;"))
        {
            while (directiveIndex < directives.Length && directives[directiveIndex].Index < m.Index)
            {
                var args = directives[directiveIndex++].Groups[1].Value.Split(',', StringSplitOptions.TrimEntries);
                if (args[0] == "push") { packStack.Push(pack); if (args.Length > 1) pack = args[^1]; }
                else if (args[0] == "pop") pack = packStack.Count > 0 ? packStack.Pop() : "unknown";
                else pack = args[0].Length == 0 ? null : args[0];
            }
            if (pack is not null) rejectedPacking.Add(m.Groups[2].Value);
            var fields = new List<(string, string, int)>();
            foreach (var decl in m.Groups[4].Value.Split(';', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
            {
                var f = Regex.Match(decl, @"^(.+?[\s*])(\w+)\s*(?:\[\s*(\d+)\s*\])?$");
                if (!f.Success) { fields.Clear(); break; }
                fields.Add((f.Groups[2].Value, Symbols.Clean(f.Groups[1].Value), f.Groups[3].Success ? int.Parse(f.Groups[3].Value) : 1));
            }
            records.TryAdd(m.Groups[2].Value, new(m.Groups[2].Value, m.Groups[3].Success ? m.Groups[3].Value : null, m.Value, m.Groups[1].Value, fields.ToArray()));
        }
    }
    private const string Prelude = "typedef signed char int8_t; typedef unsigned char uint8_t; typedef short int16_t; typedef unsigned short uint16_t; typedef int int32_t; typedef unsigned int uint32_t; typedef long long int64_t; typedef unsigned long long uint64_t; typedef unsigned long size_t; typedef long intptr_t; typedef unsigned long uintptr_t; typedef void(*Il2CppMethodPointer)();\n";
    private readonly Dictionary<string, int> Scalars = new()
    {
        ["bool"] = 1, ["char"] = 1, ["int8_t"] = 1, ["uint8_t"] = 1, ["int16_t"] = 2, ["uint16_t"] = 2,
        ["int32_t"] = 4, ["uint32_t"] = 4, ["int"] = 4, ["unsigned int"] = 4, ["float"] = 4,
        ["int64_t"] = 8, ["uint64_t"] = 8, ["double"] = 8, ["intptr_t"] = 8, ["uintptr_t"] = 8, ["size_t"] = 8, ["Il2CppMethodPointer"] = 8
    };
    public int Size(string type)
    {
        if (type.EndsWith('*')) return 8;
        if (Scalars.TryGetValue(type, out var size)) return size;
        Ensure(type); return layouts[type].Size;
    }
    public AbiShape Shape(string type)
    {
        if (type == "void") return AbiShape.Void;
        if (type.EndsWith('*')) return AbiShape.Integer();
        if (floatingScalars.Contains(type)) return AbiShape.Float(Size(type));
        if (Scalars.TryGetValue(type, out var scalar)) return AbiShape.Integer(scalar);
        if (!records.TryGetValue(type, out var record) || record.Kind == "union") return AbiShape.Unknown;
        Ensure(type);
        var fields = Flatten(type, 0).ToArray();
        if (fields.Any(f => records.ContainsKey(f.Type))) return AbiShape.Unknown;
        var layout = layouts[type];
        if (fields.Length > 0 && fields.All(f => floatingScalars.Contains(f.Type) && Size(f.Type) == Size(fields[0].Type)))
        {
            var elementSize = Size(fields[0].Type);
            var count = fields.Sum(f => f.Size) / elementSize;
            var offset = 0;
            var contiguous = fields.All(f => { var matches = f.Offset == offset; offset += f.Size; return matches; });
            if (count is >= 1 and <= 4 && contiguous && layout.Size == offset) return AbiShape.Hfa(elementSize, count);
        }
        return AbiShape.Composite(layout.Size, layout.Align);
    }
    public string? ParentFields(string objectType)
    {
        var name = objectType.TrimEnd('*');
        var fieldsName = name.EndsWith("_o") ? name[..^2] + "_Fields" : name;
        return records.TryGetValue(fieldsName, out var fields) ? fields.Base : null;
    }
    public HeaderField? Field(string pointerType, int offset, int size)
    {
        var root = pointerType.TrimEnd('*');
        if (!records.ContainsKey(root)) return null;
        return Flatten(root, 0).FirstOrDefault(f => f.Offset == offset && f.Size == size);
    }
    public HeaderField? FieldAt(string pointerType, int offset)
    {
        var root = pointerType.TrimEnd('*');
        return records.ContainsKey(root) ? Flatten(root, 0).FirstOrDefault(f => f.Offset == offset) : null;
    }
    public HeaderField[] Members(string type)
    {
        type = type.TrimEnd('*');
        if (!records.TryGetValue(type, out var record)) return [];
        Ensure(type);
        return record.Fields.Select(f => new HeaderField(f.Name, f.Type, layouts[type].Offsets[f.Name], Size(f.Type) * f.Count, type) { Path = [f.Name] }).ToArray();
    }
    public string? ArrayType(string elementType) => records.Values.FirstOrDefault(r => r.Name.EndsWith("_array") &&
        r.Fields.Any(f => f.Name == "m_Items" && f.Type == elementType) && r.Fields.Any(f => f.Name == "max_length"))?.Name;
    public HeaderField? ArrayElements(string type) => type.TrimEnd('*').EndsWith("_array") ? Members(type).SingleOrDefault(f => f.Name == "m_Items") : null;
    public HeaderField? ContainingField(string type, int offset, int size, string? expectedType = null)
    {
        foreach (var field in Members(type))
        {
            if (field.Offset == offset && field.Size == size && (expectedType is null || field.Type == expectedType)) return field;
            if (offset >= field.Offset && offset + size <= field.Offset + field.Size && !field.Type.EndsWith('*') &&
                ContainingField(field.Type, offset - field.Offset, size, expectedType) is { } nested)
                return nested with { Offset = field.Offset + nested.Offset, Path = [.. field.Path, .. nested.Path] };
        }
        return null;
    }
    public IEnumerable<HeaderField> Flatten(string name, int origin)
    {
        Ensure(name);
        var record = records[name];
        var layout = layouts[name];
        if (record.Kind == "union") yield break;
        if (record.Base is not null)
            foreach (var field in Flatten(record.Base, origin + layout.Base)) yield return field;
        foreach (var field in record.Fields)
        {
            var offset = origin + layout.Offsets[field.Name];
            if (records.ContainsKey(field.Type) && field.Count == 1 && records[field.Type].Kind != "union")
                foreach (var nested in Flatten(field.Type, offset)) yield return nested;
            else yield return new(field.Name, field.Type, offset, checked(Size(field.Type) * field.Count), name);
        }
    }
    private void Ensure(string name)
    {
        if (layouts.ContainsKey(name)) return;
        var ordered = new List<HeaderRecord>();
        var seen = new HashSet<string>();
        var active = new HashSet<string>();
        var forwards = new HashSet<string>();
        void Visit(string n)
        {
            if (active.Contains(n)) throw new InvalidDataException("递归值类型布局");
            if (!seen.Add(n)) return;
            if (!records.TryGetValue(n, out var record)) throw new InvalidDataException("缺少布局：" + n);
            if (rejectedPacking.Contains(n)) throw new InvalidDataException("不支持该记录的 pack 布局：" + n);
            active.Add(n);
            if (record.Base is not null) Visit(record.Base);
            foreach (var f in record.Fields)
            {
                if (f.Count <= 0) throw new InvalidDataException("不支持零长数组");
                if (f.Type.EndsWith('*'))
                {
                    var target = f.Type.TrimEnd('*');
                    if (target != "void" && !Scalars.ContainsKey(target)) forwards.Add(target);
                }
                else if (!Scalars.ContainsKey(f.Type)) Visit(f.Type);
            }
            ordered.Add(record); active.Remove(n);
        }
        Visit(name);
        var source = Prelude + scalarAliases + string.Join('\n', forwards.Select(n => $"{(records.TryGetValue(n, out var r) ? r.Kind : "struct")} {n};")) + "\n" + string.Join('\n', ordered.Select(r => r.Source));
        var start = new ProcessStartInfo(compiler) { RedirectStandardInput = true, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false, CreateNoWindow = true };
        foreach (var arg in new[] { "-cc1", "-triple", "aarch64-unknown-linux-gnu", "-x", "c++", "-std=c++17", "-fdump-record-layouts-complete", "-fsyntax-only", "-" }) start.ArgumentList.Add(arg);
        using var process = Process.Start(start)!;
        var outputTask = process.StandardOutput.ReadToEndAsync();
        var errorTask = process.StandardError.ReadToEndAsync();
        process.StandardInput.Write(source); process.StandardInput.Close(); process.WaitForExit();
        var output = outputTask.GetAwaiter().GetResult();
        var error = errorTask.GetAwaiter().GetResult();
        if (process.ExitCode != 0) throw new InvalidDataException("Clang 布局失败：" + error);
        foreach (var section in output.Split("*** Dumping AST Record Layout"))
        {
            var root = Regex.Match(section, @"^\s*0 \| (?:struct|union) (\w+)(?: \(empty\))?\s*$", RegexOptions.Multiline);
            var size = Regex.Match(section, @"\[sizeof=(\d+),.*?align=(\d+),", RegexOptions.Singleline);
            if (!root.Success || !size.Success || !seen.Contains(root.Groups[1].Value)) continue;
            var offsets = new Dictionary<string, int>();
            var baseOffset = 0;
            foreach (Match f in Regex.Matches(section, @"^\s*(\d+) \|   (\S[^\r\n]*)", RegexOptions.Multiline))
            {
                var desc = f.Groups[2].Value;
                if (desc.Contains("(base)")) baseOffset = int.Parse(f.Groups[1].Value);
                else offsets[desc.Replace(" (empty)", "").Split(' ')[^1]] = int.Parse(f.Groups[1].Value);
            }
            layouts[root.Groups[1].Value] = (int.Parse(size.Groups[1].Value), int.Parse(size.Groups[2].Value), offsets, baseOffset);
        }
        if (!layouts.ContainsKey(name)) throw new InvalidDataException("Clang 没有返回布局：" + name);
    }
}
