using System.Diagnostics;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

/// <summary>
/// 载入程序模型并与 Il2CppDumper 的 script.json 对照。script.json 只作一致性参照：
/// 不一致的条目逐条列出，由人工判断哪一侧有误。
/// </summary>
internal static class ModelCheck
{
    public static int Run(string binary, string metadata, string? script)
    {
        var watch = Stopwatch.StartNew();
        var model = Load(binary, metadata);
        Console.WriteLine($"载入      {watch.ElapsedMilliseconds} ms  元数据 v{model.MetadataVersion}");
        Console.WriteLine($"类型      {model.Types.Count}  字段 {model.Fields.Count}  方法 {model.Methods.Count}（有地址 {model.Methods.Count(m => m.Address != 0)}）");
        Console.WriteLine($"运行时类型 {model.RuntimeTypes.Count}  方法实例 {model.MethodSpecs.Count}  字段引用 {model.FieldRefs.Count}  字符串 {model.StringLiterals.Count}");
        Console.WriteLine($"代码地址  {model.Code.Count}（共享多所有者 {model.Code.Count(p => p.Value.Count > 1)}）");
        Console.WriteLine($"vtable    {model.Types.Sum(t => t.VTable.Count)} 槽位，空 {model.Types.Sum(t => t.VTable.Count(s => s is null))}  接口偏移 {model.Types.Sum(t => t.InterfaceOffsets.Count)}");
        var attributes = model.Assemblies.Sum(a => a.CustomAttributes.Count) + model.Types.Sum(t => t.CustomAttributes.Count
            + t.Fields.Sum(f => f.CustomAttributes.Count) + t.Properties.Sum(p => p.CustomAttributes.Count) + t.Events.Sum(e => e.CustomAttributes.Count)
            + t.Methods.Sum(m => m.CustomAttributes.Count + m.ReturnAttributes.Count + m.Parameters.Sum(p => p.CustomAttributes.Count)));
        Console.WriteLine($"特性      {attributes}（返回值 {model.Methods.Sum(m => m.ReturnAttributes.Count)}）  事件 {model.Types.Sum(t => t.Events.Count)}  已知大小 {model.Types.Count(t => t.Size >= 0)}  RVA 数据 {model.Fields.Count(f => f.InitialValue is not null)}（{model.Fields.Sum(f => f.InitialValue?.Length ?? 0)} 字节）");
        if (script is null) return 0;

        using var document = JsonDocument.Parse(File.ReadAllBytes(script));
        var root = document.RootElement;
        var bad = 0;
        void Report(string what)
        {
            if (++bad <= 30) Console.WriteLine("  不一致 " + what);
        }

        var methods = 0;
        foreach (var entry in root.GetProperty("ScriptMethod").EnumerateArray())
        {
            var address = entry.GetProperty("Address").GetUInt64() + model.Image.PreferredBase;
            methods++;
            if (!model.Code.ContainsKey(address)) Report($"方法 0x{address:x} {entry.GetProperty("Name").GetString()} 不在代码表");
        }
        Console.WriteLine($"ScriptMethod         {methods}");

        var tally = new Dictionary<string, int>();
        void Check(string section, ulong address, Func<Usage, bool> agrees, string expected)
        {
            var usage = model.UsageAt(address + model.Image.PreferredBase);
            var key = usage is null ? section + ":未解码" : agrees(usage) ? section + ":一致" : section + ":不同";
            tally[key] = tally.GetValueOrDefault(key) + 1;
            if (usage is null || !agrees(usage)) Report($"{section} 0x{address:x} 期望 {expected} 实得 {usage?.ToString() ?? "null"}");
        }
        foreach (var entry in root.GetProperty("ScriptString").EnumerateArray())
        {
            var value = entry.GetProperty("Value").GetString()!;
            Check("ScriptString", entry.GetProperty("Address").GetUInt64(), u => u.Kind == UsageKind.StringLiteral && (string)u.Value == value, value);
        }
        foreach (var entry in root.GetProperty("ScriptMetadata").EnumerateArray())
        {
            var signature = entry.GetProperty("Signature").GetString()!;
            var kind = entry.GetProperty("Name").GetString()!.StartsWith("Field$") ? UsageKind.FieldInfo
                : signature == "Il2CppType*" ? UsageKind.Il2CppType : UsageKind.TypeInfo;
            Check("ScriptMetadata", entry.GetProperty("Address").GetUInt64(), u => u.Kind == kind, $"{kind} {entry.GetProperty("Name").GetString()}");
        }
        foreach (var entry in root.GetProperty("ScriptMetadataMethod").EnumerateArray())
        {
            var name = entry.GetProperty("Name").GetString()!;
            var kind = name.StartsWith("Field$") ? UsageKind.FieldInfo : UsageKind.MethodRef;
            Check("ScriptMetadataMethod", entry.GetProperty("Address").GetUInt64(),
                u => kind == UsageKind.FieldInfo ? u.Kind == UsageKind.FieldInfo : u.Kind is UsageKind.MethodDef or UsageKind.MethodRef, name);
        }
        foreach (var (key, value) in tally.OrderBy(p => p.Key)) Console.WriteLine($"{key,-28} {value}");
        Console.WriteLine($"不一致合计 {bad}");
        return bad == 0 ? 0 : 1;
    }

    /// <summary>Il2CppDumper 在搜索注册表时会往控制台打印进度，这里临时丢弃。</summary>
    public static ProgramModel Load(string binary, string metadata)
    {
        var console = Console.Out;
        Console.SetOut(TextWriter.Null);
        var (model, _) = ModelBuilder.Load(binary, metadata);
        Console.SetOut(console);
        return model;
    }
}
