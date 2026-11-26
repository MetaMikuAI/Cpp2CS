using System.Security.Cryptography;
using System.Buffers.Binary;
using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Model;

namespace Cpp2CS.Tools.ForwardCheck;

internal static class MetadataAudit
{
    // 顺序只影响提问顺序。把各行答案写回原位，摘要按模型行序计算。
    public static int Keys(SrmMetadata metadata, bool reverse, string? outputPath)
    {
        var k = metadata.Facts.Keys;
        var m = k.Model;
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        using var output = outputPath == null ? null : File.Create(outputPath);
        int total = 0, absent = 0;
        void Rows(string table, int count, Func<int, long?> query)
        {
            var bytes = new byte[checked(count * 8)];
            int missing = 0;
            for (int j = 0; j < count; j++)
            {
                int i = reverse ? count - 1 - j : j;
                long? key = query(i);
                if (key == null) missing++;
                BinaryPrimitives.WriteInt64LittleEndian(bytes.AsSpan(i * 8), key ?? -1);
            }
            hash.AppendData(bytes);
            output?.Write(bytes);
            total += count;
            absent += missing;
            Console.WriteLine($"{table} {count}，无 Key {missing}");
        }
        Rows("运行时类型", m.RuntimeTypes.Count, i => k.TypeKey(m.RuntimeTypes[i]));
        Rows("类型定义", m.Types.Count, i => k.TypeKey(new NamedType(i, [])));
        Rows("泛型类型登记", m.GenericClasses.Count, i => m.GenericClasses[i] is { } t ? k.TypeKey(t) : null);
        Rows("方法定义", m.Methods.Count, k.MethodKey);
        Rows("方法实例", m.MethodInstances.Count, i => k.MethodKey(m.MethodInstances[i]));
        Rows("字段定义", m.Fields.Count, i => k.FieldKey(i, new(m.Fields[i].Owner, [])));
        var fields = m.GenericClasses.OfType<NamedType>().SelectMany(t => FieldIndices(m, t).Select(i => (t, i))).ToArray();
        Rows("实例字段", fields.Length, i => k.FieldKey(fields[i].i, fields[i].t));
        Rows("字符串", m.StringLiterals.Count, i => k.StringKey(m.StringLiterals[i]));
        Console.WriteLine($"共 {total}，无 Key {absent}，SHA256 {Convert.ToHexString(hash.GetHashAndReset())}");
        return 0;
    }

    private static IEnumerable<int> FieldIndices(MetadataModel model, NamedType t)
    {
        var d = model.Types[t.Definition];
        return Enumerable.Range(d.FieldCount == 0 ? 0 : d.FirstField, d.FieldCount);
    }

    // 输出实体坐标与适配器的回答。DWARF 的独立读数由同目录的 dwarf_layout.py 给出。
    public static int Layouts(SrmMetadata metadata)
    {
        var view = metadata.Facts;
        var m = view.Model;
        static bool Open(TypeReference t) => t switch
        {
            VariableType => true, NamedType n => n.Arguments.Any(Open),
            ArrayType a => Open(a.Element), ReferenceType r => Open(r.Element), PointerType p => Open(p.Element), _ => false,
        };

        static (int? Value, string? Reason) Ask(Func<int?> read)
        {
            try { return (read(), null); }
            catch (ExpansionException e) { return (null, e.Message); }
        }

        void Write(NamedType t, int? generic)
        {
            var d = m.Types[t.Definition];
            bool open = Open(t) || t.Arguments.Count != d.GenericParameters.Count;
            var fields = new List<object>();
            foreach (int i in FieldIndices(m, t))
            {
                var f = m.Fields[i];
                if (f.Storage == FieldStorage.Literal) continue;
                var storage = f.Storage;
                var offset = open ? (Value: (int?)null, Reason: "开放泛型没有布局") : Ask(() => view.FieldOffset(i, t, storage));
                if (!open && generic != null && storage == FieldStorage.Static && offset is (null, null))
                {
                    storage = FieldStorage.ThreadStatic;
                    offset = Ask(() => view.FieldOffset(i, t, storage));
                }
                fields.Add(new { i, f.Ordinal, f.Name, storage = storage.ToString(), offset = offset.Value, reason = offset.Reason });
            }
            var size = d.ValueType && !open ? Ask(() => view.ValueSize(t)) : default;
            Console.WriteLine(JsonSerializer.Serialize(new { definition = t.Definition, generic, key = view.Keys.TypeKey(t), open,
                value = d.ValueType, size = size.Value, sizeReason = size.Reason, fields }));
        }
        for (int i = 0; i < m.Types.Count; i++) Write(new(i, []), null);
        var registered = new HashSet<long?>();
        for (int i = 0; i < m.GenericClasses.Count; i++)
            if (m.GenericClasses[i] is { } t)
            {
                registered.Add(view.Keys.TypeKey(t));
                Write(t, i);
            }
        foreach (var t in m.RuntimeTypes.Select(t => t is ReferenceType r ? r.Element : t).OfType<NamedType>())
            if (t.Arguments.Count != 0 && registered.Add(view.Keys.TypeKey(t))) Write(t, -1);
        return 0;
    }
}
