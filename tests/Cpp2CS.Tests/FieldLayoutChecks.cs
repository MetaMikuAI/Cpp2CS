using System.Reflection;
using Cpp2CS.Model;
using Cpp2CS.Runtime.Layouts;
namespace Cpp2CS.Tests;

internal static class FieldLayoutChecks
{
    public const string Command = "field-layout";
    internal static void Set(object obj, string name, object value) => obj.GetType().GetProperty(name)!.SetValue(obj, value);
    internal static TypeDef Def(string name, bool value = true, int pack = 0, TypeAttributes attributes = TypeAttributes.SequentialLayout) => new()
    {
        Index = 0, Assembly = "mscorlib.dll", Namespace = "System", Name = name, Token = 0,
        Attributes = attributes, IsValueType = value, IsEnum = false, PackingSize = pack, ClassSizeIsDefault = true
    };
    internal static DefinitionRef Ref(TypeDef d) => new(d, []);
    internal static FieldDef Field(TypeDef owner, TypeRef type, int offset = -1, bool stat = false, bool thread = false)
    {
        var f = new FieldDef { Index = owner.Fields.Count, Owner = owner, Name = "f" + owner.Fields.Count, Type = type, Offset = offset, Attributes = stat ? FieldAttributes.Static : 0 };
        Set(f, nameof(f.IsThreadStatic), thread);
        Set(owner, nameof(owner.Fields), owner.Fields.Append(f).ToArray());
        return f;
    }
    public static int Run()
    {
        var a = new Assertions();
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8);
        var h = (int)spec.Layout.ObjectHeaderSize;
        var b = Ref(Def("Byte")); var i = Ref(Def("Int32")); var l = Ref(Def("Int64"));
        a.True(layouts.SizeAndAlignment(b) == (1, 1) && layouts.SizeAndAlignment(i) == (4, 4) && layouts.SizeAndAlignment(l) == (8, 8), "基元大小对齐");
        a.True(layouts.SizeAndAlignment(Ref(Def("Object", false))) == (8, 8), "引用大小对齐");
        var empty = Def("Empty"); Set(empty, "Size", 1);
        a.True(layouts.Compute(Ref(empty))!.ValueSize == 1, "空值类型");
        var packed = Def("Packed", pack: 1); Field(packed, b, 0); Field(packed, l, 1); Set(packed, "Size", 9);
        a.True(layouts.Compute(Ref(packed)) is { ValueSize: 9, MinimumAlignment: 1 }, "打包");
        var nested = Def("Nested"); Field(nested, Ref(packed)); Field(nested, b);
        a.True(layouts.Compute(Ref(nested))!.ValueSize == 10, "嵌套值类型");
        var explicitType = Def("Overlap", attributes: TypeAttributes.ExplicitLayout); Field(explicitType, l, 0); Field(explicitType, i, 1);
        a.True(layouts.Compute(Ref(explicitType))!.Fields[1].Offset == h + 1, "显式偏移不再对齐");
        var parent = Def("Parent", false); Field(parent, b);
        var child = Def("Child", false); Set(child, "BaseType", Ref(parent)); Field(child, b);
        a.True(layouts.Compute(Ref(child))!.Fields[0].Offset == h + 1, "父类尾部填充复用");
        var generic = Def("Container`1");
        Set(generic, "GenericParameters", new[] { new GenericParameterDef { Name = "T", Position = 0, Attributes = 0 } });
        Field(generic, new GenericParameterRef("T", false, 0));
        a.True(layouts.Of(new DefinitionRef(generic, [l]))!.ValueSize == 8, "泛型代入");
        a.True(layouts.Of(Ref(generic)) is null && layouts.TrySizeAndAlignment(new GenericParameterRef("T", false, 0)) is null, "开放泛型拒绝");
        var storage = Def("Storage"); Field(storage, b); Field(storage, l, stat: true); Field(storage, i, stat: true, thread: true);
        var sl = layouts.Compute(Ref(storage))!;
        a.True(sl.StaticSize == 8 && sl.Statics.Single().Offset == 0 && sl.ThreadStatics.Single().Offset == 0, "静态与线程静态独立排布");
        var recursive = Def("Recursive"); Field(recursive, Ref(recursive));
        for (var repeat = 0; repeat < 2; repeat++)
        {
            var rejected = false;
            try { layouts.Compute(Ref(recursive)); } catch (InvalidDataException) { rejected = true; }
            a.True(rejected, "递归值类型拒绝且清理构建状态");
        }
        var refs = Def("References", pack: 1); Field(refs, b); Field(refs, Ref(Def("Object", false)));
        a.True(layouts.Compute(Ref(refs)) is { HasReferences: true, MinimumAlignment: 8 }, "含引用忽略打包");
        a.True(layouts.Of(Ref(packed)) is { FromMetadata: true, ValueSize: 9 }, "非泛型采用元数据");
        a.True(layouts.Of(Ref(nested)) is null, "非泛型缺元数据不回退猜测");
        var selfStatic = Def("SelfStatic"); Set(selfStatic, "Size", 4);
        Field(selfStatic, i, 0); Field(selfStatic, Ref(selfStatic), 0, stat: true);
        a.True(layouts.Of(Ref(selfStatic)) is { StaticSize: 4, ValueSize: 4 }, "自身值类型静态字段使用实例部分");
        var results = new TypeLayout?[64];
        Parallel.For(0, results.Length, index => results[index] = layouts.Of(new DefinitionRef(generic, [l])));
        a.True(results.All(r => ReferenceEquals(r, results[0])), "并行缓存身份");
        return a.Finish("字段布局");
    }
}
