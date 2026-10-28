using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class NativeBindingCheck
{
    [Command("native-binding", "相同泛型身份在不同入口使用独立布局缓存", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        TypeDef Type(int index, string name, string assembly = "mscorlib.dll") => new()
        {
            Index = index, Name = name, Assembly = assembly, Namespace = "System", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false,
        };
        var slot = new GenericParameterDef { Name = "T", Position = 0, Attributes = GenericParameterAttributes.None };
        var parameter = new GenericParameterRef("T", false, 0) { Parameter = slot };
        var container = Type(3, "Container", "Tests.dll");
        container.GenericParameters = [slot];
        container.Fields = [new FieldDef { Index = 0, Owner = container, Name = "First", Type = parameter, Attributes = FieldAttributes.Public, Offset = -1 },
            new FieldDef { Index = 1, Owner = container, Name = "Second", Type = parameter, Attributes = FieldAttributes.Public, Offset = -1 }];
        var small = parameter with { Binding = new(NativeBindingKind.Scalar, new DefinitionRef(Type(1, "Int32"), []), 0x100) };
        var large = parameter with { Binding = new(NativeBindingKind.Scalar, new DefinitionRef(Type(2, "Int64"), []), 0x200) };
        var narrow = new DefinitionRef(container, [small]);
        var wide = new DefinitionRef(container, [large]);
        var layouts = new FieldLayouts(null!);
        a.True(narrow.Equals(wide), "布局证据不改变托管泛型身份");
        a.Equal(8, layouts.Of(narrow)!.ValueSize, "第一个入口的两个四字节字段");
        a.Equal(16, layouts.Of(wide)!.ValueSize, "第二个入口不命中第一个入口的缓存");
        a.Equal(8, layouts.Of(narrow)!.ValueSize, "再次读取保留入口身份");
        a.True(!ReferenceEquals(layouts.Of(narrow), layouts.Of(wide)), "原生布局结果独立");
        return a.Finish("native-binding");
    }
}
