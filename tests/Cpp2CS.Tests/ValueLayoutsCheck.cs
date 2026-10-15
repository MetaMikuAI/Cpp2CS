using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

/// <summary>自然布局的独立预期：字段对齐、尾部填充、泛型代入以及证据不足时的拒绝。</summary>
internal static class ValueLayoutsCheck
{
    public static int Run()
    {
        var layouts = new ValueLayouts();
        var boolean = Primitive("Boolean");
        var integer = Primitive("Int32");
        var single = Primitive("Single");
        var small = Primitive("Int16");
        var reference = new DefinitionRef(Type("Object", false), []);
        var parameter = new GenericParameterRef("T", false, 0);
        var nullable = Generic("Nullable", ("hasValue", boolean), ("value", parameter));
        var task = Generic("TaskValue", ("source", reference), ("result", parameter), ("token", small));
        Check(new DefinitionRef(nullable, [integer]), 8, 4, 0, 4);
        Check(new DefinitionRef(nullable, [reference]), 16, 8, 0, 8);
        Check(new DefinitionRef(task, [boolean]), 16, 8, 0, 8, 10);
        Check(new DefinitionRef(task, [reference]), 24, 8, 0, 8, 16);

        var vector = Type("Vector3");
        vector.Size = 12;
        vector.Fields = [Field(vector, "x", single, 0), Field(vector, "y", single, 4), Field(vector, "z", single, 8)];
        var vectorRef = new DefinitionRef(vector, []);
        Check(vectorRef, 12, 4, 0, 4, 8);
        Check(new DefinitionRef(nullable, [vectorRef]), 16, 4, 0, 4);
        Check(new DefinitionRef(task, [vectorRef]), 24, 8, 0, 8, 20);
        Require(layouts.Get(new DefinitionRef(nullable, [])) is null, "开放泛型不能当作已实例化布局");
        Require(layouts.Get(new DefinitionRef(nullable, [parameter])) is null, "未确定的值参数不能按指针处理");
        var array = Generic("ArrayWrapper", ("items", new ArrayRef(parameter, 1)));
        Check(new DefinitionRef(array, [parameter]), 8, 8, 0);

        var packed = Generic("Packed", ("data", parameter), packing: 1);
        Require(layouts.Get(new DefinitionRef(packed, [integer])) is null, "自定义 packing 不使用自然布局");
        var explicitType = Generic("Explicit", ("data", parameter), explicitLayout: true);
        Require(layouts.Get(new DefinitionRef(explicitType, [integer])) is null, "显式布局不使用顺序字段推断");
        var padded = Type("WrongSize");
        padded.Size = 8;
        padded.Fields = [Field(padded, "value", integer, 0)];
        Require(layouts.Get(new DefinitionRef(padded, [])) is null, "总大小必须匹配元数据");
        var shifted = Type("WrongOffset");
        shifted.Size = 8;
        shifted.Fields = [Field(shifted, "value", integer, 4)];
        Require(layouts.Get(new DefinitionRef(shifted, [])) is null, "字段偏移必须匹配元数据");
        Require(nullable.Fields.All(f => f.Offset == -1), "实例计算不得改写定义上的偏移");
        Console.WriteLine("泛型值布局检查通过");
        return 0;

        void Check(TypeRef type, int size, int alignment, params int[] offsets)
        {
            var layout = layouts.Get(type);
            Require(layout is not null && layout.Size == size && layout.Alignment == alignment
                && layout.Fields.Select(f => f.Offset).SequenceEqual(offsets), $"{type} 布局不符");
        }
    }

    private static TypeDef Type(string name, bool value = true, int packing = 0, bool explicitLayout = false) => new()
    {
        Index = 0, Assembly = "Test.dll", Namespace = "System", Name = name, Token = 0,
        Attributes = TypeAttributes.Public | (explicitLayout ? TypeAttributes.ExplicitLayout : TypeAttributes.SequentialLayout),
        IsValueType = value, IsEnum = false, PackingSize = packing, ClassSizeIsDefault = true,
    };
    private static TypeRef Primitive(string name) => new DefinitionRef(Type(name), []);
    private static FieldDef Field(TypeDef owner, string name, TypeRef type, int offset) => new()
    {
        Index = 0, Owner = owner, Name = name, Type = type, Offset = offset, Attributes = FieldAttributes.Public,
    };
    private static TypeDef Generic(string name, (string Name, TypeRef Type) first,
        (string Name, TypeRef Type)? second = null, (string Name, TypeRef Type)? third = null, int packing = 0, bool explicitLayout = false)
    {
        var type = Type(name, packing: packing, explicitLayout: explicitLayout);
        type.GenericParameters = [new GenericParameterDef { Name = "T", Position = 0, Attributes = GenericParameterAttributes.None }];
        var fields = new List<FieldDef> { Field(type, first.Name, first.Type, -1) };
        if (second is { } b) fields.Add(Field(type, b.Name, b.Type, -1));
        if (third is { } c) fields.Add(Field(type, c.Name, c.Type, -1));
        type.Fields = fields;
        return type;
    }
    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
