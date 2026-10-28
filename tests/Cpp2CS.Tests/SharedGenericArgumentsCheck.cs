using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SharedGenericArgumentsCheck
{
    [Command("shared-generic-arguments", "引用、枚举及嵌套值类型的共享实参", Arguments = "<binary> <metadata>")]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var a = new Assertions();
        TypeDef Definition(int index, string name, bool enumeration = false, bool value = true) => new()
        {
            Index = index, Assembly = "Tests", Namespace = "Tests", Name = name, Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = enumeration,
        };
        var container = Definition(-20, "Value");
        var reference = Definition(-21, "Reference", value: false);
        a.Equal(types.Object, types.SharedGenericArgument(types.String), "引用类型使用 object");
        a.Equal(types.Int32, types.SharedGenericArgument(types.Int32), "普通整数不变成共享枚举");
        a.Equal(types.Object, types.SharedGenericArgument(new DefinitionRef(reference, [types.Int32])), "泛型引用整体共享");
        var index = -1;
        foreach (var number in new[] { types.SByte, types.Byte, types.Int16, types.UInt16, types.Int32, types.UInt32, types.Int64, types.UInt64 })
        {
            var definition = Definition(index--, "Kind" + -index, enumeration: true);
            definition.Fields = [new FieldDef { Index = index--, Owner = definition, Name = "value__", Type = number, Offset = 0, Attributes = FieldAttributes.Public }];
            var original = new DefinitionRef(definition, []);
            var expected = types.CorlibDefinition($"System.{ManagedTypes.PrimitiveName(number)}Enum") is { } shared ? new DefinitionRef(shared, []) : original;
            a.Equal(expected, types.SharedGenericArgument(original), "枚举保持底层整数的宽度和符号");
            a.Equal(number, ManagedTypes.Underlying(types.SharedGenericArgument(original)), "共享后底层整数不变");
            var nested = new DefinitionRef(container, [new DefinitionRef(container, [original, types.String]), number]);
            var expectedNested = new DefinitionRef(container, [new DefinitionRef(container, [expected, types.Object]), number]);
            a.Equal(expectedNested, types.SharedGenericArgument(nested), "嵌套值类型实参递归共享");
            a.Equal(expectedNested, types.SharedGenericArgument(types.SharedGenericArgument(nested)), "重复归约保持不变");
        }
        return a.Finish("shared-generic-arguments");
    }
}
