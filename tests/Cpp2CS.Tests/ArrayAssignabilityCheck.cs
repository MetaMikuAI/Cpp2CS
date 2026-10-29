using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class ArrayAssignabilityCheck
{
    [Command("array-assignability", "数组集合接口与协变的 CLR 对照和拒绝边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var a = new Assertions();
        (TypeRef Managed, Type Clr)[] elements = [(types.Int32, typeof(int)), (types.Int64, typeof(long)),
            (types.String, typeof(string)), (types.Object, typeof(object))];
        foreach (var name in new[] { "IEnumerable", "ICollection", "IList", "IReadOnlyCollection", "IReadOnlyList" })
        {
            var definition = types.CorlibDefinition("System.Collections.Generic." + name)!;
            var clr = typeof(object).Assembly.GetType("System.Collections.Generic." + name + "`1")!;
            foreach (var (from, clrFrom) in elements)
            foreach (var (to, clrTo) in elements)
            {
                var target = new DefinitionRef(definition, [to]);
                a.Equal(clr.MakeGenericType(clrTo).IsAssignableFrom(clrFrom.MakeArrayType()),
                    types.IsAssignable(new ArrayRef(from, 1), target), $"{from}[] → {target}");
                a.True(!types.IsAssignable(new ArrayRef(from, 2), target), "多维数组没有泛型集合接口");
                a.True(!types.IsAssignable(new ArrayRef(from, 1) { IsVector = false }, target), "非向量 rank=1 不作 SZARRAY");
            }
        }
        foreach (var (from, clrFrom) in elements)
        foreach (var (to, clrTo) in elements)
            a.Equal(clrTo.MakeArrayType().IsAssignableFrom(clrFrom.MakeArrayType()),
                types.IsAssignable(new ArrayRef(from, 1), new ArrayRef(to, 1)), $"数组协变 {from} → {to}");
        a.True(!types.IsAssignable(new ArrayRef(types.String, 1), new ArrayRef(types.Object, 2)), "不同秩不能协变");
        a.True(!types.IsAssignable(new ArrayRef(types.String, 1), new ArrayRef(types.Object, 1) { IsVector = false }), "数组形状必须相同");
        a.True(!types.IsAssignable(new ArrayRef(types.Int32, 1), new DefinitionRef(types.CorlibDefinition("System.Collections.Generic.List")!, [types.Int32])), "数组不是 List");
        foreach (var name in new[] { "System.Array", "System.Collections.IEnumerable", "System.Collections.ICollection", "System.Collections.IList" })
            a.True(types.IsAssignable(new ArrayRef(types.Int32, 2), types.Corlib(name)), $"数组沿真实 Array 元数据实现 {name}");
        foreach (var clr in new[] { typeof(IEnumerable<>), typeof(IList<>), typeof(IComparer<>), typeof(Action<>), typeof(List<>) })
        {
            var definition = facts.Model.Types.Single(t => t.Assembly == "mscorlib.dll" && t.Namespace == clr.Namespace && t.Name == clr.Name);
            foreach (var (from, clrFrom) in elements)
            foreach (var (to, clrTo) in elements)
                a.Equal(clr.MakeGenericType(clrTo).IsAssignableFrom(clr.MakeGenericType(clrFrom)),
                    types.IsAssignable(new DefinitionRef(definition, [from]), new DefinitionRef(definition, [to])),
                    "泛型接口/委托变体与类不变性服从 CLR，值类型不发生装箱协变");
        }
        var list = types.CorlibDefinition("System.Collections.Generic.List")!;
        var enumerable = types.CorlibDefinition("System.Collections.Generic.IEnumerable")!;
        foreach (var (from, clrFrom) in elements)
        foreach (var (to, clrTo) in elements)
            a.Equal(typeof(IEnumerable<>).MakeGenericType(clrTo).IsAssignableFrom(typeof(List<>).MakeGenericType(clrFrom)),
                types.IsAssignable(new DefinitionRef(list, [from]), new DefinitionRef(enumerable, [to])), "类实现接口后允许合法协变");
        a.True(types.IsAssignable(new DefinitionRef(enumerable, [new DefinitionRef(enumerable, [types.String])]),
            new DefinitionRef(enumerable, [new DefinitionRef(enumerable, [types.Object])])), "嵌套引用协变逐层核对");
        return a.Finish("array-assignability");
    }
}
