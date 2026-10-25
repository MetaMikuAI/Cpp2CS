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
        return a.Finish("array-assignability");
    }
}
