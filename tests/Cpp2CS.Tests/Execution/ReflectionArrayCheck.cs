using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

internal static class ReflectionArrayCheck
{
    [Command("reflection-array", "按 CLR 实际数组类型核对协变反射检查", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var world = new World(new WorldIndex(facts, types), 0, new Hints([], []), null);
        var side = new CilSide(world);
        world.Active = side;
        var getType = types.CorlibMethod("System.Object", "GetType")!;
        var elementType = types.CorlibMethod("System.Type", "GetElementType")!;
        var instanceOf = types.CorlibMethod("System.Type", "IsInstanceOfType", types.Object)!;
        var a = new Assertions();
        foreach (var (clrArray, element) in new (object[], TypeRef)[] { (new object[1], types.Object), (new string[1], types.String) })
        {
            var array = side.NewArray(new ArrayRef(element, 1), 1);
            var reflected = side.RuntimeTypeReturn(getType, [array])!.Value;
            a.Equal<TypeRef>(new ArrayRef(element, 1), world.ReflectedType(reflected)!, "GetType 取实际数组类型");
            a.Equal(reflected, side.RuntimeTypeReturn(getType, [array])!.Value, "运行时类型身份稳定");
            var actualElement = side.RuntimeTypeReturn(elementType, [reflected])!.Value;
            a.Equal(element, world.ReflectedType(actualElement)!, "GetElementType 保留协变后的实际元素类型");
            foreach (var value in new object?[] { null, "text", new object() })
            {
                var instance = value is null ? 0 : value is string ? world.String("text") : world.Instance(types.Object, "plain", 0);
                var before = side.Events.Count;
                var expected = clrArray.GetType().GetElementType()!.IsInstanceOfType(value);
                a.Equal(expected ? 1UL : 0, side.RuntimeTypeReturn(instanceOf, [actualElement, instance])!.Value, "与 CLR 的兼容、不兼容及 null 结果一致");
                a.Equal(before, side.Events.Count, "类型查询不产生应用调用事件");
            }
            a.Equal(0UL, side.RuntimeTypeReturn(elementType, [actualElement])!.Value, "普通引用类型没有元素类型");
        }
        return a.Finish("reflection-array");
    }
}
