using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

internal abstract partial class Side
{
    private readonly Dictionary<TypeRef, ulong> reflectedTypes = new();
    private readonly Dictionary<ulong, TypeRef> reflectionObjects = new();
    private readonly Dictionary<ulong, (ulong Array, int Index)> enumIterators = new();

    /// <summary>枚举数组的库契约：GetValues 按无符号值排序，ArrayEnumerator.Current 每次装箱当前元素。</summary>
    public byte[]? EnumArrayReturn(MethodRef callee, ulong[] arguments)
    {
        if (callee.Method is { Owner.FullName: "System.Type", Name: "GetTypeFromHandle", IsStatic: true }
            && arguments is [var handle] && World.TypeOfHandle(handle) is DefinitionRef { Definition.IsEnum: true } enumType)
        {
            if (!reflectedTypes.TryGetValue(enumType, out var reflected))
            {
                var runtimeType = World.Types.Corlib("System.RuntimeType");
                reflected = New(runtimeType, World.Index.Facts.Layouts.Of(runtimeType)!.InstanceSize);
                reflectedTypes.Add(enumType, reflected);
                reflectionObjects.Add(reflected, enumType);
            }
            return StructAbi.Bytes(reflected, 8);
        }
        if (callee.Method is { Owner.FullName: "System.Enum", Name: "GetValues", IsStatic: true }
            && arguments is [var typeObject] && reflectionObjects.GetValueOrDefault(typeObject) is DefinitionRef element)
        {
            var size = World.StorageSize(element);
            ulong Bits(object value) => Mask(value is ulong unsigned ? unsigned : unchecked((ulong)Convert.ToInt64(value)), size * 8);
            var values = element.Definition.Fields.Where(f => f.IsStatic && f.Constant is not null).Select(f => Bits(f.Constant!)).Order().ToArray();
            var array = NewArray(new ArrayRef(element, 1), values.Length);
            for (var i = 0; i < values.Length; i++) WriteValue(array + (ulong)(RuntimeLayout.ArrayData + i * size), values[i], size);
            return StructAbi.Bytes(array, 8);
        }
        if (callee.Method is { Owner.FullName: "System.Array", Name: "GetEnumerator", IsStatic: false }
            && arguments is [var arrayObject] && arrayObject != 0 && TypeOf(arrayObject) is ArrayRef { Element: DefinitionRef { Definition.IsEnum: true } })
        {
            var iteratorType = new DefinitionRef(World.Types.Corlib("System.Array").Definition.NestedTypes.Single(t => t.Name == "ArrayEnumerator"), []);
            var iterator = New(iteratorType, World.Index.Facts.Layouts.Of(iteratorType)!.InstanceSize);
            enumIterators.Add(iterator, (arrayObject, -1));
            return StructAbi.Bytes(iterator, 8);
        }
        if (arguments is not [var receiver] || !enumIterators.TryGetValue(receiver, out var state)) return null;
        var length = (int)Read64(state.Array + RuntimeLayout.ArrayMaxLength);
        if (callee.Method.Name == "MoveNext")
        {
            var next = Math.Min(state.Index + 1, length);
            enumIterators[receiver] = (state.Array, next);
            return StructAbi.Bytes(next < length ? 1UL : 0, 1);
        }
        if (callee.Method.Name != "get_Current") return null;
        if (state.Index < 0 || state.Index >= length) throw new Unsupported("枚举数组的 Current 不在有效位置");
        var item = ((ArrayRef)TypeOf(state.Array)).Element;
        var itemSize = World.StorageSize(item);
        var box = New(item, RuntimeLayout.ObjectHeaderSize + itemSize);
        RunClassConstructor(item);
        WriteValue(box + RuntimeLayout.ObjectHeaderSize, ReadValue(state.Array + (ulong)(RuntimeLayout.ArrayData + state.Index * itemSize), itemSize), itemSize);
        return StructAbi.Bytes(box, 8);
    }
}
