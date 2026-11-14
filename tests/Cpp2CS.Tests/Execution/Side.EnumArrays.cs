using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

internal abstract partial class Side
{
    private readonly Dictionary<ulong, (ulong Array, int Index)> enumIterators = new();

    /// <summary>已知类型句柄返回缓存的非空类型对象；枚举 GetValues 按无符号值排序，Current 每次装箱当前元素。</summary>
    public byte[]? EnumArrayReturn(MethodRef callee, ulong[] arguments)
    {
        if (callee.Method is { Owner.FullName: "System.Type", Name: "GetTypeFromHandle", IsStatic: true }
            && arguments is [var handle])
        {
            // vm/Type.cpp::GetTypeFromHandle 经 Reflection::GetTypeObject 返回句柄所指类型的反射对象。
            var reflectedType = World.TypeOfHandle(handle);
            return ManagedValues.Bytes(World.RuntimeTypeObject(reflectedType), 8);
        }
        if (callee.Method is { Owner.FullName: "System.Enum", Name: "GetValues", IsStatic: true }
            && arguments is [var typeObject] && World.ReflectedType(typeObject) is DefinitionRef { Definition.IsEnum: true } element)
        {
            var size = World.StorageSize(element);
            ulong Bits(object value) => Mask(value is ulong unsigned ? unsigned : unchecked((ulong)Convert.ToInt64(value)), size * 8);
            var values = element.Definition.Fields.Where(f => f.IsStatic && f.Constant is not null).Select(f => Bits(f.Constant!)).Order().ToArray();
            var array = NewArray(new ArrayRef(element, 1), values.Length);
            for (var i = 0; i < values.Length; i++) WriteValue(array + (ulong)(StorageLayout.ArrayData + i * size), values[i], size);
            return ManagedValues.Bytes(array, 8);
        }
        if (callee.Method is { Owner.FullName: "System.Array", Name: "GetEnumerator", IsStatic: false }
            && arguments is [var arrayObject] && arrayObject != 0 && TypeOf(arrayObject) is ArrayRef { Element: DefinitionRef { Definition.IsEnum: true } })
        {
            var iteratorType = new DefinitionRef(World.Types.Corlib("System.Array").Definition.NestedTypes.Single(t => t.Name == "ArrayEnumerator"), []);
            var iterator = New(iteratorType, World.Index.Layouts.Of(iteratorType)!.InstanceSize);
            enumIterators.Add(iterator, (arrayObject, -1));
            return ManagedValues.Bytes(iterator, 8);
        }
        if (arguments is not [var receiver] || !enumIterators.TryGetValue(receiver, out var state)) return null;
        var length = (int)Read64(state.Array + StorageLayout.ArrayMaxLength);
        if (callee.Method.Name == "MoveNext")
        {
            var next = Math.Min(state.Index + 1, length);
            enumIterators[receiver] = (state.Array, next);
            return ManagedValues.Bytes(next < length ? 1UL : 0, 1);
        }
        if (callee.Method.Name != "get_Current") return null;
        if (state.Index < 0 || state.Index >= length) throw new Unsupported("枚举数组的 Current 不在有效位置");
        var item = ((ArrayRef)TypeOf(state.Array)).Element;
        var itemSize = World.StorageSize(item);
        var box = New(item, StorageLayout.ObjectHeaderSize + itemSize);
        RunClassConstructor(item);
        WriteValue(box + StorageLayout.ObjectHeaderSize, ReadValue(state.Array + (ulong)(StorageLayout.ArrayData + state.Index * itemSize), itemSize), itemSize);
        return ManagedValues.Bytes(box, 8);
    }
}
