using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

internal sealed partial class World
{
    private readonly Dictionary<TypeRef, ulong> runtimeTypeObjects = new();
    private readonly Dictionary<ulong, TypeRef> reflectedRuntimeTypes = new();

    public TypeRef? ReflectedType(ulong address) => reflectedRuntimeTypes.GetValueOrDefault(address);

    /// <summary>缓存的运行时类型对象属于元数据区，不消耗应用对象的堆分配序号。</summary>
    public ulong RuntimeTypeObject(TypeRef type)
    {
        if (runtimeTypeObjects.TryGetValue(type, out var address)) return address;
        var runtimeType = Types.Corlib("System.RuntimeType");
        address = Reserve(Index.Facts.Layouts.Of(runtimeType)!.InstanceSize);
        Put64(address + RuntimeLayout.ObjectKlass, Klass(runtimeType));
        runtimeTypeObjects.Add(type, address);
        reflectedRuntimeTypes.Add(address, type);
        return address;
    }
}

internal abstract partial class Side
{
    /// <summary>非空对象的实际类型、类型的元素类型，以及引用类型的实例检查；自定义 Type 实现不在此模型内。</summary>
    public ulong? RuntimeTypeReturn(MethodRef method, ulong[] arguments)
    {
        if (method.Method.IsStatic || method.Method.Owner.Assembly != "mscorlib.dll") return null;
        if (method.Method is { Owner.FullName: "System.Object", Name: "GetType", Parameters.Count: 0 } && arguments is [var value])
        {
            if (value == 0) throw new Unsupported("GetType 的空接收者未进入反射模型");
            return World.RuntimeTypeObject(TypeOf(value));
        }
        if (method.Method.Owner.FullName is not ("System.Type" or "System.RuntimeType") || arguments.Length == 0
            || World.ReflectedType(arguments[0]) is not { } type) return null;
        if (method.Method is { Name: "GetElementType", Parameters.Count: 0 } && arguments.Length == 1)
            return type switch { ArrayRef a => World.RuntimeTypeObject(a.Element), ByRefRef r => World.RuntimeTypeObject(r.Element),
                PointerRef p => World.RuntimeTypeObject(p.Element), _ => 0 };
        if (method.Method is { Name: "IsInstanceOfType", Parameters.Count: 1 } && arguments is [_, var instance]
            && Cpp2CS.Model.ManagedTypes.IsReferenceType(type))
            return instance != 0 && World.Types.IsAssignable(TypeOf(instance), type) ? 1UL : 0;
        return null;
    }
}
