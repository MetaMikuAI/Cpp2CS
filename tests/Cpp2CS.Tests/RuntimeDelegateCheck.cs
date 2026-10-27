using Cpp2CS.Facts;
using Cpp2CS.Model;
using System.Reflection;

namespace Cpp2CS.Tests;

internal static class RuntimeDelegateCheck
{
    private delegate T Callback<T>(ref T value, int count);

    [Command("runtime-delegate", "委托运行时成员的真实元数据与签名边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var references = new Dictionary<Type, TypeRef>();
        TypeRef Type(Type type)
        {
            if (references.TryGetValue(type, out var known)) return known;
            return references[type] = type.IsByRef ? new ByRefRef(Type(type.GetElementType()!))
                : type.IsGenericParameter ? new GenericParameterRef(type.Name, false, type.GenericParameterPosition)
                : new DefinitionRef(new TypeDef { Index = references.Count, Assembly = "mscorlib.dll", Namespace = type.Namespace ?? "", Name = type.Name,
                    Token = 0, Attributes = type.Attributes, IsValueType = type.IsValueType, IsEnum = type.IsEnum }, []);
        }
        var reflected = typeof(Callback<>);
        var owner = new TypeDef { Index = -1, Assembly = "Tests.dll", Namespace = "Tests", Name = "Callback`1", Token = 0,
            Attributes = reflected.Attributes, IsValueType = false, IsEnum = false, BaseType = Type(reflected.BaseType!) };
        var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.DeclaredOnly;
        owner.Methods = reflected.GetConstructors(flags).Cast<MethodBase>().Concat(reflected.GetMethods(flags)).Select((method, index) => new MethodDef
        {
            Index = index, Owner = owner, Name = method.Name, Token = 0, Attributes = method.Attributes, ImplAttributes = method.GetMethodImplementationFlags(), Slot = -1,
            ReturnType = Type(method is MethodInfo info ? info.ReturnType : typeof(void)),
            Parameters = method.GetParameters().Select(p => new ParameterDef(p.Name!, Type(p.ParameterType), p.Attributes, null, false)).ToArray(),
        }).ToArray();
        var a = new Assertions();
        a.Equal(4, owner.Methods.Count, "CLR 编译的泛型 ref 委托包含四个运行时成员");
        foreach (var method in owner.Methods) a.True(DelegateFacts.IsRuntimeMethod(method), $"真实签名 {method.Name}");
        var begin = owner.Methods.Single(m => m.Name == "BeginInvoke");
        var end = owner.Methods.Single(m => m.Name == "EndInvoke");
        var constructor = owner.Methods.Single(m => m.Name == ".ctor");
        var saved = begin.Parameters;
        begin.Parameters = saved.Skip(1).ToArray();
        a.True(!DelegateFacts.IsRuntimeMethod(begin), "BeginInvoke 不得遗漏原参数");
        begin.Parameters = saved;
        saved = end.Parameters;
        end.Parameters = saved.Reverse().ToArray();
        a.True(!DelegateFacts.IsRuntimeMethod(end), "EndInvoke 保留 ref 参数顺序及末尾结果句柄");
        end.Parameters = saved;
        saved = constructor.Parameters;
        constructor.Parameters = [saved[0], saved[1] with { Type = Type(typeof(ulong)) }];
        a.True(!DelegateFacts.IsRuntimeMethod(constructor), "构造器方法地址必须是 native int");
        constructor.Parameters = saved;
        var originalBase = owner.BaseType;
        owner.BaseType = Type(typeof(object));
        a.True(owner.Methods.All(m => !DelegateFacts.IsRuntimeMethod(m)), "同名普通类不能作为委托运行时声明");
        owner.BaseType = originalBase;
        var ordinary = new MethodDef { Index = -1, Owner = owner, Name = "Invoke", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Virtual, ImplAttributes = MethodImplAttributes.IL, Slot = -1 };
        a.True(!DelegateFacts.IsRuntimeMethod(ordinary), "普通 IL 实现不能仅按方法名删除");
        Callback<int> callback = (ref int value, int count) => value += count;
        var input = 7;
        a.Equal(16, callback(ref input, 9), "CLR 提供泛型委托 Invoke 的返回值");
        a.Equal(16, input, "CLR 保留 ref 参数写回");
        return a.Finish("runtime-delegate");
    }
}
