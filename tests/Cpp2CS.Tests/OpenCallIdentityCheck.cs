using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class OpenCallIdentityCheck
{
    [Command("open-call-identity", "完整开放实例的调用身份与 ABI 边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 1, Assembly = "Calls.Tests.dll", Namespace = "Tests", Name = "Worker",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false };
        var parameter = new GenericParameterDef { Name = "T", Position = 0, Attributes = GenericParameterAttributes.None };
        var generic = new GenericParameterRef("T", true, 0) { Parameter = parameter };
        var method = new MethodDef { Index = 1, Owner = owner, Name = "Apply", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, GenericParameters = [parameter],
            Parameters = [new ParameterDef("value", new ByRefRef(generic), 0, null, false)] };
        var open = MethodRef.Open(method);
        // 此签名只含 this、byref 和 void，不读取映像或值类型字段布局。
        var abi = new ManagedAbi(new FieldLayouts(null!));
        var signature = abi.Classify(open, out _)!;
        var identity = new UnregisteredMethod(0x1000, method, signature, [], [0x2000], []);
        MethodRef? Resolve(MethodRef symbol, Storage? register = null) => UnregisteredMethods.Resolve(identity,
            new Call(0x3000, CallKind.Direct, Expr.C(0x1000, 64)) {
                Sources = [register ?? signature.MethodInfo!.Register], Arguments = [new Symbol(SymbolKind.Method, symbol)] }, v => v, abi, out _);
        var a = new Assertions();
        a.True(!UnregisteredMethods.IsClosed(open) && UnregisteredMethods.IsComplete(open), "开放参数不是缺失参数");
        a.True(Resolve(open) == open, "按引用传递的开放实例保留自身 MethodRef");
        a.True(Resolve(new(method, [], [])) is null, "缺失方法实参不能通过");
        a.True(Resolve(open, Storage.Gpr(7)) is null, "不从错误隐藏参数位置猜测身份");
        var genericType = new TypeDef { Index = 2, Assembly = owner.Assembly, Namespace = owner.Namespace, Name = "Box`1",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, GenericParameters = [parameter] };
        a.True(Resolve(new(method, [], [new DefinitionRef(genericType, [])])) is null, "嵌套实参不完整也拒绝");
        a.True(Resolve(new(method, [], [new DefinitionRef(genericType, [generic])])) is not null, "嵌套开放类型完整且 byref ABI 确定");
        method.Parameters = [method.Parameters[0] with { Type = generic }];
        a.True(Resolve(open) is null, "不受约束的 T 按值传递，布局未知时拒绝");
        method.Parameters = [];
        a.True(Resolve(open) is null, "实参完整但 ABI 改变仍拒绝");
        var resultType = new TypeDef { Index = 3, Assembly = owner.Assembly, Namespace = owner.Namespace, Name = "Result`1",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false, GenericParameters = [parameter] };
        resultType.Fields = [new FieldDef { Index = 1, Owner = resultType, Name = "value", Type = new GenericParameterRef("T", false, 0),
            Offset = 16, Attributes = FieldAttributes.Public }];
        method.ReturnType = new DefinitionRef(resultType, [generic]);
        a.True(UnregisteredMethods.ClassifyInstance(open, abi) is null, "返回结构体中未约束 T 的占位大小不是 ABI 证据");
        var integer = new TypeDef { Index = 4, Assembly = "mscorlib.dll", Namespace = "System", Name = "Int32",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false };
        var intType = new DefinitionRef(integer, []);
        integer.Fields = [new FieldDef { Index = 2, Owner = integer, Name = "m_value", Type = intType, Offset = 16, Attributes = FieldAttributes.Private }];
        method.ReturnType = intType;
        a.True(UnregisteredMethods.ClassifyInstance(open, abi) is { Return.Pieces: [{ Width: 32 }] }, "基元自身的元数据字段不构成结构体布局递归");
        return a.Finish("open-call-identity");
    }
}
