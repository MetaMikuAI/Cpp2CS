using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class SharedSignatureCheck
{
    [Command("shared-signature", "完全共享泛型的参数、返回缓冲区与隐藏参数位置", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 1, Assembly = "Shared.Tests.dll", Namespace = "Tests", Name = "Functions",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var t = new GenericParameterDef { Name = "T", Position = 0, Attributes = GenericParameterAttributes.None };
        var u = new GenericParameterDef { Name = "U", Position = 1, Attributes = GenericParameterAttributes.None };
        var input = new GenericParameterRef("T", true, 0) { Parameter = t };
        var output = new GenericParameterRef("U", true, 1) { Parameter = u };
        var method = new MethodDef { Index = 1, Owner = owner, Name = "Map", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1,
            GenericParameters = [t, u], ReturnType = output,
            Parameters = [new("context", new DefinitionRef(owner, []), 0, null, false), new("value", input, 0, null, false)] };
        var abi = new ManagedAbi(new FieldLayouts(null!));
        var a = new Assertions();
        a.True(abi.Classify(MethodRef.Open(method), out _) is null, "开放签名本身不提供共享 ABI 证据");
        var shared = new MethodRef(method, [], [input with { Binding = new(NativeBindingKind.Shared) }, output with { Binding = new(NativeBindingKind.Shared) }]);
        var signature = abi.Classify(shared, out _)!;
        a.True(signature.Parameters[1] is { Passing: Passing.Shared, Pieces: [{ Width: 64 }] }, "T 保留引用值或值副本地址的双重形式");
        a.Equal(Storage.Gpr(1), signature.Parameters[1].Pieces[0].Register, "T 在第二个整数参数位置");
        a.Equal(Storage.Gpr(2), signature.Return!.Pieces[0].Register, "共享返回缓冲区紧随显式参数");
        a.Equal(Storage.Gpr(3), signature.MethodInfo!.Register, "MethodInfo 位于返回缓冲区之后");
        a.True(signature.Results.Length == 0 && signature.Reads.Contains(Storage.Gpr(2)), "返回缓冲区是输入地址");
        a.True(abi.Kind(shared.MethodArguments[0]) is null, "共享 T 不成为可参与整数运算的标量");
        method.ReturnType = new ByRefRef(output);
        signature = abi.Classify(shared, out _)!;
        a.True(signature.Return is { Passing: Passing.Registers } && signature.Return.Pieces[0].Register == Storage.Gpr(0)
            && signature.MethodInfo!.Register == Storage.Gpr(2), "ref U 返回指针，不额外插入共享返回缓冲区");
        method.ReturnType = output;
        method.Parameters = Enumerable.Range(0, 8).Select(i => new ParameterDef("p" + i, input, 0, null, false)).ToArray();
        a.True(abi.Classify(shared, out var problem) is null && problem!.Contains("返回缓冲区"), "不能把栈返回缓冲区误放在 x8");
        method.Parameters = Enumerable.Range(0, 9).Select(i => new ParameterDef("p" + i, input, 0, null, false)).ToArray();
        a.True(abi.Classify(shared, out problem) is null && problem!.Contains("参数"), "不猜测尚未实现的共享栈入参");
        method.Parameters = [new("value", input, 0, null, false)];
        foreach (var name in new[] { "__Il2CppFullySharedGenericType", "__Il2CppFullySharedGenericStructType" })
        {
            var marker = new TypeDef { Index = 2, Assembly = "Shared.Tests.dll", Namespace = "Unity.IL2CPP.Metadata", Name = name,
                Token = 0, Attributes = TypeAttributes.Public, IsValueType = name.EndsWith("StructType"), IsEnum = false };
            var type = new DefinitionRef(marker, []);
            signature = abi.Classify(new(method, [], [type, type]), out _)!;
            a.True(signature.Parameters[0].Passing == Passing.Shared && signature.Return!.Pieces[0].Register == Storage.Gpr(1)
                && signature.MethodInfo!.Register == Storage.Gpr(2), "元数据占位类型与开放共享见证的位置一致：" + name);
        }
        return a.Finish("shared-signature");
    }
}
