using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class GenericInvokerIdentityCheck
{
    [Command("generic-invoker-identity", "泛型 invoker 三处身份与字段宽度边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 0, Assembly = "Tests.dll", Namespace = "Tests", Name = "Functions", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        MethodRef Method(int index) => new(new MethodDef { Index = index, Owner = owner, Name = "Read" + index, Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1 }, [], []);
        var method = Method(1);
        var info = new Symbol(SymbolKind.Method, method);
        var other = new Symbol(SymbolKind.Method, Method(2));
        Expr Invoker(Expr value, int offset = RuntimeLayout.MethodInvoker, int width = 64) =>
            new Load(new Binary(BinOp.Add, value, Expr.C((ulong)offset, 64), 64), width);
        var a = new Assertions();
        a.True(GenericInvokerIdentity.Match(Invoker(info), new Load(info, 64), info) == method, "同一 MethodInfo 的 invoker 与方法指针匹配");
        foreach (var (target, pointer, argument) in new (Expr, Expr, Expr)[]
        {
            (Invoker(other), new Load(info, 64), info), (Invoker(info), new Load(other, 64), info),
            (Invoker(info), new Load(info, 64), other), (Invoker(info, 8), new Load(info, 64), info),
            (Invoker(info, width: 32), new Load(info, 64), info), (Invoker(info), new Load(info, 32), info),
            (Invoker(info), info, info), (Invoker(info), new Load(info, 64), new Use(new(Storage.Gpr(1), 3), 64)),
            (Invoker(new Symbol(SymbolKind.Class, method)), new Load(info, 64), info),
        }) a.True(GenericInvokerIdentity.Match(target, pointer, argument) is null, "混用方法、偏移、窄加载及未展开身份保留未恢复诊断");
        return a.Finish("generic-invoker-identity");
    }
}
