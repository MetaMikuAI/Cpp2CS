using System.Reflection;
using Cpp2CS.Calls;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class CallBindingStateCheck
{
    [Command("call-binding-state", "调用缓存随 IR 和类型版本失效，已提交身份独立保留", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 0, Assembly = "Calls.Tests.dll", Namespace = "Tests", Name = "Worker",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var definition = new MethodDef { Index = 0, Owner = owner, Name = "Run", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1 };
        var method = MethodRef.Open(definition);
        var call = new Call(0x100, CallKind.Direct, Expr.C(0x200, 64));
        var state = new CallBindingState();
        var a = new Assertions();
        state.Remember(call, method, 1);
        a.Equal(method, state.Cached(call, 1), "同版本复用");
        a.True(state.Cached(call, 2) is null, "IR 改写失效");
        state.InvalidateTypes();
        a.True(state.Cached(call, 1) is null, "类型变化失效");
        state.Commit(call, method);
        state.InvalidateTypes();
        a.Equal(method, state.Cached(call, 3), "已证明身份不受推断版本影响");
        state.Commit(call, method);
        var copy = call with { };
        a.True(state.Cached(copy, 3) is null, "值相同的 IR 节点不共享绑定");
        state.Copy(call, copy);
        a.Equal(method, state.Cached(copy, 3), "等价复制保留已提交身份");
        a.Equal(state.Resolution(call), state.Resolution(copy), "等价复制保留诊断来源");
        var replacement = call with { Address = 0x104 };
        state.Move(copy, replacement);
        a.True(state.Cached(copy, 3) is null, "替换后旧节点不再持有绑定");
        a.Equal(method, state.Cached(replacement, 3), "替换后身份迁移");
        a.True(new CallBindingState().Cached(call, 3) is null, "方法间状态隔离");
        return a.Finish("call-binding-state");
    }
}
