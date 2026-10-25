using Cpp2CS.Model;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>手写 CIL 区间与预期，不调用 L3/L4 或原生 LSDA；依据 ECMA-335 I.12.4.2。</summary>
internal static class CilExceptionCheck
{
    [Command("eh-cil", "独立 CIL catch/fault/leave/rethrow 区间语义", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        using var module = ModuleDefinition.CreateModule("EhSemantics", ModuleKind.Dll);
        var method = new MethodDefinition("Test", MethodAttributes.Static, module.TypeSystem.Void);
        method.Body = new MethodBody(method);
        var instructions = Enumerable.Range(0, 24).Select(_ => Instruction.Create(OpCodes.Nop)).ToArray();
        foreach (var instruction in instructions) method.Body.Instructions.Add(instruction);
        ExceptionHandler Handler(ExceptionHandlerType kind, int start, int end, int handler, int limit)
        {
            var result = new ExceptionHandler(kind)
            {
                TryStart = instructions[start], TryEnd = instructions[end], HandlerStart = instructions[handler], HandlerEnd = instructions[limit],
                CatchType = kind == ExceptionHandlerType.Catch ? module.TypeSystem.Object : null,
            };
            method.Body.ExceptionHandlers.Add(result); return result;
        }
        var outer = Handler(ExceptionHandlerType.Catch, 0, 18, 18, 22);
        var fault = Handler(ExceptionHandlerType.Fault, 1, 10, 10, 14);
        var inner = Handler(ExceptionHandlerType.Catch, 2, 5, 5, 9);
        var exception = new CilThrow(new PrimitiveRef("Object"), 0x1234);
        var flow = new CilExceptionFlow(method.Body);
        var direct = flow.Throw(3, exception, _ => true);
        a.True(direct is { Pc: 5, Object: 0x1234 }, "最内层 catch，入口栈只有同一异常对象");
        a.True(ReferenceEquals(exception, flow.Rethrow(6)), "rethrow 保留对象而非创建新异常");
        var raised = flow.Throw(6, flow.Rethrow(6), _ => true);
        a.True(raised is { Pc: 10, Object: null }, "重抛先运行外层 fault，入口栈为空");
        var afterFault = flow.EndFault(11, out var pending);
        a.True(afterFault is { Pc: 18, Object: 0x1234 } && ReferenceEquals(exception, pending), "fault 完成后进入外层 catch");
        flow.Leave(23);
        bool Reject(Action action) { try { action(); return false; } catch (InvalidProgramException) { return true; } }
        a.True(Reject(() => flow.Rethrow(19)), "leave 后当前 catch 失效");
        a.True(Reject(() => flow.Rethrow(23)), "区域外不允许 rethrow");
        flow = new CilExceptionFlow(method.Body);
        a.True(flow.Throw(3, exception, h => h == outer) is { Pc: 10 }, "类型筛选失败向外查找并执行 fault");
        a.True(flow.EndFault(11, out _) is { Pc: 18 }, "不匹配的内层 catch 不截断传播");
        flow = new CilExceptionFlow(method.Body);
        a.True(flow.Throw(3, exception, _ => false) is { Pc: 10 }, "没有匹配 catch 时仍执行 fault");
        a.True(flow.EndFault(11, out pending) is null && ReferenceEquals(exception, pending), "最外 fault 完成后抛出离开，身份不变");
        flow = new CilExceptionFlow(method.Body);
        flow.Leave(23);
        a.True(Reject(() => flow.EndFault(11, out _)), "正常 leave 不进入 fault");
        a.True(flow.Throw(23, exception, _ => true) is null, "区域之外抛出直接离开");
        a.True(flow.Throw(5, exception, _ => true) is { Pc: 10 }, "try 右边界不命中自身 catch");

        // catch 内有嵌套 catch：离开内层仍可重抛外层保存的异常。
        method.Body.ExceptionHandlers.Clear();
        outer = Handler(ExceptionHandlerType.Catch, 0, 2, 2, 22);
        inner = Handler(ExceptionHandlerType.Catch, 3, 6, 6, 9);
        flow = new CilExceptionFlow(method.Body);
        _ = flow.Throw(1, exception, _ => true);
        var nested = new CilThrow(exception.Type, 0x5678);
        _ = flow.Throw(4, nested, _ => true);
        a.True(ReferenceEquals(nested, flow.Rethrow(7)), "嵌套 catch 重抛内层异常");
        flow.Leave(12);
        a.True(ReferenceEquals(exception, flow.Rethrow(12)), "离开内层 catch 后保留外层异常");

        method.Body.ExceptionHandlers.Clear();
        outer = Handler(ExceptionHandlerType.Catch, 0, 18, 18, 22);
        fault = Handler(ExceptionHandlerType.Fault, 0, 4, 4, 18);
        inner = Handler(ExceptionHandlerType.Catch, 5, 8, 8, 11);
        flow = new CilExceptionFlow(method.Body);
        _ = flow.Throw(2, exception, _ => true);
        a.True(flow.Throw(6, nested, _ => true) is { Pc: 8, Object: 0x5678 }, "fault 内新异常由内层 catch 捕获");
        flow.Leave(12);
        a.True(flow.EndFault(14, out pending) is { Pc: 18, Object: 0x1234 } && ReferenceEquals(exception, pending), "内层 catch 完成后恢复旧展开");
        flow = new CilExceptionFlow(method.Body);
        _ = flow.Throw(2, exception, _ => true);
        a.True(flow.Throw(6, nested, h => h == outer) is { Pc: 18, Object: 0x5678 }, "类型不匹配使新异常离开 fault");
        a.True(Reject(() => flow.EndFault(14, out _)), "离开 fault 的新异常废弃旧展开");
        flow = new CilExceptionFlow(method.Body);
        _ = flow.Throw(2, exception, _ => true);
        a.True(flow.Throw(6, nested, _ => false) is null, "fault 内新异常无人捕获时离开方法");
        a.True(Reject(() => flow.EndFault(14, out _)), "逃逸的新异常不留下旧 fault 状态");
        return a.Finish("eh-cil");
    }
}
