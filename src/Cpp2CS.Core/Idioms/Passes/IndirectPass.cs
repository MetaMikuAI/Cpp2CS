using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class IndirectPass
{
    internal static Call? Indirect(this IdiomState state, Call call)
    {
        var target = state.defs.Expand(call.Target);
        if (target is not Load { Width: 64 } load)
            return null;
        var expanded = call.Arguments.Select(a => state.defs.Expand(a)).ToArray();
        var terms = TermsPass.Terms(load.Address);
        var constant = terms.OfType<Const>().Aggregate(0UL, (sum, c) => sum + c.Value);
        var rest = terms.Where(t => t is not Const).ToList();
        RuntimeOp? op = null;
        Template template = default;
        // vtable：target = klass->vtable[n].methodPtr，klass = *obj，obj 为第一个参数，klass->vtable[n].method 作为参数传入
        // MethodInfo* 参数可能未设置（被调用者不读它时编译器省略），所以只要求 this 与 vtable 槽位的形态
        if (rest is [Load { Width: 64 } klass] && constant >= RuntimeLayout.ClassVtable && (constant - RuntimeLayout.ClassVtable) % RuntimeLayout.VirtualInvokeDataSize == 0 && expanded.Length > 0 && expanded[0] == klass.Address)
        {
            op = new RuntimeOp(OpKind.CallVirtual, (int)((constant - RuntimeLayout.ClassVtable) / RuntimeLayout.VirtualInvokeDataSize));
            template = Template.VirtualCall;
        }
        // 接口：target = data->methodPtr，data 为 InterfaceInvokeData 的结果，data->method 作为参数传入
        else if (rest is [Use { Variable: var data }] && constant == 0 && state.interfaceData.TryGetValue(data, out var operand))
        {
            op = new RuntimeOp(OpKind.CallInterface, operand);
            template = Template.InterfaceCall;
        }
        else if (rest is [Use { Variable: var resolvedMethod }] && constant == RuntimeLayout.MethodVirtualPointer && state.genericVirtual.TryGetValue(resolvedMethod, out var gvm))
        {
            op = new RuntimeOp(OpKind.CallGenericVirtual, gvm);
            template = Template.GenericVirtualCall;
        }
        else if (rest.Count == 1 && constant == RuntimeLayout.DelegateInvokeImpl)
        {
            op = new RuntimeOp(OpKind.CallDelegate, null);
            template = Template.DelegateCall;
        }
        // MethodInfo.methodPointer：target = method->methodPointer，method 本身作为参数传入
        else if (constant == RuntimeLayout.MethodPointer && rest.Count == 1 && expanded.Contains(rest[0]))
        {
            op = new RuntimeOp(OpKind.CallMethodPointer, rest[0] is Symbol { Kind: SymbolKind.Method } m ? m.Value : null);
            template = Template.MethodPointerCall;
        }

        if (op is null)
            return null;
        state.Result.Hit(template);
        return call with
        {
            Op = op
        };
    }
}
