using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>invoker、方法指针和 MethodInfo 必须来自同一个已知方法。</summary>
internal static class GenericInvokerIdentity
{
    internal static MethodRef? Match(Expr target, Expr pointer, Expr info)
    {
        if (info is not Symbol { Kind: SymbolKind.Method, Value: MethodRef method }
            || pointer is not Load { Width: 64, Address: var pointerInfo } || pointerInfo != info
            || target is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Width: 64, Left: var targetInfo,
                Right: Const { Width: 64, Value: RuntimeLayout.MethodInvoker } } } || targetInfo != info) return null;
        return method;
    }
}
