using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<Variable, Expr> arrayCursors = new();
        private readonly Dictionary<Variable, Expr> arrayOffsets = new();

        private void PrepareArrayCursors()
        {
            bool changed;
            do
            {
                changed = false;
                foreach (var cursor in ArrayCursorRecognition.Read(function,
                    expression => TypeOfAddressBase(expression) is ArrayRef { IsVector: true } array ? types.Size(array.Element) : null))
                {
                    // 归纳根保留为真实 SSA 值，避免两个等步长游标相互展开。
                    if (ExprMap.Walk(cursor.Address).OfType<Use>().Any(u => arrayCursors.ContainsKey(u.Variable))) continue;
                    if (!arrayCursors.TryAdd(cursor.Pointer, cursor.Address)) continue;
                    runtime.Add(cursor.Pointer);
                    runtime.UnionWith(cursor.AddressCopies);
                    if (cursor.IsOffset)
                    {
                        arrayOffsets[cursor.Pointer] = Fold.Simplify(cursor.Address);
                        foreach (var copy in cursor.AddressCopies) arrayOffsets[copy] = values[copy];
                    }
                    changed = true;
                }
                foreach (var (variable, expression) in values)
                {
                    if (arrayCursors.ContainsKey(variable) || expression is not Binary { Op: BinOp.Add }
                        || ExprMap.Walk(expression).Any(e => e is not (Use or Const or Ir.Binary or Ir.Convert))
                        || ArrayLocation(expression) is null) continue;
                    // 只展开纯地址计算；数组引用的字段读取仍使用原 SSA 快照。
                    arrayCursors[variable] = expression;
                    runtime.Add(variable);
                    changed = true;
                }
                if (changed) InferTypes();
            } while (changed);
        }
    }
}
