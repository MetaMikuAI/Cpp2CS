using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Memory;

/// <summary>
/// IL2CPP 的栈上临时装箱：对值类型调用其基类（Object、ValueType、Enum）上的实例方法时，codegen 不在堆上分配，
/// 而在栈帧上依次写入类指针、monitor（-1，标记栈上临时对象）与值，以对象地址作为接收者调用，对象只在这次调用期间存在。
/// 类指针、monitor 与值共同证明这是一次装箱；被调方法是引用类型上的实例方法，装箱对象可赋给其声明类型
/// （装箱转换的结果是值类型基类链上的实例，ECMA-335 I.8.2.4）。成立时接收者换成对值的 box。
/// </summary>
internal static class StackBoxing
{
    public static int Run(MachineFunction function, ValueModel values, TypeOracle oracle)
    {
        var count = 0;
        var nextTemp = function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
            { Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines.OfType<Variable>(), _ => [] })
            .Concat(function.Dead.Select(d => d.Define.Target)).Where(v => v.Storage.Bank == Bank.Temp)
            .Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call || oracle.Callee(call) is not { Method.IsStatic: false } callee
                    || !ManagedTypes.IsReferenceType(callee.DeclaringType)) continue;
                var position = call.ArgumentIndex(Storage.Gpr(0));
                var operands = values.Operands(call);
                if (position < 0 || position + 1 >= operands.Count || SymTable.Resolve(operands[position + 1]) is not LocalSym { Space.Kind: LocalKind.Frame } receiver) continue;
                var writes = new List<(Store Store, long Offset, int Width, Sym Value)>();
                for (var j = i - 1; j >= 0; j--)
                {
                    if (block.Statements[j] is Call) break;
                    if (block.Statements[j] is not Store store) continue;
                    var data = values.Operands(store);
                    if (oracle.Decompose(data[0]) is (LocalSym { Space.Kind: LocalKind.Frame } local, var offset, null, _))
                        writes.Add((store, local.Offset + offset - receiver.Offset, store.Value.Width, data[1]));
                }
                Sym? At(int offset, int width)
                {
                    foreach (var write in writes)
                        if (write.Offset < offset + width / 8 && offset < write.Offset + write.Width / 8)
                            return write.Offset <= offset && offset * 8 + width <= write.Offset * 8 + write.Width
                                ? SymTable.Resolve(values.Syms.Slice(write.Value, (int)(offset - write.Offset) * 8, width)) : null;
                    return null;
                }
                if (At(RuntimeLayout.ObjectKlass, 64) is not EntitySym { Symbol: { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsValueType: true } type } }
                    || type.Definition.BaseType?.Substitute(type.Arguments, []) is not { } boxed || !oracle.Types.IsAssignable(boxed, callee.DeclaringType)
                    || At(RuntimeLayout.ObjectMonitor, 64) is not ConstSym { Value: ulong.MaxValue }
                    || oracle.Types.Size(type) <= 0
                    || At(RuntimeLayout.ObjectHeaderSize, oracle.Types.Size(type) * 8) is null) continue;
                var temporary = new Variable(Storage.Temp(nextTemp++), 1);
                var box = new Call(call.Address, CallKind.Direct, Expr.C(0, 64))
                {
                    Op = new RuntimeOp(OpKind.Box, type),
                    Arguments = [new Symbol(SymbolKind.Class, type), new FrameAddress(receiver.Offset + RuntimeLayout.ObjectHeaderSize)],
                    Results = [temporary.Storage], Defines = [temporary],
                };
                var arguments = call.Arguments.ToArray();
                arguments[position] = new Use(temporary, 64);
                block.Statements[i] = call with { Arguments = arguments };
                block.Statements.Insert(i++, box);
                count++;
            }
        return count;
    }
}
