using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Ssa;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>
        /// 提升时间接调用的目标未知，按保守约定读取全部参数寄存器（x0–x8、v0–v7）。L2 认出接口调用之后，被调用者是接口槽位的某个实现，
        /// 它们与接口方法的托管签名相同，按 AAPCS64 只读取签名中的寄存器（含 MethodInfo 与 x8）。按签名裁去其余实参后再删除死值：
        /// 否则被调用破坏的寄存器经 φ 流进这些实参，连带让只为这些 φ 存在的值（例如 awaiter 的 128 位拷贝）无法恢复。
        /// 结果寄存器不裁剪（SSA 版本已经分配，后续读取保持原样）。
        /// </summary>
        private void TrimIndirectArguments()
        {
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call call || Callee(call) is not { } callee || owner.abi.Classify(callee, out _) is not { } signature) continue;
                    var reads = signature.Reads.ToHashSet();
                    var keep = Enumerable.Range(0, call.Sources.Length).Where(k => reads.Contains(call.Sources[k])).ToArray();
                    if (keep.Length == call.Sources.Length || keep.Length != reads.Count) continue;
                    block.Statements[i] = call with { Arguments = keep.Select(k => call.Arguments[k]).ToArray(), Sources = keep.Select(k => call.Sources[k]).ToArray() };
                    changed = true;
                }
            if (changed) Propagate.RemoveDead(function);
        }

        /// <summary>
        /// 签名已知的间接调用：接口调用按接口方法；虚调用（含尾调用 br）的接收者是入口参数时，按其声明类型虚表槽位上的方法
        /// （覆盖它的方法签名相同）。尾调用的保守约定还读 x8，常把类指针的读取留成活值。
        /// </summary>
        private MethodRef? Callee(Call call)
        {
            switch (call.Op)
            {
                case { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> { Item1: DefinitionRef itf } pair }:
                    return itf.Definition.Methods.FirstOrDefault(m => m.Slot == pair.Item2 && !m.IsStatic) is { } method ? new MethodRef(method, itf.Arguments, []) : null;
                case { Kind: OpKind.CallVirtual, Operand: int slot } when call.Arguments.FirstOrDefault() is Use { Variable: { Version: 0 } self }
                    && arguments.TryGetValue(self.Storage, out var argument) && argument.Type is DefinitionRef { Arguments.Count: 0, Definition: var type }
                    && slot < type.VTable.Count && type.VTable[slot] is { Method.Owner.GenericParameters.Count: 0 } entry:
                    return entry with { TypeArguments = [] };
                default:
                    return null;
            }
        }
    }
}
