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
        private void TrimIndirectArguments(bool typed = false)
        {
            var changed = false;
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call call) continue;
                    // 托管写入自带 GC 屏障；通知调用的地址实参不应保活原生地址计算及其 φ。
                    if (IsWriteBarrier(call) && call.Arguments.Length > 0)
                    {
                        block.Statements[i] = Trimmed(call, [], []);
                        changed = true;
                        continue;
                    }
                    if ((typed ? Resolve(call) : Callee(call)) is not { } callee || owner.abi.Classify(callee, out _) is not { } signature) continue;
                    var reads = signature.Reads.ToHashSet();
                    var keep = Enumerable.Range(0, call.Sources.Length).Where(k => reads.Contains(call.Sources[k])).ToArray();
                    if (keep.Length == call.Sources.Length || keep.Length != reads.Count) continue;
                    block.Statements[i] = Trimmed(call, keep.Select(k => call.Arguments[k]).ToArray(), keep.Select(k => call.Sources[k]).ToArray());
                    changed = true;
                }
            if (!changed) return;
            RemoveDeadDefinitions();
            if (typed) definitions = IndexDefinitions();

            Call Trimmed(Call call, Expr[] arguments, Storage[] sources)
            {
                var replacement = call with { Arguments = arguments, Sources = sources };
                if (!typed) return replacement;
                // 裁去未读取的实参不改变调用身份；保留已建立的返回局部、构造配对与异常证据。
                Copy(typeChecks); Copy(constructed); Copy(forwardedConstructors); Copy(boxed); Copy(resolved);
                Copy(structResults); Copy(delegateCreations); Copy(exceptionTypeTargets); Copy(stackEnums); Copy(virtualDelegates);
                Copy(frameCopies); Copy(frameInitializers);
                Keep(dropped); Keep(virtualCalls); Keep(cleanupCalls); Keep(genericResolvers); Keep(stackEnumStorage);
                foreach (var live in frameLives.Values) Keep(live);
                ledger.Replace(call, replacement);
                return replacement;

                void Copy<TKey, TValue>(Dictionary<TKey, TValue> map) where TKey : Stmt
                {
                    if (call is TKey key && replacement is TKey next && map.TryGetValue(key, out var value)) map[next] = value;
                }
                void Keep<T>(HashSet<T> set) where T : Stmt
                {
                    if (call is T key && replacement is T next && set.Contains(key)) set.Add(next);
                }
            }
        }

        private bool IsWriteBarrier(Call call) => call.Op?.Kind == OpKind.WriteBarrier
            || call.Op is null && call.Target is Const helper && facts.Helpers.At(helper.Value) is { Kind: HelperKind.WriteBarrier }
                && facts.Code.RegionOf(helper.Value) != CodeRegion.Managed;

        /// <summary>
        /// 签名已知的间接调用：接口调用按接口方法；虚调用（含尾调用 br）的接收者是入口参数或已知分配结果时，按其类型虚表槽位上的方法
        /// （覆盖它的方法签名相同）。尾调用的保守约定还读 x8，常把类指针的读取留成活值。
        /// </summary>
        private MethodRef? Callee(Call call)
        {
            switch (call.Op)
            {
                case { Kind: OpKind.CallMethodPointer or OpKind.CallDelegate, Operand: MethodRef pointerMethod }:
                    return pointerMethod;
                case { Kind: OpKind.CallGenericVirtual, Operand: MethodRef generic } when generic.Method.IsVirtual:
                    return generic;
                case { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> { Item1: DefinitionRef itf } pair }:
                    return itf.Definition.Methods.FirstOrDefault(m => m.Slot == pair.Item2 && !m.IsStatic) is { } method ? new MethodRef(method, itf.Arguments, []) : null;
                case { Kind: OpKind.CallVirtual, Operand: int slot } when call.Arguments.FirstOrDefault() is Use { Variable: var self }:
                    var receiver = self.Version == 0 && arguments.TryGetValue(self.Storage, out var argument) ? argument.Type
                        : function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
                            .FirstOrDefault(c => c.Op?.Kind == OpKind.NewObject && c.Defines.FirstOrDefault() == self)?.Op?.Operand as TypeRef;
                    return receiver is DefinitionRef { Arguments.Count: 0, Definition: var type }
                        && slot < type.VTable.Count && type.VTable[slot] is { Method.Owner.GenericParameters.Count: 0 } entry
                        ? entry with { TypeArguments = [] } : null;
                default:
                    return null;
            }
        }
    }
}
