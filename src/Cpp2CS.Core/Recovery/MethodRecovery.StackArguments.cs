using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<Store, LocalValue> stackArgumentStores = [];
        private readonly Dictionary<(ulong Site, int Parameter), ManagedValue> stackArgumentValues = [];
        private readonly Dictionary<ulong, (long Offset, int Size)> callStackAreas = [];

        /// <summary>按 AAPCS64 栈布局匹配到达写入，值在原写入位置快照；不把寄存器耗尽后的参数丢掉。</summary>
        [Analysis("标量栈实参", 29, After = ["帧前类型"])]
        private void PrepareScalarStackArguments()
        {
            var definitions = values.Concat(function.Dead.Select(d => new KeyValuePair<Variable, Expr>(d.Define.Target, d.Define.Value)))
                .GroupBy(p => p.Key).ToDictionary(g => g.Key, g => g.First().Value);
            Expr Definition(Expr expression, int depth = 12) => depth == 0 ? expression : ExprMap.Map(expression,
                e => e is Use use && definitions.TryGetValue(use.Variable, out var value) ? Definition(value, depth - 1) : null);
            long? Offset(Expr expression, HashSet<Variable> active) => expression switch
            {
                FrameAddress f => f.Offset,
                Binary { Op: BinOp.Add, Right: Const c } b when Offset(b.Left, active) is { } offset => offset + c.Signed,
                Binary { Op: BinOp.Sub, Right: Const c } b when Offset(b.Left, active) is { } offset => offset - c.Signed,
                Use u when active.Add(u.Variable) && definitions.TryGetValue(u.Variable, out var value) => Offset(value, active),
                _ => null,
            };
            var sp = owner.lifter.Machine.Convention.StackPointer;
            var writes = blocks.ToDictionary(b => b, b => b.Statements.OfType<Define>().Concat(function.Dead.Where(d => d.Block == b).Select(d => d.Define))
                .Where(d => d.Target.Storage == sp).DistinctBy(d => d.Target).OrderBy(d => d.Address).ToArray());
            var outputs = blocks.ToDictionary(b => b, _ => new HashSet<long?>());
            HashSet<long?> Input(Block block)
            {
                var input = block == function.EntryBlock ? new HashSet<long?> { 0 } : [];
                foreach (var parent in block.Predecessors.Where(outputs.ContainsKey)) input.UnionWith(outputs[parent]);
                return input;
            }
            bool changed;
            do
            {
                changed = false;
                foreach (var block in blocks)
                {
                    var state = writes[block].LastOrDefault() is { } last ? new HashSet<long?> { Offset(last.Value, []) } : Input(block);
                    if (!outputs[block].SetEquals(state)) { outputs[block] = state; changed = true; }
                }
            } while (changed);
            foreach (var block in blocks)
            foreach (var call in block.Statements.OfType<Call>())
            {
                if (Resolve(call) is not { } callee || owner.abi.Classify(callee, out _) is not { } signature) continue;
                var state = writes[block].LastOrDefault(d => d.Address < call.Address) is { } last
                    ? new HashSet<long?> { Offset(last.Value, []) } : Input(block);
                if (state.Count != 1 || state.Single() is not { } callSp) continue;
                var layout = owner.abi.StackArguments(signature);
                callStackAreas[call.Address] = (callSp, layout.Size);
                // 虚调用的隐藏 MethodInfo 与方法指针来自同一个 vtable 槽，寄存器耗尽时写入栈。
                if (call.Op?.Kind == OpKind.CallVirtual && layout.MethodInfoOffset is { } hidden
                    && ReachingStackStore(block, block.Statements.IndexOf(call), callSp + hidden, []) is { } metadata
                    && Definition(metadata.Value) is Load { Width: 64 } info && Definition(call.Target) is Load { Width: 64 } pointer
                    && Split(info.Address) is var infoAt && Split(pointer.Address) is var pointerAt
                    && infoAt.Base == pointerAt.Base && infoAt.Offset == pointerAt.Offset + 8)
                    dropped.Add(metadata);
                foreach (var parameter in layout.Parameters)
                {
                    if (!parameter.Indirect && types.Kind(parameter.Type) == TypeKind.Struct && owner.abi.Hfa(parameter.Type) is { } hfa)
                    {
                        var leaves = StructPaths(parameter.Type).Where(p => types.Kind(p.Type) is TypeKind.Float or TypeKind.Double).ToArray();
                        var stores = leaves.Select(p => ReachingStackStore(block, block.Statements.IndexOf(call),
                            callSp + parameter.Offset + p.Offset, [], hfa.Width)).ToArray();
                        if (leaves.Length != hfa.Count || stores.Any(s => s is null)
                            || leaves.Any(p => !ExclusiveStackArgument(callSp + parameter.Offset + p.Offset, hfa.Width))
                            || stores.Where((s, i) => stackArgumentStores.TryGetValue(s!, out var local) && !local.Type.Equals(leaves[i].Type)).Any()) continue;
                        var parts = leaves.Select((p, i) =>
                        {
                            if (!stackArgumentStores.TryGetValue(stores[i]!, out var local))
                                stackArgumentStores[stores[i]!] = local = StructLocal(p.Type, hfa.Width);
                            return ((IReadOnlyList<FieldRef>)p.Path, (ManagedValue)local);
                        }).ToArray();
                        stackArgumentValues[(call.Address, parameter.Index)] = new ComposedValue(parameter.Type, parts);
                        continue;
                    }
                    if (types.Kind(parameter.Type) is not (TypeKind.Float or TypeKind.Double or TypeKind.Int or TypeKind.Bool or TypeKind.Reference)) continue;
                    var width = types.Size(parameter.Type) * 8;
                    if (width is not (8 or 16 or 32 or 64)
                        || ReachingStackStore(block, block.Statements.IndexOf(call), callSp + parameter.Offset, [], width, allowWider: true) is not { } store) continue;
                    // AAPCS64 栈参数按 8 字节对齐；整槽清零可用 64 位写入，参数只读取低位。
                    if (!ExclusiveStackArgument(callSp + parameter.Offset, store.Value.Width)) continue;
                    if (!stackArgumentStores.TryGetValue(store, out var local))
                        stackArgumentStores[store] = local = StructLocal(parameter.Type, width);
                    if (!local.Type.Equals(parameter.Type)) continue;
                    stackArgumentValues[(call.Address, parameter.Index)] = local;
                }
            }
        }

        private bool ExclusiveStackArgument(long offset, int width)
        {
            bool Exposes(Expr expression)
            {
                if (expression is Load) return false;
                if (FrameOffset(expression) is { } at) return at >= offset && at < offset + width / 8;
                return ExprMap.Children(expression).Any(Exposes);
            }
            // 消费写入前排除普通加载及地址逃逸，避免同一槽既是实参又是可变局部时丢失内存副作用。
            foreach (var statement in blocks.SelectMany(b => b.Statements))
            {
                var values = ExprMap.Operands(statement);
                foreach (var load in values.SelectMany(ExprMap.Walk).OfType<Load>())
                    if (FrameOffset(load.Address) is { } at && at < offset + width / 8 && offset < at + load.Width / 8) return false;
                var exposed = statement is Store store ? new[] { store.Value } : values;
                if (statement is Define { Value: Load } || statement is Define { Value: Ir.Convert { Operand: Load } }) continue;
                if (exposed.Any(Exposes)) return false;
            }
            return true;
        }

        [StoreRule(1)]
        private RecoveryResult<bool> StoreStackArgument(Store store, List<ManagedStatement> output)
        {
            if (!stackArgumentStores.TryGetValue(store, out var local)) return false;
            if (!RecoverAs(store.Value, local.Type, store.Address).TryGet(out var value, out var failure)) return failure;
            output.Add(new ManagedAssignment(store.Address, local, value));
            return true;
        }

        [ArgumentRule(1)]
        private ManagedValue? ScalarStackArgument(AbiValue parameter, ArgumentSite site)
        {
            if (parameter.Passing != Passing.Stack) return null;
            return stackArgumentValues.GetValueOrDefault((site.Call.Address, site.Index));
        }
    }
}
