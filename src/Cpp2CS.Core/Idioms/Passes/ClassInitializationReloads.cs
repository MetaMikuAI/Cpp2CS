using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>类构造守卫中的字段重读：跳过初始化时已有相同快照，统一保留初始化后的读取。</summary>
internal static class ClassInitializationReloads
{
    internal static bool Run(MachineFunction function, Func<Expr, TypeRef?>? typeOf = null)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        var phis = function.Blocks.SelectMany(b => b.Statements).OfType<Phi>().ToArray();
        var uses = function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Use>().ToLookup(u => u.Variable);
        int ObservedWidth(Variable variable, HashSet<Variable> seen)
        {
            if (!seen.Add(variable)) return 0;
            return Math.Max(uses[variable].Select(u => u.Width).DefaultIfEmpty(0).Max(),
                phis.Where(p => p.Sources.Contains(variable)).Select(p => ObservedWidth(p.Target, seen)).DefaultIfEmpty(0).Max());
        }
        Expr Expand(Expr value, int depth = 0) => depth >= 32 ? value : ExprMap.Map(value,
            e => e is Use u && definitions.TryGetValue(u.Variable, out var source) ? Expand(source, depth + 1) : null);
        Expr Strip(Expr value)
        {
            value = Expand(value);
            while (value is Ir.Convert c) value = c.Operand;
            return value;
        }
        bool Preserves(Store store, Expr value)
        {
            // 托管对象引用只能指向对象起点；不同偏移的字段不重叠，嵌套读取的每一级也须保留。
            if (Expand(store.Target) is not Binary { Op: BinOp.Add, Left: var written, Right: Const { Value: >= RuntimeLayout.ObjectHeaderSize } displacement }
                || typeOf?.Invoke(written) is not { } writeType || !ManagedTypes.IsReferenceType(writeType)) return false;
            var reads = ExprMap.Walk(value).OfType<Load>().ToArray();
            return reads.Length > 0 && reads.All(load => load.Address is Binary
                { Op: BinOp.Add, Left: var read, Right: Const { Value: >= RuntimeLayout.ObjectHeaderSize } position }
                && typeOf(read) is { } readType && ManagedTypes.IsReferenceType(readType)
                && (position.Value + (ulong)load.Width / 8 <= displacement.Value
                    || displacement.Value + (ulong)store.Value.Width / 8 <= position.Value));
        }
        foreach (var head in function.Blocks)
        {
            if (head.Statements.LastOrDefault() is not Branch branch || head.NormalSuccessors.Count() != 2
                || Expand(branch.Condition) is not Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 } } test
                || Strip(test.Left) is not Load
                {
                    Width: 32, Address: Binary
                    {
                        Op: BinOp.Add,
                        Left: Symbol { Kind: SymbolKind.Class, Value: DefinitionRef type }, Right: Const { Value: RuntimeLayout.ClassCctorFinishedOrNoCctor }
                    }
                }) continue;
            var enterAddress = test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough;
            var enter = head.NormalSuccessors.Single(b => b.Start == enterAddress);
            var fastStart = head.NormalSuccessors.Single(b => b != enter);
            var merge = fastStart;
            var fastPrevious = head;
            var fastChain = new HashSet<Block>();
            // 快路径可在汇合前完成纯计算；加载仍由已有快照证明，不允许额外调用或写入。
            while (fastChain.Count < 32 && merge.Predecessors.Count == 1 && !merge.IsLandingPad
                && merge.Handler == head.Handler && merge.NormalSuccessors.ToArray() is [var fastNext]
                && merge.Statements.All(s => s is Nop or Jump || s is Define d
                    && !ExprMap.Walk(d.Value).Any(e => e is Load or Intrinsic or Unknown)) && fastChain.Add(merge))
            {
                fastPrevious = merge;
                merge = fastNext;
            }
            var chain = new List<Block>();
            var previous = head;
            var current = enter;
            while (current != merge && chain.Count < 32 && !chain.Contains(current) && current.Predecessors.Contains(previous)
                && !current.IsLandingPad && current.NormalSuccessors.Count() == 1 && current.Statements.LastOrDefault() is not Branch)
            {
                chain.Add(current);
                previous = current;
                current = current.NormalSuccessors.Single();
            }
            if (current != merge || chain.Count == 0) continue;
            var shared = chain.Any(b => b.Predecessors.Count != 1);
            if (shared)
            {
                // 共用初始化尾部只传递已有值；强制经过该尾部不能改变最终合流值。
                var copies = new Dictionary<Variable, Expr>();
                Expr Value(Variable variable) => copies.GetValueOrDefault(variable) ?? new Use(variable, variable.Width);
                var validPath = true;
                previous = head;
                foreach (var block in chain)
                {
                    if (block.Handler != head.Handler) { validPath = false; break; }
                    var incoming = block.Predecessors.IndexOf(previous);
                    foreach (var statement in block.Statements)
                    {
                        if (statement is Phi phi && phi.Sources.Length == block.Predecessors.Count)
                            copies[phi.Target] = Value(phi.Sources[incoming]);
                        else if (statement is not (Nop or Jump or Call { Op.Kind: OpKind.RunClassConstructor }))
                        { validPath = false; break; }
                    }
                    previous = block;
                }
                var direct = merge.Predecessors.IndexOf(fastPrevious);
                var initializedPath = merge.Predecessors.IndexOf(chain[^1]);
                if (!validPath || direct < 0 || initializedPath < 0 || merge.Statements.OfType<Phi>().Any(p =>
                    p.Sources.Length != merge.Predecessors.Count || Value(p.Sources[direct]) != Value(p.Sources[initializedPath]))) continue;
            }
            Expr? PreviousSnapshot(Expr value, bool check)
            {
                value = Expand(value);
                var visited = new HashSet<Block>();
                var block = head;
                while (visited.Add(block))
                {
                    foreach (var statement in block.Statements.AsEnumerable().Reverse())
                    {
                        if (check && statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [var subject] } && Expand(subject) == value) return subject;
                        if (!check && statement is Define define && Strip(define.Value) == value) return new Use(define.Target, value.Width);
                        if (!check && value is Load load && statement is Store store && store.Value.Width == load.Width
                            && Expand(store.Target) == load.Address) return store.Value;
                        if (!check && value is Load part && part.Address is Binary { Op: BinOp.Add, Left: var readRoot, Right: Const readAt }
                            && statement is Store whole && Expand(whole.Target) is Binary { Op: BinOp.Add, Left: var writeRoot, Right: Const writeAt }
                            && readRoot == writeRoot && readAt.Value >= writeAt.Value
                            && readAt.Value - writeAt.Value + (ulong)part.Width / 8 <= (ulong)whole.Value.Width / 8)
                            return Fold.Extract(whole.Value, checked((int)(readAt.Value - writeAt.Value) * 8), part.Width);
                        if (statement is Store write && Preserves(write, value)) continue;
                        if (statement is not (Define or Phi or Nop or Jump or Branch or Call { Op.Kind: OpKind.NullCheck })) return null;
                    }
                    if (block.IsLandingPad || block.Predecessors.Count != 1) return null;
                    block = block.Predecessors[0];
                }
                return null;
            }
            var initialized = false;
            var valid = true;
            var snapshots = new Dictionary<Variable, Expr>();
            foreach (var statement in chain.SelectMany(b => b.Statements))
            {
                if (statement is Nop or Jump || shared && statement is Phi) continue;
                if (!initialized && statement is Call { Op: { Kind: OpKind.RunClassConstructor, Operand: DefinitionRef owner } }
                    && owner.Equals(type)) { initialized = true; continue; }
                if (statement is Define d && ExprMap.Walk(d.Value).All(e => e is Use or Const or Symbol or Binary or Unary or Ir.Convert
                    || initialized && e is Load load && PreviousSnapshot(load, false) is not null))
                {
                    snapshots[d.Target] = ExprMap.Map(d.Value, e => e is Load load ? PreviousSnapshot(load, false) : null);
                    continue;
                }
                if (initialized && statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [var value] } && PreviousSnapshot(value, true) is not null) continue;
                valid = false;
                break;
            }
            if (!valid || !initialized) continue;
            // 跳过类构造的路径也必须取得同一快照；不能仅凭曾读写过该字段就改变合流值。
            Expr Snapshot(Expr value, bool useSnapshots, int depth = 0) => depth >= 32 ? value : Fold.Simplify(ExprMap.Map(value, e =>
                e is Use use && (useSnapshots && snapshots.TryGetValue(use.Variable, out var source) || definitions.TryGetValue(use.Variable, out source))
                    ? Fold.Convert(ConvKind.Truncate, Snapshot(source, useSnapshots, depth + 1), use.Width) : null));
            var fast = merge.Predecessors.IndexOf(fastPrevious);
            var slow = merge.Predecessors.IndexOf(chain[^1]);
            if (!shared && (fast < 0 || slow < 0 || merge.Statements.OfType<Phi>().Any(p => p.Sources.Length != merge.Predecessors.Count
                || ObservedWidth(p.Target, []) is var observed && observed > 0
                    && Snapshot(new Use(p.Sources[fast], observed), false) != Snapshot(new Use(p.Sources[slow], observed), true)))) continue;
            head.Statements[^1] = new Jump(branch.Address, enter.Start);
            MachineFunction.RemoveEdge(head, fastStart);
            return true;
        }
        return false;
    }
}
