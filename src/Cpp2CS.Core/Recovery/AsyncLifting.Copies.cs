using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public static partial class AsyncLifting
{
    private sealed partial class Lifter
    {
        private readonly HashSet<Variable> copiedAwaiters = [];

        // 同一值类型的全部字段按原路径连续复制时，认回整体复制，不跨越调用或分支。
        private void FoldTaskCopies()
        {
            foreach (var statements in blocks.Values)
            for (var i = 0; i < statements.Count; i++)
            {
                if (statements[i] is not ManagedStore { Target: var target, Value: var value } first
                    || StorageValue(target) is not FieldValue { Accessor: null } to
                    || StorageValue(value) is not FieldValue { Accessor: null } from
                    || !to.Field.Equals(from.Field)) continue;
                var destination = StorageValue(to.Receiver);
                var source = StorageValue(from.Receiver);
                if (destination is not FieldValue task || StorageValue(task.Receiver) is not LocalValue local
                    || !InlineTaskField(task, local.Variable) || source is not LocalValue
                    || !source.Type.Equals(destination.Type) || source.Type is not DefinitionRef type) continue;
                var fields = type.Definition.Fields.Where(f => !f.IsStatic).ToArray();
                var run = statements.Skip(i).Take(fields.Length).OfType<ManagedStore>().ToArray();
                if (run.Length != fields.Length || run.Any(s => StorageValue(s.Target) is not FieldValue { Accessor: null } t
                    || StorageValue(s.Value) is not FieldValue { Accessor: null } f || !t.Field.Equals(f.Field)
                    || !StorageValue(t.Receiver).Equals(destination) || !StorageValue(f.Receiver).Equals(source))) continue;
                var written = run.Select(s => ((FieldValue)StorageValue(s.Target)).Field.Field).ToArray();
                if (written.Distinct().Count() != fields.Length || !fields.All(written.Contains)) continue;
                statements[i] = new ManagedStore(first.Address, destination, source);
                statements.RemoveRange(i + 1, fields.Length - 1);
            }
        }

        private Func<ManagedValue, ManagedStatement, ManagedValue?> CopiedTask()
        {
            var statements = blocks.Values.SelectMany(s => s).ToArray();
            var definitions = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable)
                .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
            var factories = statements.OfType<ManagedStore>().Where(s => StorageValue(s.Target) is FieldValue f
                    && StorageValue(f.Receiver) is LocalValue l && InlineTaskField(f, l.Variable))
                .GroupBy(s => ((LocalValue)StorageValue(((FieldValue)StorageValue(s.Target)).Receiver)).Variable)
                .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
            var positions = blocks.SelectMany(b => b.Value.Select((s, i) => (Statement: s, Block: b.Key, Index: i)))
                .ToDictionary(p => p.Statement, (IEqualityComparer<ManagedStatement>)ReferenceEqualityComparer.Instance);
            var predecessors = Predecessors();
            bool Before(ManagedStatement first, ManagedStatement last)
            {
                var origin = positions[first]; var target = positions[last];
                if (origin.Block == target.Block) return origin.Index < target.Index;
                var seen = new HashSet<ulong>(); var at = target.Block;
                while (seen.Add(at) && predecessors[at] is [var previous])
                { if (previous == origin.Block) return true; at = previous; }
                return false;
            }
            bool Immutable(LocalValue source) => statements.Count(s => s is ManagedAssignment a && a.Target.Variable == source.Variable
                    || s is ManagedCall { Result: { } r } && r.Variable == source.Variable) == 1
                && !statements.Any(s => s is ManagedStore store && ManagedValues.Walk(store.Target).OfType<LocalValue>().Any(l => l.Variable == source.Variable)
                    || s is ManagedCall call && new[] { call.Invocation.Receiver }.Concat(call.Invocation.Arguments)
                        .OfType<AddressValue>().SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => l.Variable == source.Variable));
            ManagedValue? Resolve(ManagedValue value, ManagedStatement use)
            {
                var seen = new HashSet<Variable>();
                var helpers = new List<Variable>();
                while (StorageValue(value) is LocalValue local && seen.Add(local.Variable))
                {
                    if (definitions.TryGetValue(local.Variable, out var definition) && Before(definition, use))
                    { helpers.Add(local.Variable); value = definition.Value; use = definition; continue; }
                    if (factories.TryGetValue(local.Variable, out var factory) && Before(factory, use)
                        && factory.Value is LocalValue source && Immutable(source))
                    {
                        copiedAwaiters.Add(local.Variable);
                        inlineReads.UnionWith(helpers);
                        return source;
                    }
                    break;
                }
                return null;
            }
            return Resolve;
        }

        private void RemoveCopiedAwaiters()
        {
            foreach (var variable in copiedAwaiters)
            {
                bool Construction(ManagedStatement s) => s is ManagedStore store && (InlineTaskField(store.Target, variable)
                    || StorageValue(store.Target) is LocalValue l && l.Variable == variable && store.Value is ComposedValue { Leaves.Count: 0 });
                if (blocks.Values.SelectMany(s => s).Where(s => !Construction(s)).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                    .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => l.Variable == variable)) continue;
                foreach (var statements in blocks.Values) statements.RemoveAll(s => Construction(s));
            }
        }
    }
}
