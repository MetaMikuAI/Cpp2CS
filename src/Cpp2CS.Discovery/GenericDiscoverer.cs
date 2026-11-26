using System.Collections.Immutable;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Discovery;

/// <summary>
/// 通用发现器（设计 9.6）：由目录驱动，从每个效果出发，找主效果与它相符的目录项，由主效果的操作数定出模板的形参；
/// 模板里的检查按操作数在效果图的条件抛出里取候选。它只提出声明，可以多提、错提：同一处效果会给出占用不同的几条，
/// 由证明与选择取舍。这里的类型只是找候选的线索，不是结论。
/// </summary>
public sealed class GenericDiscoverer : IDiscoverer
{
    public string Name => "generic";

    public IEnumerable<Claim> Propose(FactView facts)
    {
        var graph = facts.Effects;
        if (graph.Failure is not null) yield break;
        var terms = graph.Snapshot.Terms;
        var types = new Dictionary<Term, TypeShape>(ReferenceEqualityComparer.Instance);
        foreach (var (value, type, _) in graph.Arguments) types[value] = type;
        int pointerBits = facts.Layout.PointerBits;

        Term OnStack(Term stored, TypeShape type) =>
            type.Kind != StackKind.Int32 || stored.Width >= 32 ? stored
            : type.Signed && !type.TwoValued ? terms.SignExtend(stored, 32) : terms.ZeroExtend(stored, 32);
        // 存进较窄位置的值在栈上的写法：低位相同的 32 位值。
        Term Widen(Term stored) =>
            stored.Width >= 32 ? stored
            : stored is { Kind: TermKind.Slice, Offset: 0 } slice && slice.Operands[0].Width >= 32 ? terms.Slice(slice.Operands[0], 0, 32)
            : terms.ZeroExtend(stored, 32);

        // 在此处已经成立、由某个条件抛出确立的条件：取支配这个块的检查。
        IEnumerable<ConditionalThrow> ChecksBefore(BlockId block, ExceptionKind kind) =>
            graph.Checks.Where(c => c.Exception == kind && c.Edge.Source != block && graph.Shape.Dominates(c.Edge.Source, block));
        EffectRef? NullCheck(BlockId block, Term value)
        {
            var isNull = terms.Eq(value, terms.Zero(value.Width));
            foreach (var check in ChecksBefore(block, ExceptionKind.NullReference))
                if (ReferenceEquals(check.Condition, isNull) && check.Polarity) return EffectRef.Of(check.Edge);
            return null;
        }
        // 占用的各种取法：必有的效果，加上可选效果的每个子集（同一个检查可能已被另一次访问占用）。
        static IEnumerable<List<EffectRef>> Variants(EffectRef main, params EffectRef?[] optional)
        {
            var present = optional.Where(o => o is not null).Select(o => o!.Value).Distinct().ToList();
            for (int mask = (1 << present.Count) - 1; mask >= 0; mask--)
            {
                var occupied = new List<EffectRef> { main };
                for (int i = 0; i < present.Count; i++)
                    if ((mask & (1 << i)) != 0) occupied.Add(present[i]);
                yield return occupied;
            }
        }

        foreach (var effect in graph.Effects)
        {
            var id = effect.Occurrence;
            var after = new ProgramPoint(id.Block, id.Index + 1);
            var main = EffectRef.Of(id);
            switch (effect.Kind)
            {
                case NativeEffectKind.Read or NativeEffectKind.Write:
                {
                    var address = effect.Address!;
                    bool write = effect.Kind == NativeEffectKind.Write;
                    // 实例字段：已知类型的对象加常量偏移。
                    var (root, offset) = address is { Kind: TermKind.Operation, Op: Op.Add } sum && sum.Operands[1].IsConstant
                        ? (sum.Operands[0], unchecked((long)(ulong)sum.Operands[1].Value)) : (address, 0L);
                    if (types.TryGetValue(root, out var owner) && owner.Kind == StackKind.Object
                        && facts.Metadata.FieldAt(owner.Entity, (int)offset) is { IsStatic: false } field && field.Type.StorageBits == effect.Width
                        && field.Type.Kind != StackKind.Value)
                    {
                        var check = NullCheck(id.Block, root);
                        if (write)
                            foreach (var occupied in Variants(main, check))
                                yield return new Claim("stfld.object", field.Entity, [root, Widen(effect.Value!)], after, occupied, null);
                        else
                        {
                            var definition = OnStack(effect.Value!, field.Type);
                            types[definition] = ClaimTemplate_OnStack(field.Type);
                            foreach (var occupied in Variants(main, check))
                                yield return new Claim("ldfld.object", field.Entity, [root], after, occupied, definition);
                        }
                    }
                    // 数组元素：地址里出现的已知是数组的对象，配上地址里出现的 32 位下标。
                    foreach (var array in Leaves(address).Where(t => types.TryGetValue(t, out var type) && type.Kind == StackKind.Object
                        && facts.Metadata.ElementOf(type.Entity) is { Kind: StackKind.Int32, StorageBits: 32 }))
                    {
                        if (effect.Width != 32) continue;
                        foreach (var index in Indices(address))
                        {
                            var isNull = NullCheck(id.Block, array);
                            EffectRef? bounds = null, length = null;
                            foreach (var check in ChecksBefore(id.Block, ExceptionKind.IndexOutOfRange))
                            {
                                var (condition, polarity) = (check.Condition, check.Polarity);
                                while (condition is { Kind: TermKind.Operation, Op: Op.Not }) (condition, polarity) = (condition.Operands[0], !polarity);
                                if (polarity || condition is not { Kind: TermKind.Operation, Op: Op.Ult } || !ReferenceEquals(condition.Operands[0], index)) continue;
                                bounds = EffectRef.Of(check.Edge);
                                // 检查用到的长度若是一次读取的结果，那次读取属于这个检查。
                                foreach (var leaf in Leaves(condition.Operands[1]))
                                    if (leaf.Kind == TermKind.Result && graph.Effect(leaf.Occurrence) is { Kind: NativeEffectKind.Read }) length = EffectRef.Of(leaf.Occurrence);
                            }
                            foreach (var occupied in Variants(main, isNull, bounds, length))
                                yield return write
                                    ? new Claim("stelem.i4", null, [array, index, effect.Value!], after, occupied, null)
                                    : new Claim("ldelem.i4", null, [array, index], after, occupied, effect.Value!);
                        }
                    }
                    break;
                }
                case NativeEffectKind.Call:
                {
                    var callee = effect.Callee!;
                    string? operation = callee.Dispatch switch
                    {
                        VariantCondition.StaticMethod => callee.HasInitializer ? "call.static.init" : "call.static",
                        VariantCondition.UniqueTarget => "callvirt.unique",
                        _ => null,
                    };
                    if (operation is null) break;
                    if (effect.Result is { } result && callee.Return is { } returned) types[result] = ClaimTemplate_OnStack(returned);
                    var check = callee.HasThis ? NullCheck(id.Block, effect.Arguments[0]) : null;
                    foreach (var occupied in Variants(main, check))
                        yield return new Claim(operation, callee.Entity, effect.Arguments, after, occupied, effect.Result);
                    break;
                }
            }
        }

        // 整数的除与余：主效果是除零的条件抛出；被除数取自效果图里以它的除数作除法的项。
        foreach (var check in graph.Checks)
        {
            if (check.Exception != ExceptionKind.DivideByZero || !check.Polarity
                || check.Condition is not { Kind: TermKind.Operation, Op: Op.Eq } test || !test.Operands[1].IsZero) continue;
            var divisor = test.Operands[0];
            var terminator = graph.Snapshot.Terminator(check.Edge.Source);
            var passed = terminator.Exits[1 - check.Edge.Exit];
            if (passed.Kind != ExitKind.Target) continue;
            var landing = new ProgramPoint(passed.Target, 0);
            var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
            foreach (var root in Roots(graph))
                foreach (var chain in Chains(root, [], seen))
                {
                    var quotient = chain[^1];
                    if (quotient is not { Kind: TermKind.Operation, Op: Op.SDiv } || !ReferenceEquals(quotient.Operands[1], divisor)) continue;
                    // 定义的候选：商本身，以及包住它的同宽的项（除零时的取值、余数的写法都包在外面）。
                    for (int up = 0; up < 5 && up < chain.Count; up++)
                    {
                        var definition = chain[chain.Count - 1 - up];
                        if (definition.Width != quotient.Width) break;
                        foreach (string operation in (string[])["div.int", "rem.int"])
                            yield return new Claim(operation, null, [quotient.Operands[0], divisor], landing, [EffectRef.Of(check.Edge)], definition);
                    }
                }
        }
    }

    private static TypeShape ClaimTemplate_OnStack(TypeShape type) =>
        type.Kind == StackKind.Int32 && (type.StorageBits != 32 || type.TwoValued) ? new TypeShape(StackKind.Int32, 32, true, type.Entity) : type;

    /// <summary>项的叶子集合（设计 7.3：只用于找候选）。</summary>
    private static IEnumerable<Term> Leaves(Term term)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Term>();
        pending.Push(term);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (!seen.Add(current)) continue;
            if (current.Operands.Length == 0 || current.Kind == TermKind.Attribute) yield return current;
            foreach (var operand in current.Operands) pending.Push(operand);
        }
    }

    /// <summary>地址里可能是下标的 32 位项：被扩展到指针位宽的那些。</summary>
    private static IEnumerable<Term> Indices(Term address)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        var found = new List<Term>();
        void Go(Term t)
        {
            if (!seen.Add(t)) return;
            if (t is { Kind: TermKind.Operation, Op: Op.SignExtend } && t.Operands[0].Width == 32) found.Add(t.Operands[0]);
            else if (t.Kind == TermKind.Concat)
                foreach (var part in t.Operands)
                    if (part.Width == 32 && !part.IsConstant) found.Add(part);
            foreach (var operand in t.Operands) Go(operand);
        }
        Go(address);
        return found.Distinct(ReferenceEqualityComparer.Instance).Cast<Term>();
    }

    private static IEnumerable<Term> Roots(EffectGraph graph)
    {
        foreach (int b in graph.Order)
        {
            var block = new BlockId(b);
            if (graph.Condition(block) is { } condition) yield return condition;
            if (graph.ReturnSlot(block) is { } returned) yield return returned;
        }
        foreach (var effect in graph.Effects)
        {
            if (effect.Address is { } address) yield return address;
            if (effect.Kind == NativeEffectKind.Write) yield return effect.Value!;
            foreach (var argument in effect.Arguments) yield return argument;
        }
    }

    /// <summary>从根到每个子项的链。</summary>
    private static IEnumerable<List<Term>> Chains(Term term, List<Term> above, HashSet<Term> seen)
    {
        if (!seen.Add(term)) yield break;
        var chain = new List<Term>(above) { term };
        yield return chain;
        foreach (var operand in term.Operands)
            foreach (var deeper in Chains(operand, chain, seen))
                yield return deeper;
    }
}
