using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Dispatch;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public sealed record MathOutput(string Name, ImmutableArray<MemoryRead> Reads);

/// <summary>数学导入的私有输出槽：只有该调用写入，完整读取的到达定义也必须是该调用。</summary>
public sealed class MathOutputQuery(StateQueries state, CallNamingQuery calls, FrameAddressUseQuery addressUses, MethodBinder binder, SignatureBinding signature, DispatchQuery? dispatch) : Query<CallIdentity, ImmutableArray<MathOutput>>
{
    private readonly BoundSourceQuery sources = new(state);
    public override Outcome<ImmutableArray<MathOutput>> Compute(QueryContext c, CallIdentity key)
    {
        Outcome<ImmutableArray<MathOutput>> No(string code, string message, Reason? cause = null) =>
            Outcome<ImmutableArray<MathOutput>>.Failure(new("lowering.Math." + code, message, cause));
        var classified = c.Get(calls, key);
        if (!classified.IsSuccess) return classified.Propagate<ImmutableArray<MathOutput>>();
        var function = classified.Value.Function!;
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<ImmutableArray<MathOutput>>();
        var owner = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(call => call.Identity == key));
        var call = owner.Statements.OfType<Call>().Single(call => call.Identity == key);
        var point = new Point(owner.Identity, owner.Statements.IndexOf(call));
        Outcome<ImmutableArray<Term>> CallUses(Call other, Point at, string? ignored = null)
        {
            var target = c.Get(calls, other.Identity); if (!target.IsSuccess) return target.Propagate<ImmutableArray<Term>>();
            var binding = target.Value.Binding;
            if (binding is null && target.Value.Candidates is { Candidates: [{ Binding.Value: { } managed }] }) binding = managed;
            if (binding is null && target.Value.Kind == CallKind.Indirect && dispatch is not null)
            {
                var resolved = c.Get(dispatch, other.Identity);
                if (resolved.IsSuccess) binding = resolved.Value.Binding;
            }
            if (binding is null) return Outcome<ImmutableArray<Term>>.Failure(new("lowering.Math.UseBinding", "数学输出用途中的调用没有唯一 ABI 绑定，不能排除额外使用", target.Value.Why));
            var terms = ImmutableArray.CreateBuilder<Term>();
            for (int p = 0; p < binding.Arguments.Length; p++)
            {
                if (other.Identity == key && function.Arguments[p] == ignored) continue;
                var value = c.Get(sources, new(binding.Arguments[p].Source, at));
                if (!value.IsSuccess) return value.Propagate<ImmutableArray<Term>>();
                terms.Add(value.Value);
            }
            if (other.Target is ComputedTarget computed) terms.Add(computed.Value);
            return Outcome<ImmutableArray<Term>>.Success(terms.ToImmutable());
        }
        Outcome<ImmutableArray<Term>> EndUses(Block block)
        {
            if (block.End is not Return returned) return Outcome<ImmutableArray<Term>>.Success([.. SnapshotRewrite.Uses(block.End)]);
            if (signature.Signature.ReturnType is CVoid) return Outcome<ImmutableArray<Term>>.Success([]);
            var binding = binder.Return(returned, signature, c.Snapshot.Terms,
                c.Snapshot.Inputs.Select(v => new SlotValue(v.Slot, v.Value)).ToImmutableArray(), c.Snapshot.IncomingArgumentArea);
            var value = c.Get(sources, new(binding.Value?.Source, new(block.Identity, block.Statements.Length)));
            return value.IsSuccess ? Outcome<ImmutableArray<Term>>.Success([value.Value]) : value.Propagate<ImmutableArray<Term>>();
        }
        if (function.MathRewrite == "TruncateOutput")
        {
            Outcome<bool> Fraction(IEnumerable<Term> roots)
            {
                foreach (var root in roots)
                {
                    var value = c.Get(state.Resolve, root); if (!value.IsSuccess) return value.Propagate<bool>();
                    if (SnapshotRewrite.Dependencies([root, value.Value]).Any(t => t.Identity is ResultAtom { Definition: CallIdentity producer } && producer == key))
                        return Outcome<bool>.Success(true);
                }
                return Outcome<bool>.Success(false);
            }
            foreach (var block in c.Snapshot.Blocks)
            {
                var end = EndUses(block); if (!end.IsSuccess) return end.Propagate<ImmutableArray<MathOutput>>();
                var roots = block.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)).Concat(end.Value)
                    .Concat(block.Statements.Where(s => s is not Call).SelectMany(SnapshotRewrite.Uses));
                var fraction = Fraction(roots); if (!fraction.IsSuccess) return fraction.Propagate<ImmutableArray<MathOutput>>();
                if (fraction.Value) return No("FractionUsed", "modf 的小数返回值被使用，没有直接托管对应");
            }
            foreach (var block in c.Snapshot.Blocks)
                for (int i = 0; i < block.Statements.Length; i++)
                    if (block.Statements[i] is Call other)
                    {
                        var uses = CallUses(other, new(block.Identity, i)); if (!uses.IsSuccess) return uses.Propagate<ImmutableArray<MathOutput>>();
                        var fraction = Fraction(uses.Value); if (!fraction.IsSuccess) return fraction.Propagate<ImmutableArray<MathOutput>>();
                        if (fraction.Value) return No("FractionUsed", "modf 的小数返回值进入实参，没有直接托管对应");
                    }
        }

        var outputs = ImmutableArray.CreateBuilder<MathOutput>();
        foreach (var effect in function.Operation.PointerEffects)
        {
            int width = effect.Extent.Bytes * 8;
            var pointer = c.Get(sources, new(classified.Value.Inputs![effect.Input].Source, point));
            if (!pointer.IsSuccess) return No("Output", "数学输出地址没有绑定", pointer.Why);
            var resolved = c.Get(state.Resolve, pointer.Value); if (!resolved.IsSuccess) return resolved.Propagate<ImmutableArray<MathOutput>>();
            var storage = c.Get(state.Locations, new(resolved.Value, width));
            if (!storage.IsSuccess || storage.Value is not { Region: Region.Frame, Offset: not null })
                return No("Output", "数学输出必须是起点确定的私有帧槽", storage.Why);
            if (c.Snapshot.IncomingArgumentArea is { } incoming)
            {
                var area = c.Get(state.Locations, new(incoming, width));
                if (!area.IsSuccess || storage.Value.Root == area.Value.Root && (area.Value.Offset is null || storage.Value.Offset >= area.Value.Offset))
                    return No("Output", "数学输出槽可能属于调用方栈实参区");
            }
            var reads = ImmutableArray.CreateBuilder<MemoryRead>();
            Outcome<bool> Uses(IEnumerable<Term> roots)
            {
                foreach (var root in roots)
                {
                    var uses = c.Get(addressUses, root); if (!uses.IsSuccess) return uses.Propagate<bool>();
                    foreach (var use in uses.Value)
                    {
                        var alias = c.Get(state.Alias, new(storage.Value, use.Location)); if (!alias.IsSuccess) return alias.Propagate<bool>();
                        if (alias.Value.Kind != AliasKind.Disjoint) return Outcome<bool>.Success(true);
                    }
                }
                return Outcome<bool>.Success(false);
            }
            foreach (var block in c.Snapshot.Blocks)
            {
                var end = EndUses(block); if (!end.IsSuccess) return end.Propagate<ImmutableArray<MathOutput>>();
                var blockUses = Uses(block.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)).Concat(end.Value));
                if (!blockUses.IsSuccess) return blockUses.Propagate<ImmutableArray<MathOutput>>();
                if (blockUses.Value) return No("OutputUse", "数学输出槽的地址流入合流或终结");
                for (int i = 0; i < block.Statements.Length; i++)
                {
                    var statement = block.Statements[i];
                    if (statement is MemoryRead or MemoryWrite)
                    {
                        var address = statement is MemoryRead read ? read.Address : ((MemoryWrite)statement).Address;
                        int accessWidth = statement is MemoryRead r ? r.Width : ((MemoryWrite)statement).Width;
                        var source = c.Get(state.Resolve, address); if (!source.IsSuccess) return source.Propagate<ImmutableArray<MathOutput>>();
                        var location = c.Get(state.Locations, new(source.Value, accessWidth)); if (!location.IsSuccess) return location.Propagate<ImmutableArray<MathOutput>>();
                        var overlap = c.Get(state.Alias, new(storage.Value, location.Value)); if (!overlap.IsSuccess) return overlap.Propagate<ImmutableArray<MathOutput>>();
                        if (overlap.Value.Kind != AliasKind.Disjoint)
                        {
                            if (statement is not MemoryRead outputRead || outputRead.Acquire || storage.Value != location.Value)
                                return No("OutputUse", "数学输出槽另有写入、部分访问或不能排除的别名");
                            var value = c.Get(state.Read, outputRead.Identity); if (!value.IsSuccess) return value.Propagate<ImmutableArray<MathOutput>>();
                            if (value.Value.Identity is not MemoryAtom { Definition: CallIdentity producer } || producer != key)
                                return No("OutputUse", "数学输出读取的到达定义不是该调用");
                            reads.Add(outputRead);
                        }
                        if (statement is MemoryRead) continue;
                    }
                    IEnumerable<Term> terms = SnapshotRewrite.Uses(statement);
                    if (statement is Call other)
                    {
                        var bound = CallUses(other, new(block.Identity, i), effect.Input);
                        if (!bound.IsSuccess) return bound.Propagate<ImmutableArray<MathOutput>>();
                        terms = bound.Value;
                    }
                    var use = Uses(terms); if (!use.IsSuccess) return use.Propagate<ImmutableArray<MathOutput>>();
                    if (use.Value) return No("OutputUse", "数学输出槽的地址还有其他用途或与另一个输出相交");
                }
            }
            if (reads.Count == 0) return No("OutputUse", "数学输出槽没有完整读取");
            outputs.Add(new(effect.Input, reads.ToImmutable()));
        }
        return Outcome<ImmutableArray<MathOutput>>.Success(outputs.ToImmutable());
    }
}
