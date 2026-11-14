using System.Numerics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Naming;

public sealed partial class ValueNamingQuery
{
    /// <summary>名字唯一决定的值；忽略实体槽位和不可变字段的内存版本。</summary>
    public Outcome<ValueName?> FixedValue(QueryContext c, Term value)
    {
        var resolved = c.Get(state.Resolve, value);
        if (!resolved.IsSuccess) return resolved.Propagate<ValueName?>();
        if (resolved.Value.ContainsUndefined) return Outcome<ValueName?>.Success(null);
        var named = c.Get(this, resolved.Value);
        return named.IsSuccess ? Outcome<ValueName?>.Success(named.Value.EquivalentName ?? FixedName(named.Value.Name)) : named.Propagate<ValueName?>();
    }

    /// <summary>共享同值判断；没有定值凭据的同名位置不消去读取版本。</summary>
    public Outcome<bool> SameValue(QueryContext c, Term left, Term right)
    {
        var a = c.Get(state.Resolve, left); if (!a.IsSuccess) return a.Propagate<bool>();
        var b = c.Get(state.Resolve, right); if (!b.IsSuccess) return b.Propagate<bool>();
        if (a.Value == b.Value && !a.Value.ContainsUndefined) return Outcome<bool>.Success(true);
        var x = FixedValue(c, a.Value); if (!x.IsSuccess) return x.Propagate<bool>();
        var y = FixedValue(c, b.Value); if (!y.IsSuccess) return y.Propagate<bool>();
        return Outcome<bool>.Success(x.Value is not null && x.Value == y.Value);
    }

    /// <summary>托管捕获对象非空；其空测试的组合仍由项的规范化求值。</summary>
    public Outcome<Term> KnownCondition(QueryContext c, Term condition)
    {
        var resolved = c.Get(state.Resolve, condition); if (!resolved.IsSuccess) return resolved;
        var mapped = new Dictionary<Term, Term>();
        Term Map(Term term)
        {
            if (mapped.TryGetValue(term, out var known)) return known;
            if (term.Operator is CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual } op)
                for (int i = 0; i < 2; i++)
                    if (term.Operands[1 - i].ConstantValue == 0
                        && c.Get(this, term.Operands[i]) is { IsSuccess: true, Value.Name: CaughtExceptionName })
                        return mapped[term] = term.Table.Constant(op.Operation == CoreOperation.Equal ? 0 : 1, 1);
            return mapped[term] = SnapshotRewrite.Rebuild(term, Map);
        }
        return Outcome<Term>.Success(Map(resolved.Value));
    }

    private RuntimeField? SpecificationField(FieldName field) => field.Index is null &&
        spec.Layout.Records.TryGetValue(field.Record, out var record) &&
        field.Field.StartsWith(field.Record + ".", StringComparison.Ordinal)
        ? record.Fields.GetValueOrDefault(field.Field[(field.Record.Length + 1)..]) : null;

    private ValueName? FixedName(ValueName? name) => name switch
    {
        EntityName entity => entity with { Slot = null },
        // 定义名字指向同一动态环境中的 SSA 值；LoadedName 自带读取版本。
        ParameterName or IndirectParameterName or CallResultName or LoadedName or ReferenceValueName or RuntimeInputName or AddressName => name,
        FieldName field when SpecificationField(field)?.ImmutableEvidence is { Length: > 0 }
            && FixedName(field.Owner) is { } owner => field with { Owner = owner },
        ArrayElementName element when !element.Index.ContainsUndefined
            && SpecificationField(element.Array)?.ArrayElement?.ImmutableEvidence is { Length: > 0 }
            && FixedName(element.Array) is FieldName array => element with { Array = array },
        _ => null,
    };

    private Outcome<NamedValue>? ReadSpecificationElement(QueryContext c, Location location)
    {
        if (location.Offset is not null)
        {
            var owner = c.Get(this, location.Root);
            if (!owner.IsSuccess) return owner;
            if (owner.Value.Name is not FieldName field || SpecificationField(field)?.ArrayElement is null) return null;
        }
        var t = c.Snapshot.Terms;
        var address = location.UnknownOffsetAddress ?? location.Root;
        BigInteger offset = location.UnknownOffsetAddress is null ? location.Offset ?? 0 : 0;
        var terms = new List<(Term Value, int Sign)>();
        void Sum(Term value, int sign)
        {
            if (value.ConstantValue is { } n) { offset += sign * n; return; }
            if (value.Operator is CoreOperator { Operation: CoreOperation.Add or CoreOperation.Subtract } op)
            {
                Sum(value.Operands[0], sign);
                Sum(value.Operands[1], op.Operation == CoreOperation.Add ? sign : -sign);
            }
            else terms.Add((value, sign));
        }
        Sum(address, 1);
        // 地址中的模常量按有符号偏移解释，下标仍保留为项。
        var modulus = BigInteger.One << address.Width;
        offset = (offset % modulus + modulus) % modulus;
        if (offset >= modulus / 2) offset -= modulus;
        for (int i = 0; i < terms.Count; i++)
        {
            var item = terms[i];
            if (item.Sign != 1) continue;
            var named = c.Get(this, item.Value);
            if (!named.IsSuccess) return named;
            if (named.Value.Name is not FieldName array || SpecificationField(array)?.ArrayElement is not { } element
                || element.Size <= 0 || element.Size * 8 != location.Width || offset % element.Size != 0) continue;
            var index = t.Constant((offset / element.Size + modulus) % modulus, address.Width);
            bool valid = true;
            for (int j = 0; j < terms.Count; j++)
            {
                if (j == i) continue;
                var part = terms[j];
                var unscaled = Unscale(part.Value, element.Size);
                if (unscaled is null) { valid = false; break; }
                index = t.Apply(new CoreOperator(part.Sign == 1 ? CoreOperation.Add : CoreOperation.Subtract), address.Width, index, unscaled);
            }
            if (valid) return Yes(SpecificationValue(new ArrayElementName(array, index), element.Type));
        }
        return null;
    }

    private static Term? Unscale(Term value, long scale)
    {
        var t = value.Table;
        if (scale == 1) return value;
        if (value.Operator is CoreOperator { Operation: CoreOperation.Multiply })
            foreach (var (factor, other) in new[] { (value.Operands[0], value.Operands[1]), (value.Operands[1], value.Operands[0]) })
                if (factor.ConstantValue is { } n && n % scale == 0)
                    return t.Apply(new CoreOperator(CoreOperation.Multiply), value.Width, other, t.Constant(n / scale, value.Width));
        int bits = 0;
        while (scale > 1 && scale % 2 == 0) { bits++; scale /= 2; }
        if (scale != 1 || bits >= value.Width || t.Slice(value, 0, bits).ConstantValue != 0) return null;
        return t.Apply(new CoreOperator(CoreOperation.ZeroExtend), value.Width, t.Slice(value, bits, value.Width - bits));
    }
}
