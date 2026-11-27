using System.Collections.Immutable;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Discovery;

internal sealed partial class TemplateSearch
{
    private IEnumerable<Binding> BindEffect(CatalogEntry entry, int at, NativeEffect effect, Binding initial)
    {
        var step = entry.Steps[at];
        var bound = initial with { Required = initial.Required.Add(EffectRef.Of(effect.Occurrence)) };
        switch (step.Kind)
        {
            case StepKind.Read:
            case StepKind.Write:
                foreach (var location in Locations(entry, step.Location, effect))
                {
                    var match = bound with { Subject = location.Type, Owner = location.Field?.DeclaringType };
                    if (location.Field is { } field)
                    {
                        if (match.WithEntity(field.Entity) is not { } named) continue;
                        match = named;
                    }
                    if (location.BaseRead is { } baseRead) match = match.WithRead(baseRead);
                    var values = location.Bases;
                    if (step.Kind == StepKind.Write) values = values.Add(effect.Value!);
                    if (MatchRow(step.Values, values, match) is not { } row) continue;
                    if (step.Kind == StepKind.Write) yield return row;
                    else if (row.Result(at, effect.Value!) is { } read) yield return read;
                }
                break;

            case StepKind.Call:
                if (effect.Callee is not { } method || !Fits(entry.Condition, method) || step.Indirect ||
                    bound.WithEntity(method.Entity) is not { } call) break;
                call = call with { Owner = method.DeclaringType, Subject = method.Return };
                if (step.Values.Length > effect.Arguments.Length ||
                    MatchRow(step.Values, effect.Arguments[..step.Values.Length], call) is not { } args) break;
                if (entry.OperandsFromSignature)
                {
                    for (int i = step.Values.Length; i < effect.Arguments.Length; i++)
                    {
                        if (args.Operand(i - step.Values.Length, effect.Arguments[i]) is not { } next) yield break;
                        args = next;
                    }
                }
                if (effect.Result is null) yield return args;
                else if (args.Result(at, effect.Result) is { } produced) yield return produced;
                break;

            case StepKind.NewObject:
                if (effect.Class is { Kind: TermKind.Entity } allocated && bound.Owner is { } expected && allocated.Entity != expected) break;
                if (bound.Results.TryGetValue(at, out var receiver))
                {
                    // 接收者可能是选择项；结果的绑定保留整项，分配候选由它的叶子给出。
                    if (EffectIndex.TermsOf(receiver).Contains(effect.Value!)) yield return bound;
                }
                else if (effect.Value is { } created && bound.Result(at, created) is { } allocation) yield return allocation;
                break;

            case StepKind.ClassInitialize:
                if (effect.Class is { Kind: TermKind.Entity } cls && (bound.Owner is null || bound.Owner == cls.Entity))
                    yield return bound with { Owner = cls.Entity };
                break;

            case StepKind.Throw:
                if (effect.Value is { } thrown && MatchRow(step.Values, [thrown], bound) is { } throwing) yield return throwing;
                break;
        }
    }

    private static bool Fits(VariantCondition condition, MethodShape method) => condition switch
    {
        VariantCondition.None => true,
        VariantCondition.StaticMethod => !method.HasThis && !method.HasInitializer,
        VariantCondition.StaticMethodWithInitializer => !method.HasThis && method.HasInitializer,
        VariantCondition.ReferenceTypeConstructor => method is { HasThis: true, Return: null, Parameters: [{ Kind: StackKind.Object }, ..] },
        _ => condition == method.Dispatch,
    };

    private sealed record Location(TypeShape Type, ImmutableArray<Term> Bases, FieldShape? Field = null, NativeEffect? BaseRead = null);

    private IEnumerable<Location> Locations(CatalogEntry entry, LocationKind kind, NativeEffect effect)
    {
        var address = effect.Address!;
        var (root, offset) = BaseOffset(address);
        switch (kind)
        {
            case LocationKind.InstanceField:
            case LocationKind.FieldAtAddress:
                if (!types.TryGetValue(root, out var type)) break;
                if (kind == LocationKind.InstanceField && type.Kind != StackKind.Object ||
                    kind == LocationKind.FieldAtAddress && type.Kind != StackKind.ByRef) break;
                // 接收者类型来自这个基的签名或结果。嵌套字段即使同址也需要各自的托管接收者。
                if (Field(type, offset) is { IsStatic: false } field && field.Type.StorageBits == effect.Width)
                    yield return new(field.Type, [root], field);
                break;

            case LocationKind.StaticField:
                // FieldAt 只查询实例字段。若项中已有静态字段实体，可由其声明类型和偏移反查静态区上的访问。
                if (Read(root) is not { } statics) break;
                var (owner, slot) = BaseOffset(statics.Address!);
                if (slot != facts.Layout.ClassStaticFieldsOffset || owner.Kind != TermKind.Entity) break;
                foreach (var entity in index.FieldEntities)
                {
                    var member = facts.Metadata.Field(entity);
                    if (member.IsStatic && member.DeclaringType == owner.Entity && member.Offset == offset && member.Type.StorageBits == effect.Width)
                        yield return new(member.Type, [], member, statics);
                }
                break;

            case LocationKind.ArrayElement:
                foreach (var array in EffectIndex.TermsOf(address))
                {
                    if (!types.TryGetValue(array, out var arrayType) || arrayType.Kind != StackKind.Object ||
                        facts.Metadata.ElementOf(arrayType.Entity) is not { } element || element.StorageBits != effect.Width) continue;
                    if (entry.Storage is { } storage && (element.Kind != storage.Kind ||
                        storage.Bits > 0 && element.StorageBits != storage.Bits)) continue;
                    foreach (var subscript in Indices(address, array, element.StorageBits / 8))
                        yield return new(element, [array, subscript]);
                }
                break;
        }
    }

    private IEnumerable<Term> Indices(Term address, Term array, int bytes)
    {
        if (bytes <= 0) yield break;
        var (root, offset) = BaseOffset(address);
        long delta = offset - facts.Layout.ArrayDataOffset;
        if (root == array && delta >= 0 && delta % bytes == 0 && delta / bytes <= int.MaxValue)
            yield return Terms.Constant(delta / bytes, 32);

        // 编译后的下标可能按有符号或无符号数扩展，缩放与加法用项池的同一套规范写法。
        var data = Terms.Add(array, Terms.Constant(facts.Layout.ArrayDataOffset, address.Width));
        var scale = Terms.Constant(bytes, address.Width);
        foreach (var term in EffectIndex.TermsOf(address))
        {
            if (term.Width != 32 || term.IsConstant) continue;
            if (Terms.Add(data, Terms.Mul(Terms.SignExtend(term, address.Width), scale)) == address ||
                Terms.Add(data, Terms.Mul(Terms.ZeroExtend(term, address.Width), scale)) == address)
                yield return term;
        }
    }

    private FieldShape? Field(TypeShape type, long offset)
    {
        long header = type.Kind is StackKind.ByRef or StackKind.Value ? facts.Layout.ObjectHeaderBytes : 0;
        return offset >= 0 && offset <= int.MaxValue - header ? facts.Metadata.FieldAt(type.Entity, (int)(offset + header)) : null;
    }

    private static (Term Base, long Offset) BaseOffset(Term address) =>
        address is { Op: Op.Add, Operands: [var root, { IsConstant: true } offset] }
            ? (root, unchecked((long)(ulong)offset.Value)) : (address, 0L);

    private NativeEffect? Read(Term value) => value.Kind == TermKind.Result &&
        facts.Effects.Effect(value.Occurrence) is { Kind: NativeEffectKind.Read } read ? read : null;
}
