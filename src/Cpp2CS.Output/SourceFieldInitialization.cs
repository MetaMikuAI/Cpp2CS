using System.Reflection;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>局部结构体的完整初始化：用 default 合并清零，保留随后可观察的字段设置。</summary>
internal static class SourceFieldInitialization
{
    internal static ManagedBody Rewrite(ManagedBody body, Func<MethodRef, FieldRef?> writtenField)
    {
        static ManagedValue Unwrap(ManagedValue value) => value is AddressValue address ? Unwrap(address.Target) : value;
        static (LocalValue Root, FieldRef[] Path)? Location(ManagedValue value)
        {
            if (value is IndirectValue { Address: AddressValue address }) value = address.Target;
            value = Unwrap(value);
            var path = new List<FieldRef>();
            while (value is FieldValue field)
            {
                if (field.Accessor is { } accessor && (!accessor.Write || !accessor.Field.Equals(field.Field)
                    || !accessor.ValueType.Equals(field.Type) || accessor.Width != field.Width)) return null;
                var receiver = Unwrap(field.Receiver);
                if (receiver.Type is not DefinitionRef { Definition.IsValueType: true }) return null;
                path.Insert(0, field.Field); value = receiver;
            }
            return value is LocalValue { Type: DefinitionRef { Definition.IsValueType: true } } local ? (local, path.ToArray()) : null;
        }
        static List<FieldRef[]>? Leaves(DefinitionRef type, int depth = 0)
        {
            if (depth > 16 || (type.Definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout) return null;
            var result = new List<FieldRef[]>();
            foreach (var field in type.Definition.Fields.Where(f => !f.IsStatic))
            {
                var reference = new FieldRef(field, type);
                if (field.Type.Substitute(type.Arguments, []) is DefinitionRef { Definition: { IsValueType: true, IsEnum: false } } child
                    && ManagedTypes.PrimitiveName(child) is null)
                {
                    if (Leaves(child, depth + 1) is not { Count: > 0 } nested) return null;
                    result.AddRange(nested.Select(path => new[] { reference }.Concat(path).ToArray()));
                }
                else result.Add([reference]);
            }
            return result;
        }
        (LocalValue Root, FieldRef[] Path, ManagedValue Value)? Write(ManagedStatement statement)
        {
            if (statement is ManagedStore store && Location(store.Target) is { } location) return (location.Root, location.Path, store.Value);
            if (statement is ManagedCall { Tail: false, Result: null, Invocation: { Receiver: { } receiver, Arguments: [var value] } call }
                && Location(receiver) is { } target && writtenField(call.Method) is { } field)
                return (target.Root, [.. target.Path, field], value);
            return null;
        }
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var statements = block.Statements.ToList();
            for (var i = 0; i < statements.Count; i++)
            {
                if (Write(statements[i]) is not { } first || first.Root.Type is not DefinitionRef type
                    || Leaves(type) is not { Count: > 0 } expected) continue;
                var covered = new List<FieldRef[]>();
                var dirty = new List<FieldRef[]>();
                var keep = new List<ManagedStatement>();
                var end = i;
                var removed = 0;
                while (end < statements.Count && Write(statements[end]) is { } write && write.Root.Equals(first.Root))
                {
                    var value = write.Value;
                    var zero = value is ConstantValue { Bits: 0 } or ComposedValue { Leaves.Count: 0 };
                    if (value is not (ConstantValue or StringValue or ArgumentValue or LocalValue or ComposedValue { Leaves.Count: 0 })
                        || value is LocalValue local && local.Variable == first.Root.Variable) break;
                    var paths = value is ComposedValue { Leaves.Count: 0, Type: DefinitionRef nestedType }
                        && Leaves(nestedType) is { } nested ? nested.Select(p => write.Path.Concat(p).ToArray()).ToArray() : [write.Path];
                    if (paths.Any(p => !expected.Any(e => e.SequenceEqual(p)))) break;
                    covered.AddRange(paths);
                    if (zero && !paths.Any(p => dirty.Any(d => d.SequenceEqual(p)))) removed++;
                    else keep.Add(statements[end]);
                    if (!zero) dirty.AddRange(paths);
                    end++;
                }
                if (removed == 0 || !expected.All(e => covered.Any(p => e.SequenceEqual(p)))) continue;
                var initialized = new ManagedStore(statements[i].Address, new IndirectValue(new AddressValue(first.Root), type), new ComposedValue(type, []));
                statements.RemoveRange(i, end - i);
                statements.InsertRange(i, new ManagedStatement[] { initialized }.Concat(keep));
                i += keep.Count;
            }
            return block with { Statements = statements };
        }).ToArray() };
    }
}
