using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>源码中的内联库操作：匹配库方法体或已知集合操作的控制流与读写结构。</summary>
public sealed partial class SourceLibraryCalls(ProgramFacts facts, ManagedTypes types, MethodRecovery recovery)
{
    private sealed record Pattern(MethodRef Method, ManagedStatement[] Statements, Dictionary<Variable, ManagedValue> Values, ManagedValue Returned);
    private readonly Dictionary<TypeDef, Pattern[]> patterns = [];
    public List<string> Evidence { get; } = [];
    private int next = -4_000_000;

    private IEnumerable<(FieldRef[] Path, TypeRef Type)> Leaves(TypeRef type, FieldRef[]? path = null)
    {
        path ??= [];
        if (type is not DefinitionRef d || facts.Layouts.Of(d) is not { } layout) yield break;
        foreach (var field in layout.Fields)
        {
            var p = path.Append(new FieldRef(field.Field, d)).ToArray();
            if (types.Kind(field.Type) == TypeKind.Struct)
            {
                foreach (var leaf in Leaves(field.Type, p)) yield return leaf;
            }
            else yield return (p, field.Type);
        }
    }

    private static (ManagedValue Root, FieldRef[] Path) Path(ManagedValue value)
    {
        var path = new List<FieldRef>();
        while (value is FieldValue field)
        {
            path.Insert(0, field.Field);
            value = field.Receiver is AddressValue address ? address.Target : field.Receiver;
        }
        return (value, path.ToArray());
    }

    private ManagedValue Normalize(ManagedValue value)
    {
        if (value is IndirectValue { Address: AddressValue address }) return address.Target;
        if (value is FieldValue { Receiver: AddressValue { Target: ComposedValue composed } } field
            && composed.Leaves.FirstOrDefault(l => l.Path.Count == 1 && l.Path[0].Equals(field.Field)).Value is { } component) return component;
        if (value is not ComposedValue aggregate || aggregate.Leaves.Count == 0) return value;
        var expected = Leaves(aggregate.Type).ToArray();
        if (expected.Length != aggregate.Leaves.Count || expected.Any(e => !aggregate.Leaves.Any(l => l.Path.SequenceEqual(e.Path)))) return value;
        ManagedValue? Whole(ManagedValue leaf, IReadOnlyList<FieldRef> path)
        {
            foreach (var field in path.Reverse())
            {
                if (leaf is not FieldValue component || !component.Field.Equals(field)) return null;
                leaf = component.Receiver is AddressValue address ? address.Target : component.Receiver;
            }
            return leaf;
        }
        var whole = aggregate.Leaves.Select(l => Whole(l.Value, l.Path)).ToArray();
        if (whole[0] is { } common && common.Type.Equals(aggregate.Type) && whole.All(v => Equals(v, common))) return common;
        var roots = aggregate.Leaves.Select(l => (l, p: Path(l.Value))).ToArray();
        if (!roots.All(p => p.p.Root.Equals(roots[0].p.Root) && p.p.Path.SequenceEqual(p.l.Path))) return value;
        var root = roots[0].p.Root;
        return root.Type.Equals(value.Type) ? root : root.Type is ByRefRef reference && reference.Element.Equals(value.Type)
            ? new IndirectValue(root, value.Type) : value;
    }

    private ManagedValue Expand(ManagedValue value, IReadOnlyDictionary<Variable, ManagedValue> values)
    {
        var visited = 0;
        ManagedValue Walk(ManagedValue current, int depth)
        {
            if (++visited > 512 || depth >= 32) return current;
            if (current is LocalValue local && values.TryGetValue(local.Variable, out var source)) return Walk(source, depth + 1);
            return Normalize(ManagedValues.Map(current, child => Walk(child, depth + 1)));
        }
        return Walk(value, 0);
    }

    private Pattern[] Patterns(TypeDef owner)
    {
        if (patterns.TryGetValue(owner, out var cached)) return cached;
        var list = new List<Pattern>();
        foreach (var method in owner.Methods.Where(m => m.Address != 0 && m.GenericParameters.Count == 0 && owner.GenericParameters.Count == 0
            && facts.Code.RegionOf(m.Address) == CodeRegion.Managed
            && (m.Attributes & System.Reflection.MethodAttributes.MemberAccessMask) == System.Reflection.MethodAttributes.Public
            && m.Name is not (".ctor" or ".cctor") && m.Parameters.Count <= 3).OrderBy(m => m.Parameters.Count))
        {
            var reference = new MethodRef(method, [], []);
            if (recovery.Recover(reference, method.Address).Body is not { Regions.Count: 0 } original) continue;
            var body = SourceRewriter.Rewrite(original, types);
            var blocks = body.Blocks.ToDictionary(b => b.Address);
            var seen = new HashSet<ulong>();
            var statements = new List<ManagedStatement>();
            var block = body.Blocks[0];
            while (seen.Add(block.Address))
            {
                statements.AddRange(block.Statements.Where(s => s is not ManagedJump));
                if (block.Statements.LastOrDefault() is not ManagedJump { Edge.Copies.Count: 0 } jump || !blocks.TryGetValue(jump.Edge.Target, out block!)) break;
            }
            if (statements.LastOrDefault() is ManagedCall { Tail: true } tail)
            {
                var result = new LocalValue(new Variable(Storage.Temp(next--), 1), method.ReturnType, types.Kind(method.ReturnType) == TypeKind.Struct ? 0 : types.Size(method.ReturnType) * 8);
                statements[^1] = tail with { Tail = false, Result = result };
                statements.Add(new ManagedReturn(tail.Address, result));
            }
            if (seen.Count != body.Blocks.Count || statements.Count > 40 || statements.LastOrDefault() is not ManagedReturn { Value: { } returned }
                || statements.Take(statements.Count - 1).Any(s => s is not (ManagedAssignment or ManagedCall { Tail: false, Result: not null }))) continue;
            var assignments = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).ToArray();
            if (assignments.Any(g => g.Count() != 1)) continue;
            var values = assignments.ToDictionary(g => g.Key, g => g.Single().Value);
            list.Add(new(reference, statements.ToArray(), values, Expand(returned, values)));
        }
        return patterns[owner] = list.ToArray();
    }

    public ManagedBody Rewrite(ManagedBody body)
    {
        body = SourceFieldInitialization.Rewrite(body, method => method.DeclaringType is DefinitionRef type
            ? FieldCalls(type).FirstOrDefault(c => c.Write && c.Method.Equals(method))?.Field : null);
        SourceValueConstructor? Constructor(MethodRef method)
        {
            if (method.Method.Name != ".ctor" || method.DeclaringType is not DefinitionRef type) return null;
            _ = FieldCalls(type);
            return valueConstructors[type].FirstOrDefault(c => c.Method.Equals(method));
        }
        body = SourceConstructorWrites.Rewrite(body, type =>
        {
            _ = FieldCalls(type);
            return valueConstructors[type].Where(c => ManagedAccess.Method(types, body.Method.Method.Owner, c.Method, null));
        }, (site, method) => Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{site:x}\t{body.Method}\t{method}"));
        body = SourceListCalls.Rewrite(body, types, (site, method) =>
            Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{site:x}\t{body.Method}\t{method}"), Constructor);
        body = RewriteGuardedUpdates(body);
        body = RewriteFieldCalls(body);
        var caller = body.Method.Method.Owner;
        body = AccessorRewriter.Rewrite(body, (value, write) =>
        {
            var existing = value switch { FieldValue f => f.Accessor, StaticFieldValue f => f.Accessor, _ => null };
            if (write || existing is not null || value is not FieldValue field || CollectionCount(field, caller) is not { } count) return existing;
            Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{body.Method.Method.Address:x}\t{body.Method}\t{count.Method}");
            return count;
        });
        var blocks = new List<ManagedBlock>();
        foreach (var block in body.Blocks)
        {
            var output = new List<ManagedStatement>();
            var statements = block.Statements.ToList();
            for (var i = 0; i < statements.Count; i++)
            {
                var statement = statements[i];
                if (statement is ManagedCall call && !ManagedAccess.Method(types, caller, call.Invocation.Method, call.Invocation.Receiver?.Type))
                {
                    foreach (var pattern in Patterns(call.Invocation.Method.Method.Owner))
                    {
                        if (!ManagedAccess.Method(types, caller, pattern.Method, pattern.Method.Method.IsStatic ? null : new ByRefRef(pattern.Method.DeclaringType))) continue;
                        if (!Match(body, statements, i, pattern, out var replacement, out var end)) continue;
                        output.Add(replacement!);
                        Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{call.Address:x}\t{body.Method}\t{pattern.Method}");
                        i = end;
                        statement = null!;
                        break;
                    }
                    if (statement is null) continue;
                }
                var loaded = new Dictionary<StaticFieldValue, LocalValue>();
                ManagedValue Replace(ManagedValue value)
                {
                    if (value is IndirectValue { Address: AddressValue { Target: StaticFieldValue storage } } indirect
                        && storage.Type.Equals(indirect.Type)) value = storage;
                    if (value is AddressValue) return value;
                    if (value is not StaticFieldValue field || ManagedAccess.Field(types, caller, field.Field, null)
                        || (field.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) == 0) return ManagedValues.Map(value, Replace);
                    var getter = Patterns(field.Field.Field.Owner).FirstOrDefault(p => p.Method.Method.IsStatic && p.Method.Method.Parameters.Count == 0
                        && !p.Statements.OfType<ManagedCall>().Any() && p.Returned is StaticFieldValue f && f.Field.Equals(field.Field)
                        && p.Statements.OfType<ManagedAssignment>().SelectMany(a => ManagedValues.Walk(Expand(a.Value, p.Values)))
                            .All(v => v is ConstantValue or FieldValue or AddressValue or ComposedValue || v is StaticFieldValue read && read.Field.Equals(field.Field)));
                    if (getter is null) return value;
                    if (!ManagedAccess.Method(types, caller, getter.Method, null)) return value;
                    if (!loaded.TryGetValue(field, out var local))
                    {
                        loaded[field] = local = new LocalValue(new Variable(Storage.Temp(next--), 1), field.Type, field.Width);
                        output.Add(new ManagedCall(statement.Address, new ManagedInvocation(getter.Method, null, [], false), local, false));
                        Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{statement.Address:x}\t{body.Method}\t{getter.Method}");
                    }
                    return local;
                }
                // 只替换读取；字段地址若被写入或传出，保留原始操作。
                if (statement is ManagedAssignment or ManagedCall or ManagedReturn or ManagedStore)
                    statement = ManagedValues.Map(statement, Replace, target => target);
                output.Add(statement);
            }
            blocks.Add(block with { Statements = output.ToArray() });
        }
        var fieldGetters = fieldCalls.Values.SelectMany(c => c).Where(c => !c.Write && !c.Method.Method.IsStatic).Select(c => c.Method).ToHashSet();
        return SourceRewriter.Rewrite(body with { Blocks = blocks }, types, fieldGetters.Contains);
    }

    private bool Match(ManagedBody body, List<ManagedStatement> statements, int start, Pattern pattern, out ManagedCall? replacement, out int end)
    {
        replacement = null;
        end = start;
        var calls = pattern.Statements.OfType<ManagedCall>().ToArray();
        if (calls.Length == 0 || calls.Length > 3 || pattern.Returned is not LocalValue returned || calls[^1].Result?.Variable != returned.Variable) return false;
        var definitions = statements.Take(start).OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable)
            .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single().Value);
        var bound = new Dictionary<int, ManagedValue>();
        var fields = new Dictionary<int, Dictionary<string, (FieldRef[] Path, ManagedValue Value)>>();
        var locals = new Dictionary<Variable, ManagedValue>();
        var removed = new HashSet<Variable>();
        var firstCall = (ManagedCall)statements[start];
        var callIndex = 0;
        bool Unify(ManagedValue p, ManagedValue v)
        {
            p = Expand(p, pattern.Values);
            if (p is LocalValue symbolic) return locals.TryGetValue(symbolic.Variable, out var actualLocal) && actualLocal.Equals(v);
            if (p is IndirectValue { Address: ArgumentValue parameter } && parameter.Type is ByRefRef reference && reference.Element.Equals(v.Type))
                return v is LocalValue or ArgumentValue && Unify(parameter, new AddressValue(v));
            if (p is ArgumentValue argument)
            {
                if (!argument.Type.Equals(v.Type)) return false;
                if (bound.TryGetValue(argument.Index, out var previous)) return previous.Equals(v);
                if (callIndex != 0) return false;
                bound[argument.Index] = v;
                return true;
            }
            v = Expand(v, definitions);
            // 正有限常数乘以 ±0 仍是同一符号的零；只反向绑定这个精确恒等式，不反求一般浮点除法。
            if (v is ConstantValue { Width: 32 } zero && (zero.Bits & 0x7fffffff) == 0
                && p is BinaryValue { Op: BinOp.FMul, Right: ConstantValue { Width: 32 } factor } multiplication
                && factor.Bits is > 0 and < 0x7f800000)
                return Unify(multiplication.Left, zero);
            var path = Path(p);
            if (path.Root is ArgumentValue root && path.Path.Length > 0 && p.Type.Equals(v.Type))
            {
                if (!fields.TryGetValue(root.Index, out var entries)) fields[root.Index] = entries = [];
                var key = string.Join('/', path.Path.Select(f => f.Field.Index));
                if (entries.TryGetValue(key, out var previous)) return previous.Value.Equals(v);
                if (callIndex != 0) return false;
                entries[key] = (path.Path, v);
                return true;
            }
            if (p.GetType() != v.GetType() || !p.Type.Equals(v.Type) || p.Width != v.Width) return false;
            if (p is ComposedValue pc && v is ComposedValue vc)
                return pc.Leaves.Count == vc.Leaves.Count && pc.Leaves.All(l => vc.Leaves.Any(r => l.Path.SequenceEqual(r.Path) && Unify(l.Value, r.Value)));
            if (!ManagedValues.Map(p, c => new ConstantValue(0, c.Type, c.Width)).Equals(ManagedValues.Map(v, c => new ConstantValue(0, c.Type, c.Width)))) return false;
            return ManagedValues.Children(p).Zip(ManagedValues.Children(v)).All(pair => Unify(pair.First, pair.Second));
        }
        ManagedCall? last = null;
        var at = start;
        foreach (var expected in calls)
        {
            while (at < statements.Count && statements[at] is ManagedAssignment assignment)
            {
                if (ManagedValues.Walk(assignment.Value).Any(v => v is StaticFieldValue or ArrayElementValue or IndirectValue or NewObjectValue or NewArrayValue
                    || v is FieldValue f && (Path(f).Root is not (LocalValue or ArgumentValue) || types.Kind(Path(f).Root.Type) != TypeKind.Struct))) return false;
                definitions[assignment.Target.Variable] = assignment.Value; removed.Add(assignment.Target.Variable); at++;
            }
            if (at >= statements.Count || statements[at] is not ManagedCall { Tail: false } actual || !actual.Invocation.Method.Equals(expected.Invocation.Method)
                || actual.Invocation.Virtual != expected.Invocation.Virtual
                || (expected.Invocation.Receiver is null) != (actual.Invocation.Receiver is null) || expected.Invocation.Arguments.Count != actual.Invocation.Arguments.Count) return false;
            if (expected.Invocation.Receiver is { } receiver && !Unify(receiver, actual.Invocation.Receiver!)) return false;
            if (!expected.Invocation.Arguments.Zip(actual.Invocation.Arguments).All(pair => Unify(pair.First, pair.Second))) return false;
            if (expected.Result is not { } result || actual.Result is null) return false;
            locals[result.Variable] = actual.Result;
            removed.Add(actual.Result.Variable);
            last = actual;
            end = at++;
            callIndex++;
        }
        if (last?.Result is not { } final || !final.Type.Equals(pattern.Returned.Type)) return false;
        removed.Remove(final.Variable);
        var replaced = statements.Skip(start).Take(end - start + 1).ToHashSet();
        if (body.Blocks.SelectMany(b => b.Statements).Where(s => !replaced.Contains(s))
            .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => removed.Contains(l.Variable))) return false;
        ManagedValue? Argument(int index, TypeRef type)
        {
            if (bound.TryGetValue(index, out var value)) return value;
            if (!fields.TryGetValue(index, out var entries)) return null;
            var leaves = Leaves(type).ToArray();
            if (leaves.Length == 0 || leaves.Length != entries.Count || leaves.Any(l => !entries.ContainsKey(string.Join('/', l.Path.Select(f => f.Field.Index))))) return null;
            return new ComposedValue(type, leaves.Select(l => ((IReadOnlyList<FieldRef>)l.Path, entries[string.Join('/', l.Path.Select(f => f.Field.Index))].Value)).ToArray());
        }
        var method = pattern.Method.Method;
        var arguments = method.Parameters.Select((p, i) => Argument(i, p.Type)).ToArray();
        var self = method.IsStatic ? null : Argument(-1, new ByRefRef(pattern.Method.DeclaringType));
        if (arguments.Any(a => a is null) || !method.IsStatic && self is null) return false;
        // 绑定值只允许快照、值参数和常量；不把可变内存读取移到新的调用位置。
        if (arguments.Append(self).OfType<ManagedValue>().SelectMany(ManagedValues.Walk).Any(v => v is StaticFieldValue or ArrayElementValue or IndirectValue or NewObjectValue or NewArrayValue
            || v is FieldValue f && (Path(f).Root is not (LocalValue or ArgumentValue) || types.Kind(Path(f).Root.Type) != TypeKind.Struct))) return false;
        if (arguments.Any(a => a!.Type is ByRefRef)) return false;
        replacement = new ManagedCall(firstCall.Address, new ManagedInvocation(pattern.Method, self, arguments!, false), final, false);
        return true;
    }
}
