using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>已证明的值类型构造；实参的 IL 类型转换由下降完成。</summary>
internal sealed record ValueConstruction(MethodRef Constructor, IReadOnlyList<ManagedValue> Arguments);

/// <summary>
/// 模板的语义摘要：模板从入口单独执行到底（形参为未知量）得到的各条路径：路径条件、事件、写入、返回值。
/// 访问器、值类型构造都按摘要判定，不看方法体的写法。
/// </summary>
internal sealed class TemplateSummaries(ManagedTypes types, InlineEvidence evidence)
{
    private sealed record PathSummary(ImmutableList<Term> Phi, SideState State, Stop End, List<EventInfo> Events);

    private sealed record Run(TermTable Terms, Interpreter Interpreter, Term[] Formals, List<PathSummary> Paths, Term? Constructed);

    private Run? Execute(Program program, bool construct)
    {
        var method = program.Method;
        var definition = method.Method;
        var terms = new TermTable();
        var solver = new Solver(terms, types);
        var interpreter = new Interpreter(types, solver, evidence) { StepBudget = 2000 };
        var formals = new Term[definition.Parameters.Count + 1];
        formals[0] = definition.IsStatic || construct ? terms.Zero64
            : interpreter.Atom(AtomKind.Formal, -1, definition.Owner.IsValueType ? new ByRefRef(method.DeclaringType) : method.DeclaringType);
        for (var i = 0; i < definition.Parameters.Count; i++)
            formals[i + 1] = interpreter.Atom(AtomKind.Formal, i, method.Concrete(definition.Parameters[i].Type));
        var side = new SideState { Frames = [] };
        var evt = new EventInfo(construct ? EventKind.Construct : EventKind.Call, method, definition.IsStatic || construct ? null : formals[0], formals.Skip(1).ToArray(), false);
        interpreter.Unfold(side, program, evt, null);
        var constructed = side.Frames[0].Constructed;
        var paths = new List<PathSummary>();
        var stack = new Stack<(SideState Side, ImmutableList<Term> Phi, List<EventInfo> Events)>();
        stack.Push((side, [], []));
        var serial = 0;
        while (stack.TryPop(out var current))
        {
            if (paths.Count + stack.Count > 32) return null;
            var (state, phi, events) = current;
            while (true)
            {
                var stop = interpreter.Advance(state, phi);
                if (stop.Kind == StopKind.Fork)
                {
                    foreach (var literal in stop.Alternatives!.Reverse())
                    {
                        if (solver.Decide(phi, literal) == false) continue;
                        var child = state.Clone();
                        child.Stop = null;
                        stack.Push((child, phi.Add(literal), [.. events]));
                    }
                    break;
                }
                if (stop.Kind == StopKind.Event)
                {
                    events.Add(stop.Event!);
                    interpreter.Complete(state, stop.Event!, interpreter.Result(stop.Event!, ++serial));
                    continue;
                }
                paths.Add(new PathSummary(phi, state, stop, events));
                break;
            }
        }
        return new Run(terms, interpreter, formals, paths, constructed);
    }

    // ---- 只读 ----

    private readonly Dictionary<MethodRef, bool> readOnly = [];

    /// <summary>方法只读：每条路径都没有事件，也没有对外可见的写入（结局是返回或抛出）。对它的调用不改变内存。</summary>
    public bool IsReadOnly(Program program)
    {
        if (readOnly.TryGetValue(program.Method, out var known)) return known;
        return readOnly[program.Method] = program.Body.Regions.Count == 0 && Execute(program, false) is { } run
            && run.Paths.All(p => p.Events.Count == 0 && p.End.Kind is StopKind.Return or StopKind.Throw
                && p.State.Writes.All(w => TermTable.Immutable(w.Location) || run.Interpreter.Private(p.State, w.Location)));
    }

    // ---- 访问器 ----

    private readonly Dictionary<(MethodRef, FieldRef, bool, bool), bool> accessors = [];

    /// <summary>
    /// 方法是该字段的访问器：只有一条正常返回的路径，没有事件（静态字段所在类型的类初始化除外），
    /// getter 返回该字段（入口时的内容，结构体按全部叶子），setter 恰把第一个形参写入该字段；
    /// 抛出只有接收者为空时的空引用异常（与字段访问本身相同）。
    /// </summary>
    public bool IsAccessor(Program program, FieldRef field, bool write, bool receiverParameter)
    {
        var key = (program.Method, field, write, receiverParameter);
        if (accessors.TryGetValue(key, out var known)) return known;
        return accessors[key] = Accessor(program, field, write, receiverParameter);
    }

    private bool Accessor(Program program, FieldRef field, bool write, bool receiverParameter)
    {
        if (program.Body.Regions.Count > 0 || Execute(program, false) is not { } run) return false;
        var terms = run.Terms;
        var interpreter = run.Interpreter;
        var isStatic = field.Field.IsStatic;
        var definition = program.Method.Method;
        Term? receiver = isStatic ? null : receiverParameter ? run.Formals[1] : run.Formals[0];
        var path = terms.Path([field]);
        Term location;
        if (isStatic) location = terms.StaticRoot(path);
        else if (!receiverParameter && definition.Owner.IsValueType) location = terms.ReferenceRoot(receiver!, path);
        else location = terms.FieldRoot(receiver!, path);
        var fieldType = field.DeclaringType is DefinitionRef owner ? field.Field.Type.Substitute(owner.Arguments, []) : field.Field.Type;
        var empty = new SideState { Frames = [] };
        var returning = run.Paths.Where(p => p.End.Kind == StopKind.Return).ToArray();
        if (returning.Length != 1) return false;
        foreach (var p in run.Paths.Where(p => p.End.Kind != StopKind.Return))
        {
            if (p.End.Kind != StopKind.Throw || p.End.Thrown!.ExceptionType != "System.NullReferenceException" || receiver is null) return false;
            if (run.Interpreter.Solver.Decide(p.Phi, terms.Compare(Cond.Eq, receiver, terms.Zero64)) != true) return false;
        }
        var only = returning[0];
        var owners = isStatic ? ((DefinitionRef)field.DeclaringType).Definition : null;
        if (only.Events.Any(e => !(e.Kind == EventKind.ClassInit && ReferenceEquals(e.Identity, owners)))) return false;
        var writes = only.State.Writes.Where(w => !TermTable.Immutable(w.Location) && !interpreter.Private(only.State, w.Location)).ToArray();
        if (!write)
        {
            if (writes.Length > 0 || only.End.Value is not { } value) return false;
            return interpreter.ReadValue(empty, location, fieldType, false) is { } expected && ReferenceEquals(expected, value);
        }
        if (only.End.Value is not null || run.Formals.Length < 2) return false;
        var target = new SideState { Frames = [] };
        interpreter.Write(target, location, run.Formals[1], fieldType);
        return writes.Length == target.Writes.Count
            && target.Writes.All(t => writes.Any(w => ReferenceEquals(w.Location, t.Location) && ReferenceEquals(w.Value, t.Value)));
    }

    // ---- 值类型构造 ----

    /// <summary>值类型构造的摘要：新值各叶子的内容（常量、形参或其叶子、经 ref 形参的读取）。</summary>
    private sealed record ValueConstructor(MethodRef Method, Term[] Leaves, Leaf[] Shape, Interpreter Interpreter);

    private readonly Dictionary<DefinitionRef, ValueConstructor[]> valueConstructors = [];

    private static int? FormalIndex(Term atom) => atom.IsAtom(AtomKind.Formal) ? atom.Key switch
    {
        int k when k >= 0 => k,
        ValueTuple<int, int> p when p.Item1 >= 0 => p.Item1,
        _ => null,
    } : null;

    /// <summary>构造函数只写新值、没有事件也不抛出，且新值每片叶子都是常量、形参（的叶子）或经 ref 形参的读取。</summary>
    private ValueConstructor[] ValueConstructors(DefinitionRef structure, Func<MethodRef, Program?> templates)
    {
        if (valueConstructors.TryGetValue(structure, out var known)) return known;
        var found = new List<ValueConstructor>();
        foreach (var definition in structure.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.GenericParameters.Count == 0))
        {
            var method = new MethodRef(definition, structure.Arguments, []);
            if (templates(method) is not { } program || program.Body.Regions.Count > 0 || Execute(program, true) is not { } run) continue;
            if (run.Paths is not [{ End.Kind: StopKind.Return, Events.Count: 0 } only] || run.Constructed is not { } cell) continue;
            var interpreter = run.Interpreter;
            if (only.State.Writes.Any(w => !TermTable.Immutable(w.Location) && !interpreter.Private(only.State, w.Location))) continue;
            if (interpreter.ReadValue(only.State, cell.Location, structure, true) is not { } content) continue;
            var leaves = content.Kind == TermKind.Tuple ? content.Args : [content];
            bool Simple(Term leaf) => leaf.IsConstant || FormalIndex(leaf) is not null
                || leaf.Kind == TermKind.Read && leaf.Location.Root == RootKind.Reference && leaf.Location.Args[0].Key is int k && k >= 0
                    && leaf.Location.Args[0].IsAtom(AtomKind.Formal);
            if (!leaves.All(Simple)) continue;
            found.Add(new ValueConstructor(method, leaves.ToArray(), interpreter.Leaves(structure), interpreter));
        }
        return valueConstructors[structure] = found.ToArray();
    }

    public bool CanConstructValue(DefinitionRef structure, Func<MethodRef, Program?> templates) => ValueConstructors(structure, templates).Length > 0;

    /// <summary>
    /// 以构造函数的摘要证明给定的值：给定的（路径，值）展开到新值的每片叶子（结构体值按字段取下去，缺的叶子为零），
    /// 常量叶子相等；形参叶子绑定为对应的值，结构体形参的各叶子须取自同一个值；经 ref 形参读取的叶子须取自同一个位置，形参绑定为它的地址。
    /// 每个形参都要绑定，各处一致。
    /// </summary>
    public ValueConstruction? Prove(DefinitionRef structure, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves, Func<MethodRef, Program?> templates)
    {
        foreach (var candidate in ValueConstructors(structure, templates))
        {
            var parameters = candidate.Method.Method.Parameters;
            if (leaves.Any(l => !candidate.Shape.Any(s => Prefix(l.Path, s.Path.Fields)))) continue;
            var binding = new ManagedValue?[parameters.Count];
            var valid = true;
            for (var i = 0; i < candidate.Leaves.Length && valid; i++)
            {
                var shape = candidate.Shape[i];
                if (Desired(leaves, shape) is not { } desired) { valid = false; break; }
                var leaf = candidate.Leaves[i];
                if (leaf.IsConstant) valid = desired is ConstantValue c && (c.Bits & Mask(leaf.Width)) == leaf.Bits;
                else if (leaf.IsAtom(AtomKind.Formal) && leaf.Key is int index)
                    valid = Bind(binding, index, desired);
                else if (leaf.IsAtom(AtomKind.Formal) && leaf.Key is ValueTuple<int, int> (var structIndex, var pathId))
                {
                    var type = candidate.Method.Concrete(parameters[structIndex].Type);
                    var formalLeaf = candidate.Interpreter.Leaves(type).FirstOrDefault(l => l.Path.Id == pathId);
                    valid = formalLeaf is not null && Strip(desired, formalLeaf.Path.Fields) is { } root && root.Type.Equals(type) && Bind(binding, structIndex, root);
                }
                else if (leaf.Kind == TermKind.Read && leaf.Location.Args[0].Key is int byRef)
                {
                    var target = Strip(desired, TermTable.PathOf(leaf.Location).Fields);
                    valid = target is LocalValue or ArgumentValue or FieldValue or StaticFieldValue or ArrayElementValue or IndirectValue
                        && candidate.Method.Concrete(parameters[byRef].Type) is ByRefRef reference && reference.Element.Equals(target.Type)
                        && Bind(binding, byRef, new AddressValue(target));
                }
                else valid = false;
            }
            if (!valid || binding.Any(b => b is null)) continue;
            return new ValueConstruction(candidate.Method, binding!);
        }
        return null;
    }

    private static ulong Mask(int width) => width >= 64 ? ulong.MaxValue : (1UL << width) - 1;

    /// <summary>新值在叶子 shape 处的值：给定路径恰为该叶子时取给定值，为它的前缀时从给定的结构体值取下去；没有给定的叶子为零。</summary>
    private ManagedValue? Desired(IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves, Leaf shape)
    {
        var path = shape.Path.Fields;
        foreach (var (prefix, value) in leaves)
        {
            if (!Prefix(prefix, path)) continue;
            var current = value;
            for (var i = prefix.Count; i < path.Length; i++)
            {
                switch (current)
                {
                    case ComposedValue composed:
                        var rest = path.Skip(i).ToArray();
                        var part = composed.Leaves.FirstOrDefault(f => Prefix(f.Path, rest));
                        if (part.Value is null) return new ConstantValue(0, shape.Type, types.ValueWidth(shape.Type));
                        current = part.Value;
                        i += part.Path.Count - 1;
                        continue;
                    case ConstantValue { Bits: 0 }:
                        return new ConstantValue(0, shape.Type, types.ValueWidth(shape.Type));
                    case LocalValue or ArgumentValue or FieldValue or StaticFieldValue or ArrayElementValue or IndirectValue:
                        var field = path[i];
                        var type = field.DeclaringType is DefinitionRef owner ? field.Field.Type.Substitute(owner.Arguments, []) : field.Field.Type;
                        current = new FieldValue(current, field, type, types.ValueWidth(type));
                        continue;
                    default:
                        return null;
                }
            }
            return current;
        }
        return new ConstantValue(0, shape.Type, types.ValueWidth(shape.Type));
    }

    /// <summary>去掉值末尾的字段访问链 path，得到被访问的根；不是这条链时为 null。</summary>
    private static ManagedValue? Strip(ManagedValue value, IReadOnlyList<FieldRef> path)
    {
        for (var i = path.Count - 1; i >= 0; i--)
        {
            if (value is not FieldValue field || field.Field.Field != path[i].Field) return null;
            value = field.Receiver;
        }
        return value;
    }

    private static bool Bind(ManagedValue?[] binding, int index, ManagedValue value)
    {
        if (binding[index] is { } bound) return Cpp2CS.Managed.ManagedStructure.Value(bound, value);
        binding[index] = value;
        return true;
    }

    private static bool Prefix(IReadOnlyList<FieldRef> prefix, IReadOnlyList<FieldRef> path) =>
        prefix.Count <= path.Count && path.Take(prefix.Count).SequenceEqual(prefix);
}
