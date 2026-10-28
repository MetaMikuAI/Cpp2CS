using Cpp2CS.Recovery;

namespace Cpp2CS.Analysis;

/// <summary>比较结构内容；集合实例变化不代表 IR 变化。</summary>
public static class ManagedStructure
{
    private static bool Sequence<T>(IEnumerable<T> left, IEnumerable<T> right, Func<T, T, bool> same)
    {
        using var a = left.GetEnumerator();
        using var b = right.GetEnumerator();
        while (a.MoveNext())
            if (!b.MoveNext() || !same(a.Current, b.Current)) return false;
        return !b.MoveNext();
    }

    public static bool Same(ManagedBody a, ManagedBody b) => a.Method.Equals(b.Method)
        && Sequence(a.Regions, b.Regions, (x, y) => x.Kind == y.Kind && Equals(x.Exception, y.Exception) && Equals(x.CatchType, y.CatchType)
            && x.HandlerEntry == y.HandlerEntry && x.Try.SequenceEqual(y.Try) && x.Handler.SequenceEqual(y.Handler))
        && Sequence(a.Blocks, b.Blocks, (x, y) => x.Address == y.Address && Sequence(x.Statements, y.Statements, Same));

    private static bool Edge(ManagedEdge a, ManagedEdge b) => a.Target == b.Target
        && Sequence(a.Copies, b.Copies, (x, y) => x.Target.Equals(y.Target) && Value(x.Value, y.Value));

    public static bool Same(ManagedStatement a, ManagedStatement b) => a.Address == b.Address && (a, b) switch
    {
        (ManagedAssignment x, ManagedAssignment y) => x.Target.Equals(y.Target) && Value(x.Value, y.Value),
        (ManagedStore x, ManagedStore y) => Value(x.Target, y.Target) && Value(x.Value, y.Value),
        (ManagedCall x, ManagedCall y) => x.Tail == y.Tail && x.Inlined == y.Inlined && Equals(x.Result, y.Result)
            && x.Invocation.Method.Equals(y.Invocation.Method) && x.Invocation.Virtual == y.Invocation.Virtual
            && Value(x.Invocation.Receiver, y.Invocation.Receiver) && Sequence(x.Invocation.Arguments, y.Invocation.Arguments, Value),
        (ManagedReturn x, ManagedReturn y) => Value(x.Value, y.Value),
        (ManagedJump x, ManagedJump y) => Edge(x.Edge, y.Edge),
        (ManagedBranch x, ManagedBranch y) => Value(x.Condition, y.Condition) && Edge(x.Taken, y.Taken) && Edge(x.Fallthrough, y.Fallthrough),
        (ManagedSwitch x, ManagedSwitch y) => Value(x.Index, y.Index) && Sequence(x.Cases, y.Cases, Edge),
        (ManagedThrow x, ManagedThrow y) => Value(x.Exception, y.Exception),
        (ManagedCheck x, ManagedCheck y) => x.Exception.Equals(y.Exception) && Value(x.Condition, y.Condition),
        (ManagedAwait x, ManagedAwait y) => Equals(x.Result, y.Result) && Value(x.Task, y.Task),
        _ => a.Equals(b),
    };

    private static bool Value(ManagedValue? a, ManagedValue? b)
    {
        if (ReferenceEquals(a, b)) return true;
        if (a is null || b is null || a.GetType() != b.GetType() || a.Width != b.Width || !a.Type.Equals(b.Type)) return false;
        if (!Sequence(ManagedValues.Children(a), ManagedValues.Children(b), Value)) return false;
        return (a, b) switch
        {
            (NewObjectValue x, NewObjectValue y) => x.Constructor.Equals(y.Constructor) && x.Transparent == y.Transparent,
            (ComposedValue x, ComposedValue y) => Sequence(x.Leaves, y.Leaves, (l, r) => l.Path.SequenceEqual(r.Path)),
            _ => ManagedValues.Map(a, Empty).Equals(ManagedValues.Map(b, Empty)),
        };
    }

    private static ManagedValue Empty(ManagedValue value) => new ConstantValue(0, value.Type, value.Width);
}
