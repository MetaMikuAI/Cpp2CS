using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery;

internal sealed class HostTyping(RecoveryScope host, TypingContext typing) : IExpressionTyping
{
    public TypeRef? TypeOf(Expr expression, TypeRef? hint = null)
    {
        host.Sync(typing.Solution);
        return host.Values.Recover(expression, hint).TryGet(out var value, out _) ? value.Type : null;
    }

    public TypeRef? LocationType(Expr address, int width)
    {
        host.Sync(typing.Solution);
        return host.Values.Location(address, width).TryGet(out var value, out _) ? value.Type : null;
    }

    public Expr Expand(Expr expression) => host.Values.Expand(expression);
    public IReadOnlyList<TypeRef>? StructReceiverArguments(Expr? receiver, TypeDef owner)
    {
        host.Sync(typing.Solution);
        return host.StructReceiverArguments(receiver, owner);
    }

    public IEnumerable<(Call Call, Use Klass)> TypeChecks() => host.State.Runtime.typeChecks.Keys.Where(c => c.Arguments.LastOrDefault() is Use).Select(c => (c, (Use)c.Arguments[^1])).ToArray();
}
