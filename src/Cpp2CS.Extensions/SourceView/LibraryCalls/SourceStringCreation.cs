using System.Reflection;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>IL2CPP 的字符串实例工厂转为公开构造；须证成忽略接收者并原样转调对应静态工厂。</summary>
internal static class SourceStringCreation
{
    internal static MethodRef? Constructor(ManagedBody body, ManagedTypes types)
    {
        var method = body.Method.Method;
        if (method.Owner != types.String.Definition || method.Name != "CreateString" || method.IsStatic
            || method.GenericParameters.Count != 0 || !method.ReturnType.Equals(types.String)) return null;
        var parameters = method.Parameters.Select(p => p.Type).ToArray();
        bool Character(TypeRef type) => ManagedTypes.PrimitiveName(type) == "Char";
        bool Characters(TypeRef type) => type is ArrayRef { IsVector: true } array && Character(array.Element);
        if (!(parameters is [var character, var count] && Character(character) && count.Equals(types.Int32)
            || parameters is [var array] && Characters(array)
            || parameters is [var chars, var start, var length] && Characters(chars) && start.Equals(types.Int32) && length.Equals(types.Int32))) return null;
        if (body.Regions.Count != 0 || body.Blocks is not [{ Statements: [ManagedCall { Tail: true, Result: null } call] }]
            || call.Invocation is not { Virtual: false, Receiver: null, Method.Method: var factory }
            || factory.Owner != method.Owner || factory.Name != "Ctor" || !factory.IsStatic || !factory.ReturnType.Equals(types.String)
            || !factory.Parameters.Select(p => p.Type).SequenceEqual(parameters) || call.Invocation.Arguments.Count != parameters.Length
            || call.Invocation.Arguments.Where((v, i) => v is not ArgumentValue a || a.Index != i || !a.Type.Equals(parameters[i])).Any()) return null;
        var constructor = method.Owner.Methods.SingleOrDefault(m => m.Name == ".ctor" && !m.IsStatic
            && (m.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public
            && m.Parameters.Select(p => p.Type).SequenceEqual(parameters));
        return constructor is null ? null : new(constructor, [], []);
    }

    internal static ManagedStatement Rewrite(ManagedCall call, MethodRef constructor)
    {
        // 丢弃接收者不能丢失加载、调用或其他可能抛出的求值。
        if (call.Invocation.Receiver is not (ArgumentValue or LocalValue or ConstantValue)
            || call.Invocation.Virtual || call.Invocation.Arguments.Count != constructor.Method.Parameters.Count) return call;
        var created = new NewObjectValue(constructor, call.Invocation.Arguments);
        return call.Tail ? new ManagedReturn(call.Address, created)
            : call.Result is { } result ? new ManagedAssignment(call.Address, result, created) : call;
    }
}

public sealed partial class SourceLibraryCalls
{
    private readonly Dictionary<MethodRef, MethodRef?> stringConstructors = [];

    private ManagedBody RewriteStringCreations(ManagedBody body) => body with
    {
        Blocks = body.Blocks.Select(block => block with
        {
            Statements = block.Statements.Select(statement =>
            {
                if (statement is not ManagedCall call || call.Invocation.Method.Method is not { Name: "CreateString" } method
                    || method.Owner != types.String.Definition) return statement;
                var factory = call.Invocation.Method;
                if (!stringConstructors.TryGetValue(factory, out var constructor))
                {
                    constructor = summaries.Find(new(factory, method.Address))?.Body is { } original
                        ? SourceStringCreation.Constructor(SourceRewriter.Rewrite(original, types), types) : null;
                    stringConstructors[factory] = constructor;
                }
                if (constructor is null) return statement;
                var rewritten = SourceStringCreation.Rewrite(call, constructor);
                if (rewritten != statement) Evidence.Add($"0x{body.Method.Method.Address:x}\t0x{call.Address:x}\t{body.Method}\t{constructor}");
                return rewritten;
            }).ToArray(),
        }).ToArray(),
    };
}
