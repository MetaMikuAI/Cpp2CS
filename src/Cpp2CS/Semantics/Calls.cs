using Cpp2CS.Metadata;

namespace Cpp2CS.Semantics;

/// <summary>托管调用身份独立于原生地址；共享地址不能隐式选择某个方法。</summary>
public sealed record MethodKey(string Assembly, string Owner, string Token);
public sealed record CallTarget(MethodKey Key, TypeModel Owner, Method Method);
public sealed record Invocation(CallTarget Target, Value? Receiver, Value[] Arguments) : Value(Target.Method.ReturnType);
public sealed record AddressOf(Value Storage) : Value(Storage.Type + "&");
public sealed record Evaluate(Origin Source, Invocation Invocation) : Statement(Source);
public sealed record InitializeValue(Origin Source, CallTarget Target, Value Storage, Value[] Arguments) : Statement(Source);

public sealed class CallTargets
{
    readonly Dictionary<string, CallTarget[]> byAddress;
    public CallTargets(Catalog catalog)
    {
        byAddress = catalog.Types.SelectMany(t => t.Methods.Select(m =>
                new CallTarget(new(t.Assembly ?? catalog.Assembly, t.Name, m.Token), t, m)))
            .GroupBy(m => m.Method.Address, StringComparer.OrdinalIgnoreCase)
            .ToDictionary(g => g.Key, g => g.ToArray(), StringComparer.OrdinalIgnoreCase);
    }

    public CallTarget Resolve(string address, MethodKey? identity = null)
    {
        if (!byAddress.TryGetValue(address, out var candidates))
            throw new NotSupportedException($"调用依赖没有声明: {address}");
        var matches = identity is null ? candidates : candidates.Where(c => c.Key == identity).ToArray();
        if (matches.Length != 1)
            throw new NotSupportedException($"调用身份不唯一或不匹配: {address}, {identity}");
        return matches[0];
    }
}

/// <summary>从已恢复方法遍历调用闭包；依赖缺失会阻止输出，而不是自动变成宿主替身。</summary>
public static class Dependencies
{
    public static CallTarget[] In(Body body)
    {
        var targets = new Dictionary<MethodKey, CallTarget>();
        void Value(Value value)
        {
            switch (value)
            {
                case Invocation call:
                    targets[call.Target.Key] = call.Target;
                    if (call.Receiver is not null) Value(call.Receiver);
                    foreach (var argument in call.Arguments) Value(argument);
                    break;
                case AddressOf address: Value(address.Storage); break;
                case Conversion conversion: Value(conversion.Operand); break;
                case Binary binary: Value(binary.Left); Value(binary.Right); break;
                case Unary unary: Value(unary.Operand); break;
                case Choice choice: Value(choice.Condition); Value(choice.True); Value(choice.False); break;
            }
        }
        void Statements(IEnumerable<Statement> statements)
        {
            foreach (var s in statements)
                switch (s)
                {
                    case Store store: Value(store.Target); Value(store.Value); break;
                    case PackedStore store: Value(store.Value); break;
                    case Return { Value: not null } ret: Value(ret.Value); break;
                    case If branch: Value(branch.Condition); Statements(branch.True); Statements(branch.False); break;
                    case Evaluate effect: Value(effect.Invocation); break;
                    case InitializeValue initialize:
                        targets[initialize.Target.Key] = initialize.Target;
                        foreach (var arg in initialize.Arguments) Value(arg);
                        break;
                    case ControlFlow flow:
                        foreach (var block in flow.Blocks)
                        {
                            Statements(block.Effects);
                            switch (block.Transfer)
                            {
                                case Branch branch: Value(branch.Condition); break;
                                case Select select: Value(select.Value); break;
                                case Finish { Value: not null } finish: Value(finish.Value); break;
                            }
                        }
                        break;
                }
        }
        Statements(body.Statements);
        return targets.Values.ToArray();
    }

    public static void Verify(Catalog catalog, IReadOnlyDictionary<string, Body[]> bodies)
    {
        var available = bodies.SelectMany(t => t.Value.Select(b =>
            new MethodKey(catalog.Type(t.Key).Assembly ?? catalog.Assembly, t.Key, b.Method.Token))).ToHashSet();
        foreach (var body in bodies.Values.SelectMany(b => b))
            foreach (var target in In(body))
                if (!available.Contains(target.Key))
                    throw new InvalidOperationException($"缺少已恢复的调用依赖: {target.Key}");
    }
}
