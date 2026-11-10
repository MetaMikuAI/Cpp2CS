namespace Cpp2CS.Recovery.Inlining;

/// <summary>内联证明的调试输出（inspect --inline）：证明前的方法体与每次尝试的结果。只在本线程设置时输出。</summary>
public static class InlineTrace
{
    [ThreadStatic] private static Action<string>? sink;
    [ThreadStatic] private static Action<Cpp2CS.Managed.ManagedBody>? before;
    [ThreadStatic] private static Cpp2CS.Model.MethodDef? method;

    public static Action<string>? Sink { get => sink; set => sink = value; }
    public static Action<Cpp2CS.Managed.ManagedBody>? Before { get => before; set => before = value; }

    /// <summary>只输出这个方法的证明（恢复模板时递归恢复的方法不输出）。</summary>
    public static Cpp2CS.Model.MethodDef? Method { get => method; set => method = value; }

    [ThreadStatic] private static Action<Cpp2CS.Managed.ManagedBody>? print;
    [ThreadStatic] private static HashSet<Cpp2CS.Model.MethodRef>? printed;

    /// <summary>打印方法体（用于输出用到的模板，每个模板一次）。</summary>
    public static Action<Cpp2CS.Managed.ManagedBody>? Print { get => print; set { print = value; printed = null; } }

    internal static void Template(Cpp2CS.Model.MethodDef caller, Cpp2CS.Managed.ManagedBody body)
    {
        if (!For(caller) || print is null || !(printed ??= []).Add(body.Method)) return;
        Write($"  -- 模板 {body.Method}");
        print(body);
    }

    [ThreadStatic] private static Func<Cpp2CS.Managed.ManagedBody, IEnumerable<string>>? lines;

    /// <summary>方法体的可读行（诊断用，由 inspect 设置）。</summary>
    public static Func<Cpp2CS.Managed.ManagedBody, IEnumerable<string>>? Lines { get => lines; set => lines = value; }

    internal static bool For(Cpp2CS.Model.MethodDef caller) => sink is not null && ReferenceEquals(caller, method);
    internal static void Write(string line) => sink?.Invoke(line);
}
