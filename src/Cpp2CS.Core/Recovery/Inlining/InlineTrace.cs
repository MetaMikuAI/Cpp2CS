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

    internal static bool For(Cpp2CS.Model.MethodDef caller) => sink is not null && ReferenceEquals(caller, method);
    internal static void Write(string line) => sink?.Invoke(line);
}
