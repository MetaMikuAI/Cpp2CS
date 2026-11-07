namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 运行时库和引擎里方法体就是读取一个字段的公开访问器。IL2CPP 总是把它们内联，没有原生入口，访问器的证明拿不到恢复体；
/// 这里按库的源码给出方法体（.NET 的 Nullable&lt;T&gt;、TaskCompletionSource&lt;T&gt;、ConfiguredTaskAwaitable，
/// Unity 的 Ray、Ray2D、NativeArray&lt;T&gt;）。只用于读取：这些类型的 setter 不止写字段（如 Ray.direction 会归一化）。
/// </summary>
internal static class LibraryAccessors
{
    private static readonly HashSet<(string Type, string Method, string Field)> Reads =
    [
        ("System.Nullable", "get_HasValue", "hasValue"),
        ("System.Nullable", "GetValueOrDefault", "value"),
        ("System.Threading.Tasks.TaskCompletionSource", "get_Task", "_task"),
        ("System.Runtime.CompilerServices.ConfiguredTaskAwaitable", "GetAwaiter", "m_configuredTaskAwaiter"),
        ("UnityEngine.Ray", "get_origin", "m_Origin"),
        ("UnityEngine.Ray", "get_direction", "m_Direction"),
        ("UnityEngine.Ray2D", "get_origin", "m_Origin"),
        ("UnityEngine.Ray2D", "get_direction", "m_Direction"),
        ("Unity.Collections.NativeArray", "get_Length", "m_Length"),
    ];

    /// <summary>没有参数的实例方法，按库的源码只返回接收者的这个字段。</summary>
    public static bool IsRead(MethodDef method, FieldDef field) =>
        !method.IsStatic && method.Parameters.Count == 0 && method.Owner == field.Owner
        && Reads.Contains((method.Owner.FullName, method.Name, field.Name));
}
