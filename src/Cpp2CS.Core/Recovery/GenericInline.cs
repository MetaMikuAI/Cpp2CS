using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>
/// 按普查建模的泛型内联被调方法：原生代码把它内联进调用方，二进制中没有调用方所需实例的独立代码。
/// 认回时取同一定义的任一实例的方法体做类型代换（ManagedTypeMap）；执行对照按普查的形态执行（tests 的 AwaiterCensus）。
/// </summary>
public static class GenericInline
{
    /// <summary>GetResult 只在结果不超过 16 字节（寄存器返回，AAPCS64 C.10–C.11）时建模；普查只对这一范围严格核对。</summary>
    public const int ResultLimit = 16;

    public static bool IsModeled(MethodDef method) => method is { Name: "get_IsCompleted" or "GetResult", IsStatic: false, Parameters.Count: 0 }
        && method.Owner is { Name: "Awaiter", DeclaringType.FullName: "Cysharp.Threading.Tasks.UniTask", GenericParameters.Count: 1 };
}
