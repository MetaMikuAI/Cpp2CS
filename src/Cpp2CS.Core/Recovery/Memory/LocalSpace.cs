namespace Cpp2CS.Recovery.Memory;

public enum LocalKind : byte { Frame, Result, Argument, Dynamic }

/// <summary>
/// 方法私有的一段内存：本方法的栈帧（偏移相对入口 SP，非负部分是栈传入的实参），
/// 调用者提供的结果缓冲区，按副本传入的实参（Argument 为参数序号），或动态分配的不透明局部（Site 为分配点，Element 为类型）。
/// </summary>
public readonly record struct LocalSpace(LocalKind Kind, int Argument = 0, ulong Site = 0, TypeRef? Element = null)
{
    public static readonly LocalSpace Frame = new(LocalKind.Frame);
    public static readonly LocalSpace Result = new(LocalKind.Result);
    public static LocalSpace Copy(int argument) => new(LocalKind.Argument, argument);
    public static LocalSpace Dynamic(ulong site, TypeRef element) => new(LocalKind.Dynamic, 0, site, element);

    public override string ToString() => Kind switch
    {
        LocalKind.Frame => "frame",
        LocalKind.Result => "result",
        LocalKind.Dynamic => $"alloca@{Site:x}",
        _ => $"copy{Argument}",
    };
}
