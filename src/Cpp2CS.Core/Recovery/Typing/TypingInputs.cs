using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Typing;

internal sealed record EntryArgument(int Index, TypeRef Type, int Width);

/// <summary>
/// 已证明的非类型分析输入（ABI、配对、异常区域、删去的栈保存）。不含 known、runtime、resolved：这些由引擎产生；
/// 表达式的类型经 <see cref="Host"/> 由恢复器回答，内联、毒化与帧洞的规则因此只有一份。
/// </summary>
internal sealed class TypingInputs
{
    public required MethodRef Method { get; init; }
    public required Dictionary<Storage, EntryArgument> Arguments { get; init; }
    public required IReadOnlyDictionary<Storage, (ArgumentValue Root, AbiPiece Piece)> StructArguments { get; init; }
    public required IReadOnlySet<Stmt> Dropped { get; init; }
    /// <summary>已配对的栈实参与装箱写入；位置已被替换为局部变量，仍保留签名给出的类型。</summary>
    public required IReadOnlyDictionary<Store, TypeRef> StoredArguments { get; init; }
    public required IReadOnlyDictionary<Call, Variable> Constructed { get; init; }
    public required IReadOnlyDictionary<Call, DefinitionRef> DelegateCreations { get; init; }
    /// <summary>F5 异常值闭包（<see cref="Analysis.ExceptionValueClosure"/>）：wrapper 运行时引用与被捕获的异常对象。</summary>
    public required IReadOnlyDictionary<Variable, LocalValue> Wrappers { get; init; }
    public required IReadOnlyDictionary<Variable, LocalValue> Exceptions { get; init; }
    public required bool HasExceptions { get; init; }
    public required bool ReturnSupported { get; init; }
    public Func<Call, MethodRef, AbiValue, bool> UnusedInput { get; init; } = (_, _, _) => false;
    /// <summary>表达式定型服务：恢复器自己的 Recover 按引擎当前的解回答（MethodRecovery.HostTyping）。</summary>
    public required Func<TypingContext, IExpressionTyping> Host { get; init; }

    public IExpressionTyping Expressions(TypingContext context) => Host(context);
}
