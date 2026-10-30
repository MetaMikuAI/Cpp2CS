using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>
/// 贡献者需要的表达式定型服务：按上一轮的解回答表达式、访存位置的类型，以及运行时引用的展开与已证明的类型检查。
/// 恢复器自身实现它（<see cref="MethodRecovery"/>），同一套 Recover 规则既用于定型也用于写出。
/// </summary>
public interface IExpressionTyping
{
    TypeRef? TypeOf(Expr expression, TypeRef? hint = null);
    TypeRef? LocationType(Expr address, int width);
    Expr Expand(Expr expression);
    IReadOnlyList<TypeRef>? StructReceiverArguments(Expr? receiver, TypeDef owner);
    IEnumerable<(Call Call, Use Klass)> TypeChecks();
}
