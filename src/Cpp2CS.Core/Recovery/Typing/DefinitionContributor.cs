using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Typing;

/// <summary>
/// 定义侧表达式的类型。裸常量、以及各分支都是常量的选择，由使用处决定（例如浮点的位模式常量）；一臂是常量的选择取另一臂的类型，
/// 不以默认整数类型抢占 null 或浮点的证据；旧 InferUseTypes 的 FloatingChoice 也是用使用处的浮点类型覆盖它们。
/// </summary>
internal sealed class DefinitionContributor(TypingInputs input) : ITypeContributor
{
    public string Name => "表达式";
    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        var expressions = input.Expressions(context);
        var loads = context.Statements.OfType<Define>().Where(d => d.Value is Load { Width: 64, Address: Use }).ToDictionary(d => d.Target, d => ((Load)d.Value).Address);
        foreach (var define in context.Statements.OfType<Define>())
            if (!context.IsRuntime(define.Target) && (SealedCast(loads, define.Value) ?? TypeOfDefinition(expressions, define.Value)) is { } type)
                constraints.Defines(define.Target, type, new(Name, define.Address, $"{define.Value} : {type}"));
    }

    /// <summary>klass(obj) == Class&lt;T&gt;（T sealed）? obj : null 是 obj as T，类型为 T（见 MethodRecovery.PrepareSealedChecks）。</summary>
    private static TypeRef? SealedCast(Dictionary<Variable, Expr> loads, Expr e)
    {
        if (e is not Select { Condition: Compare { Cond: Cond.Eq } c, False: Const { Value: 0 }, True: Use obj }) return null;
        var (klass, symbol) = (c.Left, c.Right) is (Use u, Symbol s) ? (u, s) : (c.Right, c.Left) is (Use v, Symbol t) ? (v, t) : (null, null);
        if (klass is null || symbol is not { Kind: SymbolKind.Class, Value: DefinitionRef type } || type.Definition.IsInterface || type.Definition.IsValueType
            || (type.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) == 0) return null;
        return loads.TryGetValue(klass.Variable, out var address) && address == obj ? type : null;
    }

    /// <summary>常量没有自己的类型：选择的一臂是常量时，取另一臂的类型（例如 c ? 0x3f800000 : f 是 float，不是 int）。</summary>
    private static TypeRef? TypeOfDefinition(IExpressionTyping expressions, Expr e) => e switch
    {
        _ when ConstantLeaves(e) => null,
        Select s when ConstantLeaves(s.True) => TypeOfDefinition(expressions, s.False),
        Select s when ConstantLeaves(s.False) => TypeOfDefinition(expressions, s.True),
        _ => expressions.TypeOf(e),
    };

    private static bool ConstantLeaves(Expr e) => e is Const || e is Select s && ConstantLeaves(s.True) && ConstantLeaves(s.False);
}
