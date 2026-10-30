using Cpp2CS.Ir;

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
        var definitions = context.Statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        var loads = context.Statements.OfType<Define>().Where(d => d.Value is Load { Width: 64, Address: Use }).ToDictionary(d => d.Target, d => ((Load)d.Value).Address);
        foreach (var define in context.Statements.OfType<Define>())
        {
            // 标量 FMOV 写入浮点寄存器；结构体片投影可能已经返回对应的 float/double 叶子。
            var projected = define.Target.Storage.Bank == Bank.Vec && define.Value is
                Ir.Convert { Kind: ConvKind.Bitcast, Width: 32 or 64 } or Load { Width: 32 or 64 }
                ? expressions.TypeOf(define.Value, define.Value.Width == 32 ? context.Types.Single : context.Types.Double) : null;
            if (!context.IsRuntime(define.Target) && (SealedCast(loads, define.Value) ?? projected ?? TypeOfDefinition(expressions, define.Value, definitions)) is { } type)
                constraints.Defines(define.Target, type, new(Name, define.Address, $"{define.Value} : {type}"));
        }
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
    private static TypeRef? TypeOfDefinition(IExpressionTyping expressions, Expr e, Dictionary<Variable, Expr> definitions) => e switch
    {
        _ when ConstantLeaves(e, definitions, []) => null,
        Select s when ConstantLeaves(s.True, definitions, []) => TypeOfDefinition(expressions, s.False, definitions),
        Select s when ConstantLeaves(s.False, definitions, []) => TypeOfDefinition(expressions, s.True, definitions),
        _ => expressions.TypeOf(e),
    };

    private static bool ConstantLeaves(Expr e, Dictionary<Variable, Expr> definitions, HashSet<Variable> active)
    {
        if (e is Const) return true;
        if (e is Select s) return ConstantLeaves(s.True, definitions, active) && ConstantLeaves(s.False, definitions, active);
        if (e is not Use use || !active.Add(use.Variable) || !definitions.TryGetValue(use.Variable, out var value)) return false;
        var result = value.Width == use.Width && ConstantLeaves(value, definitions, active);
        active.Remove(use.Variable);
        return result;
    }
}
