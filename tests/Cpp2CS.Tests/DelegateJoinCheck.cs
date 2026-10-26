using System.Reflection;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class DelegateJoinCheck
{
    [Command("delegate-joins", "委托条件选择与循环合并的引用类型来源", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        TypeRef Type(int index, string name) => new DefinitionRef(new TypeDef { Index = index, Assembly = "Join.Tests.dll",
            Namespace = "Tests", Name = name, Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false }, []);
        var action = Type(0, "Action"); var other = Type(1, "Other");
        var initial = new Variable(Storage.Gpr(19), 1); var merged = new Variable(Storage.Gpr(19), 2);
        var chosen = new Variable(Storage.Gpr(19), 3); var loaded = new Variable(Storage.Gpr(20), 1);
        var unknown = new Variable(Storage.Gpr(21), 1);
        Expr Use(Variable variable) => new Use(variable, 64);
        var definitions = new Dictionary<Variable, Expr> { [initial] = Expr.C(0, 64),
            [chosen] = new Select(Expr.C(1, 1), Use(merged), Use(loaded), 64) };
        var phis = new Dictionary<Variable, Phi> { [merged] = new(0, merged, [initial, chosen]) };
        TypeRef? Resolve(Expr expression) => expression == Use(loaded) ? action : null;
        TypeRef? Join(Expr expression, Func<Expr, TypeRef?>? resolve = null) =>
            DelegateCallNormalizer.JoinedReferenceType([expression], definitions, phis, resolve ?? Resolve);
        a.Equal(action, Join(Use(chosen)), "循环中已知 Action 与初始 null 合并为 Action");
        a.Equal(action, Join(Use(merged)), "从循环 phi 入口追溯得到同一类型");
        phis[merged] = new(0, merged, [chosen]);
        a.Equal(action, Join(Use(merged)), "循环外存在确定来源，不依赖初始 null");
        definitions[chosen] = Use(merged);
        a.True(Join(Use(merged)) is null, "纯循环没有类型证据");
        definitions[chosen] = new Select(Expr.C(1, 1), Use(loaded), Use(unknown), 64);
        a.True(Join(Use(chosen)) is null, "未知非空来源不能丢弃");
        a.True(Join(Use(chosen), e => e == Use(loaded) ? action : other) is null, "不同引用类型不能任取其一");
        a.True(Join(Expr.C(0, 64)) is null, "只有 null 不能推定委托类型");
        a.True(Join(Expr.C(1, 64)) is null, "非零整数不是引用证据");
        return a.Finish("delegate-joins");
    }
}
