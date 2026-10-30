using Cpp2CS.Input;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Tests;

/// <summary>T3 类型推断引擎的求解语义：用核心库真实的类型层次检查最小公共超类、上下界、冲突与运行时引用。</summary>
internal static class TypingCheck
{
    [Command("typing", "T3 类型推断引擎的求解语义（核心库真实类型层次）", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var a = new Assertions();
        DefinitionRef Corlib(string name) => new(types.CorlibDefinition(name) ?? throw new InvalidDataException(name), []);
        var exception = Corlib("System.Exception");
        var argument = Corlib("System.ArgumentException");
        var argumentNull = Corlib("System.ArgumentNullException");
        var invalidOperation = Corlib("System.InvalidOperationException");
        var system = Corlib("System.SystemException");
        var e = new TypeEvidence("测试", 0, "");
        Variable V(int i) => new(Storage.Gpr(i), 1);

        a.Equal<TypeRef?>(argument, TypeSolver.Join(types, argumentNull, argument), "ArgumentNullException ∨ ArgumentException");
        a.Equal<TypeRef?>(system, TypeSolver.Join(types, argument, invalidOperation), "ArgumentException 与 InvalidOperationException 的最小公共超类是 SystemException");
        // 整数与 bool 是同一种类：汇合取与顺序无关的代表（整数优先、位宽大者、有符号者）；浮点与整数没有公共类型。
        var uint32 = types.Integer(32, false);
        a.Equal<TypeRef?>(types.Int64, TypeSolver.Join(types, types.Int32, types.Int64), "Int32 ⊔ Int64 取位宽大者");
        a.Equal<TypeRef?>(types.Int64, TypeSolver.Join(types, types.Int64, types.Int32), "汇合与顺序无关");
        a.Equal<TypeRef?>(types.Int32, TypeSolver.Join(types, uint32, types.Int32), "同宽时取有符号者");
        a.Equal<TypeRef?>(uint32, TypeSolver.Join(types, types.Boolean, uint32), "bool ⊔ 整数取整数");
        var single = Corlib("System.Single");
        a.Equal<TypeRef?>(null, TypeSolver.Join(types, single, types.Int32), "浮点与整数没有公共类型");

        var c = new TypeConstraints();
        c.Defines(V(0), argumentNull, e);                       // φ(v0, v1) 的两个来源
        c.Defines(V(1), invalidOperation, e);
        c.Flows(V(0), V(2), e);
        c.Flows(V(1), V(2), e);
        c.Requires(V(3), argument, e);                         // 只有使用：取最具体者
        c.Requires(V(3), exception, e);
        c.Defines(V(4), exception, e);                         // 下界不能当作更具体的类型使用
        c.Requires(V(4), argument, e);
        c.IsRuntime(V(5), new("klass"), e);                    // 运行时引用与托管使用冲突
        c.Requires(V(5), types.Object, e);
        c.IsRuntime(V(6), new("klass"), e);
        c.Defines(V(8), types.Int64, e);                       // 64 位定义当作 uint、bool 使用：投影，不冲突
        c.Requires(V(8), uint32, e);
        c.Requires(V(8), types.Boolean, e);
        c.Defines(V(9), types.Int32, e);                       // 整数定义当作浮点使用：冲突
        c.Requires(V(9), single, e);
        c.IsClobbered(V(10), e);                               // 破坏值：不看其余约束，也不向 φ 传播
        c.Requires(V(10), types.Int32, e);
        c.Flows(V(10), V(11), e);
        c.Defines(V(12), types.Boolean, e);
        c.Flows(V(10), V(13), e);
        c.Flows(V(12), V(13), e);
        c.Requires(V(14), uint32, e);                          // 只有整数使用：取代表
        c.Requires(V(14), types.Int32, e);
        var disposable = Corlib("System.IDisposable");                // φ 汇合两个实现同一接口的类，使用要求该接口
        var stream = Corlib("System.IO.Stream");
        var reader = Corlib("System.IO.TextReader");
        c.Defines(V(15), stream, e);
        c.Defines(V(16), reader, e);
        c.Flows(V(15), V(17), e);
        c.Flows(V(16), V(17), e);
        c.Requires(V(17), disposable, e);
        c.Defines(V(18), stream, e);                                 // 不满足使用、也没有接口上界：冲突，但保留下界
        c.Requires(V(18), argument, e);
        var s = TypeSolver.Solve(c, types);
        a.Equal<TypeResult?>(new ManagedResult(system), s.GetValueOrDefault(V(2)), "φ 取来源的最小公共超类");
        a.Equal<TypeResult?>(new ManagedResult(argument), s.GetValueOrDefault(V(3)), "只有使用时取能满足全部使用的最具体类型");
        a.True(s.GetValueOrDefault(V(4)) is ConflictResult, "下界 Exception 不能当作 ArgumentException 使用");
        a.True(s.GetValueOrDefault(V(5)) is ConflictResult, "运行时引用不能当作托管值使用");
        a.Equal<TypeResult?>(new RuntimeResult(new("klass")), s.GetValueOrDefault(V(6)), "单独的运行时引用");
        a.True(!s.ContainsKey(V(7)), "没有约束的变量没有结果");
        a.Equal<TypeResult?>(new ManagedResult(types.Int64), s.GetValueOrDefault(V(8)), "整数定义可投影到更窄的整数与 bool 使用");
        a.True(s.GetValueOrDefault(V(9)) is ConflictResult, "整数定义不能当作浮点使用");
        a.True(s.GetValueOrDefault(V(10)) is ClobberedResult, "破坏值即使被要求类型也仍是破坏值");
        a.True(!s.ContainsKey(V(11)) || s[V(11)] is not ManagedResult, "破坏值不向流的目标传播下界");
        a.Equal<TypeResult?>(new ManagedResult(types.Boolean), s.GetValueOrDefault(V(13)), "φ 的破坏来源不参与汇合");
        a.Equal<TypeResult?>(new ManagedResult(types.Int32), s.GetValueOrDefault(V(14)), "只有整数使用时取与顺序无关的代表");
        a.Equal<TypeResult?>(new ManagedResult(disposable), s.GetValueOrDefault(V(17)), "公共超类 object 不满足使用时，取各定义都能赋给的接口");
        a.True(s.GetValueOrDefault(V(18)) is ConflictResult { Lower: var lower } && stream.Equals(lower), "冲突结果带着下界，供下一轮推导");
        var block = new Block(0x1000) { Statements = Enumerable.Range(0, 24)
            .Select(i => (Stmt)new Define((ulong)(0x1000 + i * 4), new(Storage.Temp(i), 1), Expr.C(0, 32))).ToList() };
        var function = new MachineFunction { Entry = block.Start, Blocks = [block],
            Range = new(0x1000, 0x1060, CodeRegion.Managed, BoundaryEvidence.EhFrame) };
        TypingContext Context() => new(function, types, new Dictionary<Storage, TypeRef>(), _ => null);
        var chain = new TypeEngine([new DelayedTypes(false)]).Run(Context());
        a.True(chain.Converged && chain.Rounds == 25 && chain.Solution.Count == 24, "长表达式依赖链可超过固定 16 轮");
        a.True(!new TypeEngine([new DelayedTypes(false)], maxRounds: 16).Run(Context()).Converged, "显式预算仍保留未收敛诊断");
        var cycle = new TypeEngine([new DelayedTypes(true)]).Run(Context());
        a.True(!cycle.Converged && cycle.Rounds == 3, "真正的循环不会因增加预算而伪装收敛");
        return a.Finish("typing");
    }

    private sealed class DelayedTypes(bool cycle) : ITypeContributor
    {
        public string Name => "延迟表达式";
        public void Contribute(TypingContext context, TypeConstraints constraints)
        {
            foreach (var definition in context.Statements.OfType<Define>())
            {
                var index = definition.Target.Storage.Index;
                var type = cycle ? context.TypeOf(definition.Target) == context.Types.Int32 ? context.Types.Int64 : context.Types.Int32
                    : index == 0 ? context.Types.Int32 : context.TypeOf(new(Storage.Temp(index - 1), 1));
                if (type is not null) constraints.Defines(definition.Target, type, new(Name, definition.Address, "依赖上一轮"));
            }
        }
    }
}
