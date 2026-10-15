using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Ssa;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class ControlFlowCheck
{
    private static readonly Variable X = new(Storage.Gpr(0), 0);
    private static readonly Variable Y = new(Storage.Gpr(1), 0);
    private static readonly Variable Merged = new(Storage.Gpr(2), 1);
    private static Expr Condition => new Compare(Cond.Eq, new Use(X, 64), Expr.C(0, 64));

    public static int Run(string? binary, string? metadata)
    {
        var samples = new ulong[] { 0, 1, 7, uint.MaxValue, 0x1_0000_0000, 0x8000_0000_0000_0000, ulong.MaxValue };
        var checkedInputs = 0;
        void Check(string name, Func<MachineFunction> make, bool changed)
        {
            var before = make(); var after = make();
            Require(ControlFlow.Simplify(after) == changed, name + " 的改写条件");
            Settle(after);
            Require(!ControlFlow.Simplify(after), name + " 的结果稳定");
            Require(SsaCheck.Verify(after, Dominators.Compute(after)).Count == 0, name + " 的 SSA 不变量");
            foreach (var a in samples)
            foreach (var b in samples)
            {
                Require(EdgeConstantsCheck.Execute(before, X, a, Y, b) == EdgeConstantsCheck.Execute(after, X, a, Y, b), name + " 的前后执行结果");
                checkedInputs++;
            }
        }
        Check("相同目标不同 φ 值", () => Parallel(Condition), false);
        Check("相同目标相同 φ 值", () => Parallel(Condition, same: true), true);
        Check("重边保留跳转侧", () => Parallel(Expr.C(1, 1)), true);
        Check("重边保留顺序侧", () => Parallel(Expr.C(0, 1)), true);
        Check("折叠常量比较", () => Parallel(new Compare(Cond.Eq, Expr.C(42, 64), Expr.C(42, 64))), true);
        Check("空侧 φ 相同", () => Diamond(Condition, same: true), true);
        Check("空侧 φ 不同", () => Diamond(Condition), false);
        Check("常量跳过空侧", () => Diamond(Expr.C(1, 1)), true);
        Check("常量保留空侧", () => Diamond(Expr.C(0, 1)), true);
        Check("多轮传播与不可达输入清理", Cascade, true);
        var loopBefore = Loop(); var loopAfter = Loop(); Settle(loopAfter);
        Require(SsaCheck.Verify(loopAfter, Dominators.Compute(loopAfter)).Count == 0, "循环传播后的 SSA 不变量");
        for (ulong count = 1; count <= 20; count++)
        {
            Require(EdgeConstantsCheck.Execute(loopBefore, X, count, Y, 0) == EdgeConstantsCheck.Execute(loopAfter, X, count, Y, 0), "回边和退出边保持执行结果");
            checkedInputs++;
        }

        foreach (var condition in new Expr[] { new Compare(Cond.Ne, new Load(Expr.C(0, 64), 64), Expr.C(0, 64)), new Intrinsic("observable", [], 1) })
            Require(!ControlFlow.Simplify(Parallel(condition, same: true)), "不能丢掉条件中的内存读取或未知 intrinsic");
        var effect = Diamond(Condition, same: true);
        effect.Blocks.Single(b => b.Start == 0x2000).Statements.Insert(0, new Call(0x2000, CallKind.Direct, Expr.C(0x9000, 64)));
        Require(!ControlFlow.Simplify(effect), "不能丢掉侧路径中的调用");
        var landing = Diamond(Condition, same: true);
        landing.Blocks.Single(b => b.Start == 0x2000).IsLandingPad = true;
        Require(!ControlFlow.Simplify(landing), "不能把落地块当成普通空块");
        var exceptional = Parallel(Expr.C(0, 1));
        var entry = exceptional.EntryBlock; var join = exceptional.Blocks.Single(b => b.Start == 0x3000);
        var other = new Variable(Storage.Gpr(3), 0);
        entry.Successors.Add(join); entry.Handler = join; join.Predecessors.Add(entry);
        join.Statements[0] = ((Phi)join.Statements[0]) with { Sources = [X, Y, other] };
        Require(ControlFlow.Simplify(exceptional) && entry.Handler == join && entry.Successors.Count == 2
            && ((Phi)join.Statements[0]).Sources.SequenceEqual([Y, other]), "同目标的异常边及其 φ 来源保留");
        MachineFunction.RemoveEdgeAt(entry, 1);
        Require(entry.Handler is null && entry.Successors.Single() == join && ((Phi)join.Statements[0]).Sources.SequenceEqual([Y]),
            "删除异常边时保留同目标正常边");
        Require(SsaCheck.Verify(exceptional, Dominators.Compute(exceptional)).Count == 0, "重边删除后的 SSA 不变量");
        Console.WriteLine($"控制流差分检查通过：{checkedInputs} 组输入，含常量、多轮传播、重边 φ、条件读取、侧路径调用和异常边");
        if (binary is not null && metadata is not null) Native(new RecoverySession(ModelCheck.Load(binary, metadata)));
        return 0;
    }

    private static MachineFunction Parallel(Expr condition, bool same = false) => EdgeConstantsCheck.Graph(
        new Block(0x1000) { Statements = [new Branch(0x1000, condition, 0x3000, 0x3000)] },
        new Block(0x3000) { Statements = [new Phi(0x3000, Merged, [X, same ? X : Y]), new Return(0x3004) { Value = new Use(Merged, 64) }] });

    private static MachineFunction Diamond(Expr condition, bool same = false) => EdgeConstantsCheck.Graph(
        new Block(0x1000) { Statements = [new Branch(0x1000, condition, 0x3000, 0x2000)] },
        new Block(0x2000) { Statements = [new Jump(0x2000, 0x3000)] },
        new Block(0x3000) { Statements = [new Phi(0x3000, Merged, [X, same ? X : Y]), new Return(0x3004) { Value = new Use(Merged, 64) }] });

    private static MachineFunction Cascade()
    {
        var a = new Variable(Storage.Temp(0), 1); var b = new Variable(Storage.Temp(1), 1);
        return EdgeConstantsCheck.Graph(
            new Block(0x1000) { Statements = [new Branch(0x1000, Expr.C(1, 1), 0x2000, 0x2100)] },
            new Block(0x2000) { Statements = [new Define(0x2000, a, Expr.C(0, 64)), new Jump(0x2004, 0x3000)] },
            new Block(0x2100) { Statements = [new Define(0x2100, b, Expr.C(1, 64)), new Jump(0x2104, 0x3000)] },
            new Block(0x3000) { Statements = [new Phi(0x3000, Merged, [a, b]),
                new Branch(0x3004, new Compare(Cond.Eq, new Use(Merged, 64), Expr.C(0, 64)), 0x3100, 0x3200)] },
            new Block(0x3100) { Statements = [new Return(0x3100) { Value = new Use(X, 64) }] },
            new Block(0x3200) { Statements = [new Return(0x3200) { Value = new Use(Y, 64) }] });
    }

    private static MachineFunction Loop()
    {
        var next = new Variable(Storage.Temp(0), 1);
        return EdgeConstantsCheck.Graph(
            new Block(0x1000) { Statements = [new Jump(0x1000, 0x2000)] },
            new Block(0x2000) { Statements = [new Phi(0x2000, Merged, [X, next]),
                new Define(0x2004, next, new Binary(BinOp.Sub, new Use(Merged, 64), Expr.C(1, 64), 64)),
                new Branch(0x2008, new Compare(Cond.Ne, new Use(next, 64), Expr.C(0, 64)), 0x2000, 0x3000)] },
            new Block(0x3000) { Statements = [new Return(0x3000) { Value = new Use(next, 64) }] });
    }

    private static void Settle(MachineFunction function)
    {
        do
        {
            function.Renumber();
            Propagate.Run(function, Dominators.Compute(function));
        } while (ControlFlow.Simplify(function));
    }

    private static void Native(RecoverySession session)
    {
        var outer = session.Model.Code[0xa45d4c8].Single().Method;
        var prepared = session.Analyze(outer, outer.Method.Address);
        Require(prepared.Problems.Count == 0 && !prepared.Function.Blocks.SelectMany(b => b.Statements).OfType<Branch>().Any(),
            "真实 MaterialRenderingSettings 构造中，删去纯类型检查后形成的空分支也应清理");
        Require(BodyRecovery.Recover(session, prepared).Body is not null, "真实构造方法保持可恢复");
        GateBranchCheck.Run(session);

        var flag = new Variable(Storage.Gpr(8), 1);
        var frame = EdgeConstantsCheck.Graph(
            new Block(0x1000) { Statements = [new Store(0x1000, new FrameAddress(-8), Expr.C(0, 64)),
                new Define(0x1004, flag, new Load(new FrameAddress(-8), 64)),
                new Branch(0x1008, new Compare(Cond.Eq, new Use(flag, 64), Expr.C(0, 64)), 0x2000, 0x3000)] },
            new Block(0x2000) { Statements = [new Return(0x2000) { Value = new Use(X, 64) }] },
            new Block(0x3000) { Statements = [new Return(0x3000) { Value = new Use(Y, 64) }] });
        var frameResult = new Prepare(session.Resolver, session.Calls, session.Machine.Convention).Run(frame);
        Require(frameResult.PromotedSlots == 1 && !frame.Blocks.SelectMany(b => b.Statements).OfType<Branch>().Any(),
            "栈槽提升新产生的常量条件也要清理");
        Require(SsaCheck.Verify(frame, Dominators.Compute(frame)).Count == 0, "栈槽提升与边清理后仍满足 SSA");
        Require(EdgeConstantsCheck.Execute(frame, X, 23, Y, 91) == 23, "提升后的常量分支保留正确侧");

        var types = session.Types;
        var owner = new TypeDef { Index = -1, Assembly = "ControlFlowChecks.dll", Namespace = "Checks", Name = "Harness", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodRef(new MethodDef
        {
            Index = -1, Owner = owner, Name = "Pick", Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = types.UInt64,
            Parameters = [new("a", types.UInt64, 0, null, false), new("b", types.UInt64, 0, null, false)],
        }, [], []);
        var function = Parallel(Condition);
        var result = new Prepare(session.Resolver, session.Calls, session.Machine.Convention).Run(function);
        var body = BodyRecovery.Recover(session, new(method, session.Abi.ClassifyReturn(types.UInt64, out _), function, result, []));
        Require(body.Body is not null, string.Join("; ", body.Problems));
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ControlFlowChecks", new Version(1, 0)), "ControlFlowChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(host);
        var actual = new MethodDefinition("Pick", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.UInt64);
        actual.Parameters.Add(new ParameterDefinition(module.TypeSystem.UInt64)); actual.Parameters.Add(new ParameterDefinition(module.TypeSystem.UInt64)); host.Methods.Add(actual);
        var emitter = new BodyEmitter(types, t => module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(t), true)!),
            f => throw new NotSupportedException(f.ToString()), m => throw new NotSupportedException(m.ToString()));
        var problem = emitter.Emit(body.Body!, actual); Require(problem is null, problem ?? "重边输出");
        using var stream = new MemoryStream(); assembly.Write(stream);
        Execute(SR.Assembly.Load(stream.ToArray()));
        ObjectAllocationCheck.Source(assembly, Execute, "control-flow-source-check");
        Console.WriteLine("重边不同 φ 值的完整恢复、CIL/C# 执行通过；真实构造空分支已清理，外层构造尚未运行");
    }

    private static void Execute(SR.Assembly assembly)
    {
        var pick = (Func<ulong, ulong, ulong>)assembly.GetType("Checks.Harness", true)!.GetMethod("Pick")!.CreateDelegate(typeof(Func<ulong, ulong, ulong>));
        foreach (var a in new ulong[] { 0, 1, 0x1_0000_0000, ulong.MaxValue })
        foreach (var b in new ulong[] { 7, 0x8000_0000_0000_0000, ulong.MaxValue })
            Require(pick(a, b) == (a == 0 ? a : b), "同目标的两条边必须各自复制正确 φ 来源");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
