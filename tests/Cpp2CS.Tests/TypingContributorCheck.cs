using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Tests;

/// <summary>
/// 贡献者的边界与反例：未知加载不接受 T1 猜测，运行时加载偏移保持严格，破坏值不由使用反推类型。
/// 表达式与访存位置的类型由恢复器回答（HostTyping），由全量 recover 与执行对照覆盖；这里用不知道任何表达式类型的宿主，只测贡献者自身的规则。
/// </summary>
internal static class TypingContributorCheck
{
    private sealed class NoExpressions : IExpressionTyping
    {
        public TypeRef? TypeOf(Expr expression, TypeRef? hint = null) => null;
        public TypeRef? LocationType(Expr address, int width) => null;
        public Expr Expand(Expr expression) => expression;
        public IReadOnlyList<TypeRef>? StructReceiverArguments(Expr? receiver, TypeDef owner) => null;
        public IEnumerable<(Call Call, Use Klass)> TypeChecks() => [];
    }

    [Command("typing-contributors", "T3 贡献者的迁移边界与反例", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var a = new Assertions();
        var method = types.CorlibMethod("System.Object", "MemberwiseClone")!;
        var block = new Block(0x1000);
        var function = new MachineFunction { Entry = block.Start, Range = new(0x1000, 0x1100, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block] };
        var arguments = new Dictionary<Storage, EntryArgument>();
        var structs = new Dictionary<Storage, (ArgumentValue Root, AbiPiece Piece)>();
        var wrappers = new Dictionary<Variable, LocalValue>();
        var exceptions = new Dictionary<Variable, LocalValue>();
        var input = new TypingInputs
        {
            Method = method, Arguments = arguments, StructArguments = structs, Dropped = new HashSet<Stmt>(),
            Constructed = new Dictionary<Call, Variable>(), DelegateCreations = new Dictionary<Call, DefinitionRef>(),
            Wrappers = wrappers, Exceptions = exceptions, HasExceptions = true, ReturnSupported = true, Host = _ => new NoExpressions(),
        };
        TypingContext Context() => new(function, types, new Dictionary<Storage, TypeRef>(), _ => null);
        Variable V(int n) => new(Storage.Gpr(n), 1);
        var unknown = V(1);
        block.Statements = [new Define(0x1000, unknown, new Load(Expr.C(0x100, 64), 64)), new Return(0x1004) { Value = new Use(unknown, 64) }];
        var restricted = new TypeConstraints(); new UseContributor(input).Contribute(Context(), restricted);
        a.True(!TypeSolver.Solve(restricted, types).ContainsKey(unknown), "T1 不为未知加载猜返回类型");
        block.Statements[0] = new Define(0x1000, unknown, Expr.C(0, 64));
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        a.Equal<TypeResult?>(new ManagedResult(types.Object), TypeSolver.Solve(restricted, types).GetValueOrDefault(unknown), "64 位 null 可由返回签名定型");

        var exception = types.Corlib("System.Exception");
        var root = new Variable(Storage.Gpr(0), 0);
        arguments[root.Storage] = new(0, exception, 64);

        var metadataResult = V(2); var methodPointer = V(3); var beyond = V(4); var phi = V(5);
        var lookup = new Call(0x1000, CallKind.Direct, Expr.C(0, 64))
        { Op = new(OpKind.InterfaceInvokeData, null), Results = [Storage.Gpr(0)], Defines = [metadataResult] };
        Expr At(ulong offset) => new Binary(BinOp.Add, new Use(metadataResult, 64), Expr.C(offset, 64), 64);
        block.Statements = [lookup, new Define(0x1004, methodPointer, new Load(At(8), 64)), new Define(0x1008, beyond, new Load(At(16), 64)), new Phi(0x100c, phi, [methodPointer, V(9)])];
        var runtime = new TypeEngine([new RuntimeContributor(input)]).Run(Context());
        a.True(runtime.Converged && runtime.Solution.GetValueOrDefault(methodPointer) is RuntimeResult, "InterfaceInvokeData +8 是运行时指针");
        a.True(!runtime.Solution.ContainsKey(beyond), "InterfaceInvokeData +16 不能套用元数据规则");
        a.True(runtime.Solution.GetValueOrDefault(phi) is RuntimeResult, "φ 任一来源是运行时引用即标记");

        block.Statements = [lookup, new Phi(0x1004, methodPointer, [metadataResult, root]), new Phi(0x1008, beyond, [methodPointer])];
        var mixed = new TypingContext(function, types, new Dictionary<Storage, TypeRef> { [root.Storage] = exception }, _ => null);
        var mixedResult = new TypeEngine([new EntryArgumentContributor(), new PhiContributor(), new RuntimeContributor(input)]).Run(mixed);
        a.True(mixedResult.Converged && mixedResult.Solution.GetValueOrDefault(beyond) is ConflictResult,
            "运行时来源经过中间冲突 φ 后仍保留，不能丢失运行时事实而变成托管引用");

        var selected = new Select(Expr.C(1, 1), new Use(methodPointer, 32), new Use(beyond, 32), 32);
        block.Statements = [new Define(0x1000, phi, new Binary(BinOp.FAdd, selected, Expr.C(0, 32), 32))];
        var floating = new TypeConstraints(); new FloatContributor(input).Contribute(Context(), floating);
        a.Equal<TypeResult?>(new ManagedResult(types.Single), TypeSolver.Solve(floating, types).GetValueOrDefault(methodPointer), "F2 浮点使用穿过 Select 约束两侧，独立于 T1 适用范围");

        var caught = new LocalValue(new(Storage.Temp(-1), 1), exception, 64);
        block.Statements = [new Define(0x1000, methodPointer, new Load(new Use(metadataResult, 64), 64)), new Define(0x1004, beyond, new Use(methodPointer, 64)), new Phi(0x1008, phi, [methodPointer, beyond])];
        var (closedWrappers, closedExceptions) = ExceptionValueClosure.Close(block.Statements, new Dictionary<Variable, LocalValue> { [metadataResult] = caught }, new Dictionary<Variable, LocalValue>());
        foreach (var (variable, value) in closedWrappers) wrappers[variable] = value;
        foreach (var (variable, value) in closedExceptions) exceptions[variable] = value;
        var eh = new TypeEngine([new ExceptionContributor(input)]).Run(Context());
        a.Equal<TypeResult?>(new ManagedResult(exception), eh.Solution.GetValueOrDefault(phi), "catch wrapper+0 与同源 φ 恢复异常类型");
        a.True(eh.Solution.GetValueOrDefault(metadataResult) is RuntimeResult, "catch wrapper 保持运行时身份");


        // 被调用者不读 x0 时，调用后 x0 是破坏值，
        // 它与 null 汇合后作为接收者传出。φ 目标的使用不能反推出破坏值的类型，否则下降阶段把它写成 default。
        var clobbered = new Variable(Storage.Gpr(0), -1);
        arguments.Clear(); arguments[root.Storage] = new(0, exception, 64);
        block.Statements = [new Phi(0x1000, phi, [root, clobbered])];
        var undefined = new TypeEngine([new EntryArgumentContributor(), new PhiContributor(), new PhiUseContributor()])
            .Run(new TypingContext(function, types, new Dictionary<Storage, TypeRef> { [root.Storage] = exception }, _ => null));
        a.True(undefined.Solution.GetValueOrDefault(clobbered) is ClobberedResult, "φ 中版本为负的来源是破坏值，不由 φ 的使用反推类型");

        foreach (var width in new[] { 32, 64 })
        {
            var initial = V(10); var index = V(11); var next = V(12);
            Expr read = new Use(index, width);
            Expr increment = new Binary(BinOp.Add, read, Expr.C(1, width), width);
            if (width == 32) increment = new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, increment, 64);
            block.Statements =
            [
                new Define(0x1000, initial, Expr.C(0, 64)),
                new Phi(0x1004, index, [initial, next]),
                new Call(0x1008, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.BoundsCheck, null), Arguments = [read, Expr.C(3, width)] },
                new Define(0x100c, next, increment),
            ];
            var loop = new TypeEngine([new PhiContributor(), new UseContributor(input), new PhiUseContributor()]).Run(Context());
            a.True(loop.Converged && new[] { initial, index, next }.All(v => loop.Solution.GetValueOrDefault(v) is ManagedResult m && TypeSolver.Integral(types, m.Type)),
                $"{width} 位边界检查为常量起始循环提供整数约束");
            block.Statements.RemoveAt(2);
            var unproven = new TypeEngine([new PhiContributor(), new UseContributor(input), new PhiUseContributor()]).Run(Context());
            a.True(unproven.Converged && unproven.Solution.Count == 0, "无整数用途的循环不凭零初值猜类型");
        }
        return a.Finish("typing-contributors");
    }
}
