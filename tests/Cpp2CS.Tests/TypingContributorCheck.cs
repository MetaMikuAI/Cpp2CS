using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
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
        public IEnumerable<(Call Call, Expr Klass)> TypeChecks() => [];
    }

    [Command("typing-contributors", "T3 贡献者的迁移边界与反例", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
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
            Method = method, Arguments = arguments, StructArguments = structs, Dropped = new HashSet<Stmt>(), StoredArguments = new Dictionary<Store, TypeRef>(),
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
        var nullChoice = V(14); var unknownChoice = V(15); var choice = V(16);
        block.Statements = [new Define(0x1000, nullChoice, Expr.C(0, 64)),
            new Define(0x1004, unknownChoice, new Load(Expr.C(0x100, 64), 64)),
            new Define(0x1008, choice, new Select(Expr.C(1, 1), new Use(nullChoice, 64), new Use(unknownChoice, 64), 64)),
            new Return(0x100c) { Value = new Use(choice, 64) }];
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        var selectedReference = TypeSolver.Solve(restricted, types);
        a.Equal<TypeResult?>(new ManagedResult(types.Object), selectedReference.GetValueOrDefault(nullChoice), "引用选择的使用传到 null 分支");
        a.True(!selectedReference.ContainsKey(unknownChoice), "引用选择仍不猜未知加载类型");

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
        var projectedBits = Context();
        projectedBits.Solution[methodPointer] = new ManagedResult(types.UInt64);
        foreach (var width in new[] { 32, 64 })
        {
            block.Statements = [new Define(0x1000, phi, new Binary(BinOp.FAdd, new Use(methodPointer, width), Expr.C(0, width), width))];
            floating = new();
            floating.Defines(methodPointer, types.UInt64, new("输入", 0x1000, "宽整数位容器"));
            new FloatContributor(input).Contribute(projectedBits, floating);
            var projected = TypeSolver.Solve(floating, types).GetValueOrDefault(methodPointer);
            a.True(width == 32 ? projected == new ManagedResult(types.UInt64) : projected is ConflictResult,
                "窄浮点读取只约束切片，整值整数与浮点冲突仍保留");
        }
        var firstChoice = new Select(Expr.C(1, 1), Expr.C(0x3f000000, 32), Expr.C(0x3f800000, 32), 32);
        var nextChoice = new Select(Expr.C(1, 1), Expr.C(0x3e800000, 32), new Use(methodPointer, 32), 32);
        block.Statements = [new Define(0x1000, methodPointer, firstChoice), new Define(0x1004, beyond, nextChoice),
            new Define(0x1008, phi, new Binary(BinOp.FAdd, new Use(beyond, 32), Expr.C(0, 32), 32))];
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        var choices = TypeSolver.Solve(restricted, types);
        a.True(new[] { methodPointer, beyond }.All(v => choices.GetValueOrDefault(v) == new ManagedResult(types.Single)),
            "浮点用途穿过连续的常量位型选择");
        block.Statements[0] = new Define(0x1000, methodPointer, new Load(Expr.C(0x100, 64), 32));
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        a.True(!TypeSolver.Solve(restricted, types).ContainsKey(methodPointer), "连续浮点选择仍不猜未知加载类型");

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
            var count = V(13);
            foreach (var operation in new[] { BinOp.Shl, BinOp.LShr, BinOp.AShr })
            {
                block.Statements[2] = new Call(0x1008, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.BoundsCheck, null), Arguments = [new Binary(operation, read, new Use(count, 32), width), Expr.C(3, width)] };
                block.Statements.Add(new Define(0x1010, count, Expr.C(2, 64)));
                var shifted = new TypeEngine([new PhiContributor(), new UseContributor(input), new PhiUseContributor()]).Run(Context());
                a.True(shifted.Converged && new[] { initial, index, next, count }.All(v => shifted.Solution.GetValueOrDefault(v) is ManagedResult m && TypeSolver.Integral(types, m.Type)),
                    $"{width} 位 {operation} 的整数用途穿过移位传到循环与移位量");
                block.Statements[^1] = new Define(0x1010, count, new Load(Expr.C(0x100, 64), 32));
                var unknownCount = new TypeEngine([new PhiContributor(), new UseContributor(input), new PhiUseContributor()]).Run(Context());
                a.True(!unknownCount.Solution.ContainsKey(count), "移位用途不为未知加载猜类型");
                block.Statements.RemoveAt(block.Statements.Count - 1);
            }
            block.Statements.RemoveAt(2);
            var unproven = new TypeEngine([new PhiContributor(), new UseContributor(input), new PhiUseContributor()]).Run(Context());
            a.True(unproven.Converged && unproven.Solution.Count == 0, "无整数用途的循环不凭零初值猜类型");
        }
        var initialFlag = V(20); var nextFlag = V(21); var loopFlag = V(22); var maskedFlag = V(23); var returnedFlag = V(24);
        block.Statements =
        [
            new Define(0x1000, initialFlag, Expr.C(0, 64)),
            new Define(0x1004, nextFlag, Expr.C(1, 64)),
            new Phi(0x1008, loopFlag, [initialFlag, loopFlag, nextFlag]),
            new Define(0x100c, maskedFlag, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend,
                new Binary(BinOp.And, new Use(loopFlag, 32), Expr.C(1, 32), 32), 64)),
            new Phi(0x1010, returnedFlag, [maskedFlag, nextFlag]),
            new Call(0x1014, CallKind.Direct, Expr.C(0, 64))
            { Op = new(OpKind.BoundsCheck, null), Arguments = [new Use(returnedFlag, 32), Expr.C(2, 32)] },
        ];
        var flagContributors = new ITypeContributor[] { new PhiContributor(), new UseContributor(input), new PhiUseContributor() };
        var flagTypes = new TypeEngine(flagContributors).Run(Context());
        a.True(flagTypes.Converged && new[] { initialFlag, nextFlag, loopFlag, maskedFlag, returnedFlag }
            .All(v => flagTypes.Solution.GetValueOrDefault(v) is ManagedResult m && TypeSolver.Integral(types, m.Type)),
            "合流结果的整数用途穿过已定型按位定义传回循环标志");
        block.Statements[0] = new Define(0x1000, initialFlag, new Load(Expr.C(0x100, 64), 64));
        block.Statements[3] = new Define(0x100c, maskedFlag, new Binary(BinOp.And, new Use(initialFlag, 64), Expr.C(1, 64), 64));
        var loadedContext = Context();
        loadedContext.Solution[maskedFlag] = new ManagedResult(types.UInt64);
        restricted = new(); new UseContributor(input).Contribute(loadedContext, restricted);
        a.True(!TypeSolver.Solve(restricted, types).ContainsKey(initialFlag), "反传不直接定型未知加载");
        block.Statements.RemoveAt(block.Statements.Count - 1);
        var untypedFlag = new TypeEngine(flagContributors).Run(Context());
        a.True(untypedFlag.Converged && untypedFlag.Solution.Count == 0, "无外部整数用途时不凭常量与按位表达式猜控制标志类型");

        var receiverNull = V(17); var pointerResult = V(18); var pointerClobber = V(19);
        var pointerCall = new Call(0x1004, CallKind.Indirect, Expr.C(0, 64))
        {
            Op = new(OpKind.CallMethodPointer, method), Arguments = [new Use(receiverNull, 64)], Sources = [Storage.Gpr(0)],
            Results = [Storage.Gpr(0), Storage.Gpr(1)], Defines = [pointerResult, pointerClobber],
        };
        block.Statements = [new Define(0x1000, receiverNull, Expr.C(0, 64)), pointerCall];
        var pointerTypes = new TypeEngine([new CallResultContributor(), new UseContributor(input)])
            .Run(new TypingContext(function, types, new Dictionary<Storage, TypeRef>(), _ => method));
        a.Equal<TypeResult?>(new ManagedResult(types.Object), pointerTypes.Solution.GetValueOrDefault(pointerResult), "已确定方法指针的返回签名定型");
        a.Equal<TypeResult?>(new ManagedResult(types.Object), pointerTypes.Solution.GetValueOrDefault(receiverNull), "方法指针的接收者用途传到 null");
        a.True(pointerTypes.Solution.GetValueOrDefault(pointerClobber) is ClobberedResult, "方法指针的非返回寄存器仍是破坏值");
        block.Statements = [pointerCall with { Op = new(OpKind.Import, "unknown") }];
        var notManaged = new TypeEngine([new CallResultContributor()]).Run(new TypingContext(function, types, new Dictionary<Storage, TypeRef>(), _ => method));
        a.True(!notManaged.Solution.ContainsKey(pointerResult), "其他运行时操作不能套用托管调用返回规则");

        const int depth = 20000;
        Variable Chain(int i) => new(Storage.Temp(i), 1);
        block.Statements = [new Define(0x1000, Chain(0), Expr.C(1, 32))];
        for (var i = 1; i <= depth; i++)
            block.Statements.Add(new Define((ulong)(0x1000 + i * 4), Chain(i),
                new Binary(BinOp.Or, new Use(Chain(i - 1), 32), new Use(Chain(i - 1), 32), 32)));
        block.Statements.Add(new Call(0x20000, CallKind.Direct, Expr.C(0, 64))
        { Op = new(OpKind.BoundsCheck, null), Arguments = [new Use(Chain(depth), 32), Expr.C(2, 32)] });
        block.Statements.Add(new Define(0x20004, Chain(depth + 1),
            new Compare(Cond.Slt, new Use(Chain(depth), 32), Expr.C(2, 32))));
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        a.True(restricted.Uses[Chain(0)].Select(u => u.Type).ToHashSet().SetEquals([types.Int32, types.Integer(32, false)]),
            "深层共享定义链保留不同用途的有符号与无符号约束");
        a.True(restricted.Uses[Chain(0)].Select(u => u.Evidence.Address).ToHashSet().SetEquals([0x20000UL, 0x20004UL]),
            "共享定义去重只作用于当前用途，保留各使用位置的证据");
        a.Equal(depth + 1, restricted.Uses.Count, "已证实整数用途沿窄整数链一次约束全部中间值");
        block.Statements = [new Define(0x1000, Chain(0), new Binary(BinOp.Or, new Use(Chain(1), 32), Expr.C(0, 32), 32)),
            new Define(0x1004, Chain(1), new Binary(BinOp.Or, new Use(Chain(0), 32), Expr.C(0, 32), 32)),
            new Call(0x1008, CallKind.Direct, Expr.C(0, 64))
            { Op = new(OpKind.BoundsCheck, null), Arguments = [new Use(Chain(1), 32), Expr.C(2, 32)] }];
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        a.Equal(2, restricted.Uses.Count, "窄整数循环由外部用途约束，回溯能终止");
        block.Statements.RemoveAt(2);
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        a.Equal(0, restricted.Uses.Count, "无外部用途时不凭循环自身猜类型");
        block.Statements = [new Define(0x1000, Chain(0), new Load(Expr.C(0x100, 64), 64)),
            new Define(0x1004, Chain(1), new Binary(BinOp.Add, new Use(Chain(0), 64), Expr.C(8, 64), 64)),
            new Call(0x1008, CallKind.Direct, Expr.C(0, 64))
            { Op = new(OpKind.BoundsCheck, null), Arguments = [new Use(Chain(1), 64), Expr.C(2, 64)] }];
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        a.Equal(0, restricted.Uses.Count, "64 位地址加法及未知加载不按窄整数运算定型");
        block.Statements[1] = new Define(0x1004, Chain(1), new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, new Use(Chain(0), 32), 32));
        block.Statements[2] = new Call(0x1008, CallKind.Direct, Expr.C(0, 64))
        { Op = new(OpKind.BoundsCheck, null), Arguments = [new Use(Chain(1), 32), Expr.C(2, 32)] };
        restricted = new(); new UseContributor(input).Contribute(Context(), restricted);
        a.Equal(0, restricted.Uses.Count, "同宽转换可能保留浮点类型，不凭整数用途给结果定型");
        foreach (var width in new[] { 32, 64 })
        {
            block.Statements = [new Define(0x1000, Chain(0), new Binary(BinOp.And,
                    new Use(unknown, 64), Expr.C(uint.MaxValue, 64), 64)),
                new Define(0x1004, Chain(1), new Use(Chain(0), width))];
            var projected = Context();
            projected.Solution[Chain(1)] = new ManagedResult(width == 32 ? types.Int32 : types.Int64);
            restricted = new(); new UseContributor(input).Contribute(projected, restricted);
            var solution = TypeSolver.Solve(restricted, types);
            a.Equal<TypeResult?>(new ManagedResult(width == 32 ? types.UInt64 : types.Int64), solution.GetValueOrDefault(Chain(0)),
                "低位有符号快照不反推宽来源的符号，整值用途仍保留符号");
            a.True(!solution.ContainsKey(unknown), "位型用途仍不猜未知来源");
        }
        return a.Finish("typing-contributors");
    }
}
