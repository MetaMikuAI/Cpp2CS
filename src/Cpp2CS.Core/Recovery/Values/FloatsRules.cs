using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class FloatsRules
{
    private static Dictionary<Storage, int> ScalarInputs(RecoveryScope ctx)
    {
        var widths = ctx.State.Signature.arguments.Where(p => p.Key.Bank == Bank.Vec
            && ctx.types.Kind(p.Value.Type) is TypeKind.Float or TypeKind.Double).ToDictionary(p => p.Key, p => p.Value.Width);
        // HFA 参数的每个分量也只占向量寄存器低位，与调用实参和返回分量使用同一 ABI 宽度。
        foreach (var (register, argument) in ctx.State.Signature.structArguments)
            if (register.Bank == Bank.Vec && argument.Piece.Width is 32 or 64) widths[register] = argument.Piece.Width;
        return widths;
    }

    internal static void NormalizeScalarVectors(this RecoveryScope ctx) => ScalarVectorNarrowing.Run(ctx.function.Blocks, call => ctx.ScalarWidths(call, false), call => ctx.ScalarWidths(call, true), ScalarInputs(ctx));
    internal static void NarrowTypedScalars(this RecoveryScope ctx)
    {
        var changed = ScalarVectorNarrowing.NarrowDefinitions(ctx.blocks, call => ctx.ScalarWidths(call, false, typed: true), call => ctx.ScalarWidths(call, true, typed: true), ScalarInputs(ctx), (previous, replacement) =>
        {
            if (ctx.State.Structs.fragmentLocals.ContainsKey(previous.Target))
                ctx.State.Structs.fragmentDefinitions.TryAdd(previous.Target, previous.Value);
            ctx.Rewriter.Preserve(previous, replacement);
        });
        if (changed == 0)
            return;
        ctx.definitions = ctx.IndexDefinitions();
        ctx.InferTypes();
    }

    internal static Dictionary<Storage, int> ScalarWidths(this RecoveryScope ctx, Call call, bool returned, bool typed = false)
    {
        var widths = new Dictionary<Storage, int>();
        if (call.Op is { Kind: OpKind.Import, Operand: string symbol } && MathImportSignature.Find(symbol) is { } math
            && call.Arguments.Length == math.Parameters.Length)
        {
            var width = math.Single ? 32 : 64;
            if (returned) widths[Storage.Vec(0)] = width;
            else for (var index = 0; index < math.Parameters.Length; index++)
                if (!math.IsInteger(index)) widths[math.Register(index)] = width;
            return widths;
        }
        if (call.Op is { Kind: OpKind.ImportOutPair, Operand: "sincosf" })
        {
            foreach (var register in returned ? call.Results : call.Sources) widths[register] = 32;
            return widths;
        }
        MethodRef[] methods;
        // 按已知间接调用签名投影；不是实参的向量寄存器只作透传（宽度 0），不算使用。
        if (call.Op is { Kind: OpKind.CallInterface or OpKind.CallVirtual or OpKind.CallGenericVirtual or OpKind.CallDelegate } && (typed ? ctx.Resolve(call) : ctx.Callee(call)) is { } indirect && ctx.owner.abi.Classify(indirect, out _) is { } indirectSignature)
        {
            if (returned)
            {
                if (indirectSignature.Return is { Passing: Passing.Registers, Pieces.Length: > 0 } result && result.Pieces.All(p => p.Register.Bank == Bank.Vec) && ctx.types.Kind(result.Type) is TypeKind.Float or TypeKind.Double or TypeKind.Struct)
                    foreach (var piece in result.Pieces)
                        widths[piece.Register] = piece.Width;
                return widths;
            }

            foreach (var register in call.Sources.Where(s => s.Bank == Bank.Vec))
                widths[register] = indirectSignature.Arguments.Where(a => a.Passing == Passing.Registers && a.Pieces.All(p => p.Register.Bank == Bank.Vec) && ctx.types.Kind(a.Type) is TypeKind.Float or TypeKind.Double or TypeKind.Struct).SelectMany(a => a.Pieces).SingleOrDefault(p => p.Register == register) is { } parameter ? parameter.Width : indirectSignature.Arguments.Any(a => a.Pieces.Any(p => p.Register == register)) ? -1 : 0;
            foreach (var register in widths.Where(p => p.Value < 0).Select(p => p.Key).ToArray())
                widths.Remove(register);
            return widths;
        }

        if (call.Op is not null || call.Target is not Const target)
            return widths;
        methods = ctx.facts.EntriesAt(target.Value).Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod && e.Method is not null).Select(e => e.Method!).Distinct().ToArray();
        if (methods.Length == 0)
            return widths;
        var signatures = methods.Select(m => ctx.owner.abi.Classify(m, out _)).ToArray();
        if (signatures.Any(s => s is null))
            return widths;
        // ICF 共用入口只有在所有签名对同一寄存器给出同一标量宽度时才能投影，不挑选调用目标。
        if (returned)
        {
            // 标量浮点返回值，或 HFA（各片都在向量寄存器中，如 Vector3 的 s0–s2）。
            var returns = signatures.Select(s => s!.Return is { Passing: Passing.Registers } r && r.Pieces.Length > 0 && r.Pieces.All(p => p.Register.Bank == Bank.Vec) && ctx.types.Kind(r.Type) is TypeKind.Float or TypeKind.Double or TypeKind.Struct ? string.Join(",", r.Pieces.Select(p => $"{p.Register}:{p.Width}")) : null).ToArray();
            if (returns.All(r => r is not null) && returns.Distinct().Count() == 1)
                foreach (var piece in signatures[0]!.Return!.Pieces)
                    widths[piece.Register] = piece.Width;
            return widths;
        }

        foreach (var register in call.Sources.Where(s => s.Bank == Bank.Vec))
        {
            // HFA 的每个成员也只观察对应向量寄存器的低位，不能让它的 128 位外壳阻止标量 φ 收窄。
            var parameters = signatures.Select(s => s!.Arguments.Where(a => a.Passing == Passing.Registers && a.Pieces.All(p => p.Register.Bank == Bank.Vec) && ctx.types.Kind(a.Type) is TypeKind.Float or TypeKind.Double or TypeKind.Struct).SelectMany(a => a.Pieces).SingleOrDefault(p => p.Register == register)).ToArray();
            if (parameters.All(p => p is not null) && parameters.Select(p => p!.Width).Distinct().ToArray() is [var width])
                widths[register] = width;
        }

        return widths;
    }

    internal static RecoveryResult<ManagedValue> FloatingNegation(this RecoveryScope ctx, Unary unary)
    {
        if (unary.Width is not (32 or 64))
            return RecoveryDiagnostics.Fail(0, $"浮点 一元运算位宽 {unary.Width} 尚未支持", rule: "FloatingNegation");
        var type = unary.Width == 32 ? ctx.types.Single : ctx.types.Double;
        return ctx.RecoverAs(unary.Operand, type, 0).Map<ManagedValue>(value => new UnaryValue(unary.Op, value, type, unary.Width));
    }

    [BodyProof(20)]
    internal static void CheckFloatingConstructorOrder(this RecoveryScope ctx, ManagedBody body)
    {
        if (ctx.method.Method.Name != ".ctor")
            return;
        // 全程序 float-constructors 普查见任务报告。此形态需要恢复 this(...) 链接；
        // 把有副作用的浮点调用移到基类构造之后会改变顺序，留给构造函数恢复，不在 F2 重排。
        foreach (var block in body.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not ManagedCall { Invocation: { Method.Method.Name: ".ctor", Receiver: ArgumentValue { Index: -1 } } })
                    continue;
                foreach (var producer in block.Statements.Take(i).OfType<ManagedCall>().Where(c => c.Result is { } r && ctx.types.Kind(r.Type) is TypeKind.Float or TypeKind.Double))
                {
                    var aliases = new HashSet<Ir.Variable>
                    {
                        producer.Result!.Variable
                    };
                    for (var changed = true; changed;)
                    {
                        changed = false;
                        foreach (var assignment in body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>())
                            if (ManagedValues.Walk(assignment.Value).OfType<LocalValue>().Any(l => aliases.Contains(l.Variable)))
                                changed |= aliases.Add(assignment.Target.Variable);
                    }

                    if (block.Statements.Skip(i + 1).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => aliases.Contains(l.Variable)))
                        ctx.Hole(producer.Address, "构造函数 浮点调用结果跨越 this 初始化，尚未恢复构造链接", rule: "CheckFloatingConstructorOrder");
                }
            }
    }
}
