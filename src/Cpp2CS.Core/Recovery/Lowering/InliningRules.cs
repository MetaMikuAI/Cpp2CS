using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class InliningRules
{
    [Analysis("内联", 50, After = ["运行时引用"])]
    internal static void Inline(this RecoveryScope ctx)
    {
        var uses = new Dictionary<Variable, List<(Block Block, int Index)>>();
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                // 写屏障地址由托管存储承担；保留值参数的使用，避免引用选择表达式丢失局部变量类型。
                var operands = statement is Call { Op.Kind: OpKind.WriteBarrier, Arguments.Length: 2 } barrier ? barrier.Arguments.Skip(1) : ExprMap.Operands(statement);
                var used = statement is Phi phi ? phi.Sources.AsEnumerable() : operands.SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable);
                foreach (var v in used)
                {
                    if (!uses.TryGetValue(v, out var list))
                        uses[v] = list = [];
                    list.Add((statement is Phi ? null! : block, i));
                }
            }

        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Define define && !ctx.State.Runtime.runtime.Contains(define.Target) && !ExprMap.Walk(define.Value).Any(e => e is Load or FrameAddress) && uses.TryGetValue(define.Target, out var at) && at is [var only] && only.Block == block && only.Index > i)
                    ctx.State.Lowering.inlined.Add(define.Target);
        ctx.InlineStructArgumentLoads(uses);
    }

    internal static void InlineStructArgumentLoads(this RecoveryScope ctx, Dictionary<Variable, List<(Block Block, int Index)>> uses)
    {
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Define { Value: Load } define || ctx.State.Runtime.runtime.Contains(define.Target) || !uses.TryGetValue(define.Target, out var at) || at is not [var only] || only.Block is null)
                    continue;
                // 沿直线链（唯一正常后继且它只有一个前驱，含 try 中调用自成一块时的直落）找到唯一的使用；之间只能有纯定义，
                // 以及被调用方所属类型的类初始化（CIL 中由这次调用隐含触发，在实参求值之后，读取推迟到调用处顺序不变）。
                TypeRef? initialized = null;
                foreach (var statement in CheckRules.Straight(block, i))
                {
                    // 已证明只承载调用元数据的写入不会改变托管实参的求值顺序。
                    if (ctx.State.Lowering.dropped.Contains(statement))
                        continue;
                    if (statement is Call { Op: { Kind: OpKind.RunClassConstructor, Operand: TypeRef initType } } && initialized is null)
                    {
                        initialized = initType;
                        continue;
                    }

                    // 寄存器返回的结构体：片的读取只被返回使用时同样内联，叶子保留位置，可以整体返回该结构体字段（如 return this._ctx）。
                    if (statement is Return ret && ReferenceEquals(ret, only.Block.Statements[only.Index]))
                    {
                        if (ctx.owner.abi.Classify(ctx.method, out _)?.Return is { } returned && ctx.RegisterStruct(returned))
                            ctx.State.Lowering.inlined.Add(define.Target);
                        break;
                    }

                    if (statement is Call { Op: null } call && ReferenceEquals(call, only.Block.Statements[only.Index]))
                    {
                        if (ctx.Resolve(call) is { } callee && (initialized is null || callee.Method.IsStatic && callee.DeclaringType.Equals(initialized)) && ctx.owner.abi.Classify(callee, out _) is { } signature && signature.Parameters.Where(ctx.RegisterStruct).SelectMany(p => p.Pieces).Any(p => CallResolution.ArgumentsOf(call).TryGetValue(p.Register, out var argument) && argument is Use u && u.Variable == define.Target))
                            ctx.State.Lowering.inlined.Add(define.Target);
                        break;
                    }

                    if (statement is not (Define or Phi or Nop))
                        break;
                }
            }
    }

    internal static Expr Expand(this RecoveryScope ctx, Expr e) => e is Use u && ctx.State.Runtime.runtime.Contains(u.Variable) && ctx.values.TryGetValue(u.Variable, out var value) ? ctx.Expand(value) : e;
}
