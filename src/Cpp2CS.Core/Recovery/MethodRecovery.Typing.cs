using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private Dictionary<Variable, TypeRef>? typingSeeds;
        private Dictionary<Variable, TypeResult>? syncedSolution;

        /// <summary>
        /// 类型推断（T3 引擎），结果写回 known。表达式定型由恢复器自己的 Recover 回答（<see cref="HostTyping"/>），
        /// 它在每轮读引擎上一轮的解；约束集中在贡献者里（<see cref="TypingContributors"/>），由求解器统一裁决。
        /// 异常值（AnalyzeExceptionValues 写入 known 的 catch 对象）是种子，优先于引擎结果。
        /// </summary>
        private void InferTypes()
        {
            typingSeeds ??= known.ToDictionary();
            var (view, entryTypes, input) = TypingInputsFor();
            TypingContext context = null!;
            context = new(view, types, entryTypes, call => { Sync(context.Solution); return Resolve(call); });
            var trace = (Environment.GetEnvironmentVariable("CPP2CS_TYPING_TRACE") ?? "").Split(',').Contains($"0x{entry:x}") ? new TraceContributor() : null;
            var result = new TypeEngine([.. TypingContributors.Create(input), .. trace is null ? [] : new ITypeContributor[] { trace }]).Run(context);
            syncedSolution = null;
            Sync(result.Solution, final: true);
            trace?.Print(result.Solution, result.Rounds);
        }

        /// <summary>诊断：CPP2CS_TYPING_TRACE=0x入口[,0x入口…] 时打印最后一轮的全部约束与解（stderr）。不参与推断。</summary>
        private sealed class TraceContributor : ITypeContributor
        {
            private TypeConstraints last = new();
            public string Name => "诊断";
            public void Contribute(TypingContext context, TypeConstraints constraints) => last = constraints;

            public void Print(Dictionary<Variable, TypeResult> solution, int rounds)
            {
                Console.Error.WriteLine($"引擎 {rounds} 轮");
                foreach (var v in last.Variables.Concat(solution.Keys).Distinct().OrderBy(v => v.ToString(), StringComparer.Ordinal))
                {
                    Console.Error.WriteLine($"  {v} = {solution.GetValueOrDefault(v)?.ToString() ?? "未知"}");
                    foreach (var (type, evidence) in last.Definitions.GetValueOrDefault(v) ?? []) Console.Error.WriteLine($"    定义 {type}  {evidence}");
                    foreach (var (type, evidence) in last.Uses.GetValueOrDefault(v) ?? []) Console.Error.WriteLine($"    使用 {type}  {evidence}");
                    foreach (var (source, evidence) in last.FlowEdges.GetValueOrDefault(v) ?? []) Console.Error.WriteLine($"    来自 {source}  {evidence}");
                }
            }
        }

        /// <summary>
        /// known := 种子 ∪ 解中的托管类型（运行时引用除外）。推断过程中冲突的变量也写入下界，与贡献者看到的一致；
        /// 最终结果只保留确定的类型，冲突留洞。同一个解只同步一次。
        /// </summary>
        private void Sync(Dictionary<Variable, TypeResult> solution, bool final = false)
        {
            if (ReferenceEquals(syncedSolution, solution)) return;
            syncedSolution = solution;
            typeVersion++;
            known.Clear();
            foreach (var (variable, result) in solution)
            {
                if (runtime.Contains(variable)) continue;
                var type = result switch
                {
                    ManagedResult managed => managed.Type,
                    ConflictResult { Lower: { } lower } when !final => lower,
                    _ => null,
                };
                if (type is not null) known[variable] = type;
            }
            foreach (var (variable, type) in typingSeeds!) known[variable] = type;
        }

        private sealed class HostTyping(Context host, TypingContext typing) : IExpressionTyping
        {
            public TypeRef? TypeOf(Expr expression, TypeRef? hint = null)
            {
                host.Sync(typing.Solution);
                try { return host.Recover(expression, hint).Type; }
                catch (HoleException) { return null; }
            }

            public TypeRef? LocationType(Expr address, int width)
            {
                host.Sync(typing.Solution);
                try { return host.Location(address, width).Type; }
                catch (HoleException) { return null; }
            }

            public Expr Expand(Expr expression) => host.Expand(expression);

            public IReadOnlyList<TypeRef>? StructReceiverArguments(Expr? receiver, TypeDef owner)
            {
                host.Sync(typing.Solution);
                return host.StructReceiverArguments(receiver, owner);
            }

            public IEnumerable<(Call Call, Use Klass)> TypeChecks() => host.typeChecks.Select(p => (p.Key, p.Value)).ToArray();
        }

        /// <summary>引擎的输入：EH 已证明保留的块与 φ 入边构成的类型视图、入口参数类型、已证明的非类型分析结果。</summary>
        private (MachineFunction View, Dictionary<Storage, TypeRef> Entry, TypingInputs Input) TypingInputsFor()
        {
            // 不改原 CFG，Build 仍用原始边编号。
            var view = new MachineFunction
            {
                Entry = function.Entry, Range = function.Range,
                Blocks = blocks.Select(b => new Block(b.Start)
                {
                    Index = b.Index, End = b.End, IsLandingPad = b.IsLandingPad,
                    Statements = b.Statements.Select(s => s is Phi phi ? (Stmt)(exceptionPhis.GetValueOrDefault(phi.Target) ?? phi) : s).ToList(),
                }).ToList(),
            };
            var input = new TypingInputs
            {
                Method = method,
                Arguments = arguments.ToDictionary(p => p.Key, p => new EntryArgument(p.Value.Index, p.Value.Type, p.Value.Width)),
                StructArguments = structArguments.ToDictionary(), Dropped = dropped.ToHashSet(),
                StoredArguments = stackArgumentStores.Concat(boxArgumentStores).ToDictionary(p => p.Key, p => p.Value.Type),
                Constructed = constructed.ToDictionary(), DelegateCreations = delegateCreations.ToDictionary(),
                Wrappers = wrappers.ToDictionary(), Exceptions = exceptionValues.ToDictionary(),
                HasExceptions = exceptionLayout is { Succeeded: true }, ReturnSupported = returnHole is null,
                Host = context => new HostTyping(this, context),
            };
            var entry = input.Arguments.Where(p => !input.StructArguments.ContainsKey(p.Key) && p.Value.Type is not ByRefRef)
                .ToDictionary(p => p.Key, p => p.Value.Type);
            return (view, entry, input);
        }
    }
}
