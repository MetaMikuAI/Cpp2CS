using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Idioms;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// Cysharp.Threading.Tasks.UniTask&lt;T&gt;.GetAwaiter()：普查二进制中它的全部 GenericMethod 实例（new Awaiter(in this) 内联），
/// 要求每个的结果（Awaiter&lt;T&gt; 只有一个字段 task，与 UniTask&lt;T&gt; 同布局）都是 *this 的逐字节拷贝。
/// 解释器据此把认回的 task.GetAwaiter() 当作按 Awaiter&lt;T&gt; 读取 *this（CilInterpreter.InvokeAt）。
/// </summary>
[ShapeModel("UniTask<T> 的 awaiter", Basis = "awaiter-census：二进制中 UniTask<T>.GetAwaiter 的全部 GenericMethod 实例的结果都是 *this 的逐字节拷贝")]
internal static class AwaiterCensus
{
    public static bool IsGetAwaiter(MethodRef method) => method.Method is { Name: "GetAwaiter", IsStatic: false, Parameters.Count: 0, GenericParameters.Count: 0 }
        && method.DeclaringType is DefinitionRef { Definition.FullName: "Cysharp.Threading.Tasks.UniTask", Arguments.Count: 1 };

    [Command("awaiter-census", "普查 UniTask<T>.GetAwaiter 实例：结果的每个字节都拷贝自 *this 的同一偏移", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var lifter = new FunctionLifter(facts);
        var rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false };
        var recovery = new MethodRecovery(facts, types);
        var a = new Assertions();
        var instances = 0;
        foreach (var function in facts.Code.Functions)
            foreach (var entry in facts.EntriesAt(function.Start).Where(e => e.Kind == EntryKind.GenericMethod && e.Method is { } m && IsGetAwaiter(m)
                && m.TypeArguments is [DefinitionRef { Definition.FullName: not "Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericType" } or ArrayRef]))
            {
                instances++;
                var size = types.Size(entry.Method!.DeclaringType);
                string? problem;
                if (size <= 16)
                {
                    // 寄存器返回（AAPCS64 C.10–C.11）：L2 不跟踪返回寄存器，按恢复后的返回值核对每个叶子 task.f… 都是 (*this).f…。
                    var result = recovery.RecoverInstance(entry.Method!, function.Start);
                    var statements = result.Body?.Blocks.SelectMany(b => b.Statements).ToArray() ?? [];
                    problem = result.Body is not null && statements.OfType<ManagedReturn>().ToArray() is [{ Value: { } value }]
                        && statements.All(st => st is ManagedReturn or ManagedJump or ManagedAssignment or ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue } } })
                        && Composes(value, statements)
                        ? null : $"寄存器返回不是 *this 的各叶子（{string.Join("；", result.Holes.Select(h => h.Reason).Take(2))}{(Environment.GetEnvironmentVariable("CPP2CS_CENSUS_DEBUG") == "1" ? string.Join("；", statements.Select(st => st.ToString())) : "")}）";
                }
                else
                {
                    var lifted = lifter.Lift(function.Start);
                    problem = lifted.Succeeded ? Copies(lifted.Function, rewriter, size, facts) : "提升失败";
                }
                a.True(problem is null, $"0x{function.Start:x} {entry.Method} 不是 *this 的逐字节拷贝：{problem}");
            }
        Console.WriteLine($"  UniTask<T>.GetAwaiter 实例 {instances} 个");
        // Awaiter<T>.get_IsCompleted：恢复后都是 source = this.task.source; source == null ? true : source.GetStatus(this.task.token) != Pending。
        var completions = 0;
        var outside = 0;
        var unreadable = 0;
        foreach (var function in facts.Code.Functions)
            foreach (var entry in facts.EntriesAt(function.Start).Where(e => e.Kind == EntryKind.GenericMethod && e.Method is { } m && GenericInline.IsModeled(m.Method)
                && m.TypeArguments is [DefinitionRef { Definition.FullName: not "Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericType" } or ArrayRef]))
            {
                var getResult = entry.Method!.Method.Name == "GetResult";
                // GetResult 的模型只用于结果不超过 16 字节的 T（GenericInline.ResultLimit）；更大的实例经 x8 间接返回，不在模型范围内。
                var resultType = entry.Method!.TypeArguments[0];
                if (getResult && !ManagedTypes.IsReferenceType(resultType) && types.Size(resultType) > GenericInline.ResultLimit) { outside++; continue; }
                completions++;
                var result = recovery.RecoverInstance(entry.Method!, function.Start);
                // 读不出的实例（L3 尚未支持的形态）不是反例：列出，认回时不为这些 T 建模（AccessorRecovery.GenericCallees）。
                if (result.Body is null)
                {
                    unreadable++;
                    Console.WriteLine($"  未读出 0x{function.Start:x} {entry.Method}：{string.Join("；", result.Holes.Where(h => !h.Derived).Select(h => h.Reason).Distinct().Take(2))}");
                    continue;
                }
                var problem = getResult ? GetResultShape(result.Body) : IsCompletedShape(result.Body);
                a.True(problem is null, $"0x{function.Start:x} {entry.Method} 不是 {(getResult ? "GetResult" : "IsCompleted")} 形态：{problem}");
            }
        Console.WriteLine($"  UniTask.Awaiter<T>.get_IsCompleted / GetResult 实例 {completions} 个（GetResult 结果超过 16 字节、不在模型范围的 {outside} 个；读不出的 {unreadable} 个）");
        a.True(completions > 0, "没有找到 Awaiter<T>.get_IsCompleted / GetResult 实例");
        a.True(instances > 0, "没有找到 UniTask<T>.GetAwaiter 实例");
        return a.Finish("awaiter-census");
    }

    /// <summary>
    /// 结果缓冲区（x8，间接返回）的最终内容：逐条写入 [x8+k]（先清零、再写入 [x0+k] 的读取，或 memcpy(x8, x0, n)），
    /// 要求 [0, size) 的每个字节最后都来自 [x0] 的同一偏移。其余只允许保存寄存器、类初始化、写屏障（含尾调用运行时的写屏障）与跳转。
    /// </summary>
    private static string? Copies(MachineFunction function, IdiomRewriter rewriter, int size, ProgramFacts facts)
    {
        rewriter.Run(function);
        var x0 = new Variable(Storage.Gpr(0), 0);
        var x8 = new Variable(Storage.Gpr(8), 0);
        var loads = new Dictionary<Variable, (long Offset, int Width)>();
        var bytes = new long?[size];
        long? Offset(Expr address, Variable root) => address switch
        {
            Use u when u.Variable == root => 0,
            Binary { Op: BinOp.Add, Left: Use u, Right: Const c } when u.Variable == root => (long)c.Value,
            Binary { Op: BinOp.Add, Left: Binary { Op: BinOp.Add, Left: Use u, Right: Const c1 }, Right: Const c2 } when u.Variable == root => (long)(c1.Value + c2.Value),
            _ => null,
        };
        if (function.Blocks.Any(b => b.Statements.OfType<Branch>().Any())) return "有条件分支";
        foreach (var statement in function.Blocks.SelectMany(b => b.Statements))
            switch (statement)
            {
                case Store { Target: FrameAddress or Binary { Left: FrameAddress } }: break;
                case Store store when Offset(store.Target, x8) is { } at:
                    var width = store.Value.Width / 8;
                    if (at < 0 || at + width > size) return $"写入越界 +0x{at:x}";
                    for (var k = 0; k < width; k++)
                        bytes[at + k] = store.Value is Const { Value: 0 } ? null
                            : store.Value is Use { Variable: var v } && loads.TryGetValue(v, out var load) && load.Width == store.Value.Width ? load.Offset + k : -1;
                    break;
                case Define { Value: Load { Address: var address } load } define when Offset(address, x0) is { } from:
                    loads[define.Target] = (from, load.Width);
                    break;
                case Call { Op: { Kind: OpKind.Import, Operand: "memcpy" } } copy when copy.Arguments is [Use { Variable: var d }, Use { Variable: var s }, Const { Value: var n }]
                    && d == x8 && s == x0 && (int)n == size:
                    for (var k = 0; k < size; k++) bytes[k] = k;
                    break;
                case Call { Op: { Kind: OpKind.Import, Operand: "memset" } } clear when clear.Arguments is [Use { Variable: var d }, Const { Value: 0 }, Const { Value: var n }]
                    && d == x8 && (int)n <= size:
                    for (var k = 0; k < (int)n; k++) bytes[k] = null;
                    break;
                case Call { Op.Kind: OpKind.InitClass or OpKind.RunClassConstructor or OpKind.WriteBarrier }: break;
                case Call { Kind: CallKind.Tail, Op: null, Target: Const helper } when facts.Code.RegionOf(helper.Value) != CodeRegion.Managed: break;
                case Jump or Return or Nop: break;
                default: return $"语句 {statement}";
            }
        for (var k = 0; k < size; k++)
            if (bytes[k] != k) return $"字节 +0x{k:x} 不是拷贝（{bytes[k]}）";
        return null;
    }

    /// <summary>
    /// IsCompleted 形态：唯一的调用是以 this.task.source（局部变量 s）为接收者、实参来自 this.task.token 的 IUniTaskSource.GetStatus（callvirt）；
    /// 唯一的分支是 s == null；返回值（经局部变量与边上的复制）只可能是常量 1 或 (status == 0 ? 0 : 1)。
    /// </summary>
    private static string? IsCompletedShape(ManagedBody body)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var definitions = statements.OfType<ManagedAssignment>().Select(x => (x.Target.Variable, x.Value))
            .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => (c.Target.Variable, c.Value))).ToLookup(p => p.Variable, p => p.Value);
        IEnumerable<ManagedValue> Sources(ManagedValue v, int depth = 0)
        {
            if (depth < 8 && v is ConversionValue c) return Sources(c.Operand, depth + 1);
            if (depth < 8 && v is LocalValue l && definitions[l.Variable].Any()) return definitions[l.Variable].SelectMany(x => Sources(x, depth + 1));
            return [v];
        }
        static bool ThisField(ManagedValue v, string inner) => v is FieldValue { Field.Field.Name: var name } f && name == inner
            && (f.Receiver is AddressValue a ? a.Target : f.Receiver) is FieldValue { Field.Field.Name: "task" } t
            && (t.Receiver is AddressValue b ? b.Target : t.Receiver) is ArgumentValue { Index: -1 } or IndirectValue { Address: ArgumentValue { Index: -1 } };
        var calls = statements.OfType<ManagedCall>().ToArray();
        if (calls is not [{ Invocation: { Method.Method: { Name: "GetStatus", Owner.FullName: "Cysharp.Threading.Tasks.IUniTaskSource" }, Virtual: true, Receiver: { } receiver, Arguments: [var token] }, Result: { } status } call])
            return "调用不是唯一的 IUniTaskSource.GetStatus";
        if (receiver is not LocalValue source || !Sources(source).All(v => ThisField(v, "source"))) return "接收者不是 this.task.source";
        if (!Sources(token).All(v => ThisField(v, "token"))) return "实参不是 this.task.token";
        var branches = statements.OfType<ManagedBranch>().ToArray();
        if (branches is not [{ Condition: ComparisonValue { Condition: Cond.Eq, Left: LocalValue tested, Right: ConstantValue { Bits: 0 } } }] || tested.Variable != source.Variable)
            return "分支不是唯一的 source == null";
        if (statements.Any(s => s is not (ManagedAssignment or ManagedCall or ManagedBranch or ManagedJump or ManagedReturn))) return "有其他语句";
        var returns = statements.OfType<ManagedReturn>().ToArray();
        bool Allowed(ManagedValue v) => v is ConstantValue { Bits: 1 }
            || v is ChoiceValue { Condition: ComparisonValue { Condition: Cond.Eq, Left: LocalValue s, Right: ConstantValue { Bits: 0 } }, True: ConstantValue { Bits: 0 }, False: ConstantValue { Bits: 1 } }
                && s.Variable == status.Variable;
        if (returns.Length == 0 || !returns.All(r => r.Value is { } v && Sources(v).All(Allowed))) return "返回值不是 1 或 status != 0";
        return null;
    }

    /// <summary>
    /// GetResult 形态：唯一的分支是 s == null（s 是 this.task.source）；唯一的调用是以 s 为接收者、实参来自 this.task.token 的 IUniTaskSource&lt;T&gt;.GetResult（callvirt）；
    /// 返回值（经局部变量与边上的复制）只可能是该调用的结果或 this.task.result。
    /// </summary>
    private static string? GetResultShape(ManagedBody body)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var definitions = statements.OfType<ManagedAssignment>().Select(x => (x.Target.Variable, x.Value))
            .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => (c.Target.Variable, c.Value))).ToLookup(p => p.Variable, p => p.Value);
        IEnumerable<ManagedValue> Sources(ManagedValue v, int depth = 0)
        {
            if (depth < 8 && v is ConversionValue c) return Sources(c.Operand, depth + 1);
            if (depth < 8 && v is IndirectValue { Address: AddressValue { Target: var inner } }) return Sources(inner, depth + 1);
            if (depth < 8 && v is LocalValue l && definitions[l.Variable].Any()) return definitions[l.Variable].SelectMany(x => Sources(x, depth + 1));
            return [v];
        }
        static bool ThisField(ManagedValue v, string inner) => v is FieldValue { Field.Field.Name: var name } f && name == inner
            && (f.Receiver is AddressValue a ? a.Target : f.Receiver) is FieldValue { Field.Field.Name: "task" } t
            && (t.Receiver is AddressValue b ? b.Target : t.Receiver) is ArgumentValue { Index: -1 } or IndirectValue { Address: ArgumentValue { Index: -1 } };
        var calls = statements.OfType<ManagedCall>().ToArray();
        if (calls is not [{ Invocation: { Method: { Method: { Name: "GetResult", Owner.FullName: "Cysharp.Threading.Tasks.IUniTaskSource" } }, Virtual: true, Receiver: LocalValue source, Arguments: [var token] }, Result: var result }])
            return "调用不是唯一的 IUniTaskSource<T>.GetResult";
        if (!Sources(source).All(v => ThisField(v, "source"))) return "接收者不是 this.task.source";
        if (!Sources(token).All(v => ThisField(v, "token"))) return "实参不是 this.task.token";
        if (statements.OfType<ManagedBranch>().ToArray() is not [{ Condition: ComparisonValue { Condition: Cond.Eq, Left: LocalValue tested, Right: ConstantValue { Bits: 0 } } }]
            || tested.Variable != source.Variable)
            return "分支不是唯一的 source == null";
        if (statements.Any(s => s is not (ManagedAssignment or ManagedCall or ManagedBranch or ManagedJump or ManagedReturn))) return "有其他语句";
        bool Allowed(ManagedValue v) => v is LocalValue l && result is not null && l.Variable == result.Variable || ThisField(v, "result");
        // 按叶子组合的返回值：每个叶子都是（调用结果或 this.task.result）的同一路径。
        bool Leafwise(ManagedValue v) => v is ComposedValue composed && composed.Leaves.Count > 0 && composed.Leaves.All(leaf => Sources(leaf.Value).All(source =>
        {
            var current = source;
            for (var i = leaf.Path.Count - 1; i >= 0; i--)
            {
                if (current is not FieldValue field || field.Field.Field != leaf.Path[i].Field) return false;
                current = field.Receiver is AddressValue address ? address.Target : field.Receiver;
            }
            return Sources(current).All(Allowed);
        }));
        var returns = statements.OfType<ManagedReturn>().ToArray();
        if (returns.Length == 0 || !returns.All(r => r.Value is { } v && (Leafwise(v) || Sources(v).All(Allowed)))) return "返回值不是调用结果或 this.task.result";
        return null;
    }

    /// <summary>返回值是 Awaiter&lt;T&gt;，每个叶子 task.f… 都是 (*this).f…（可经局部变量的整体赋值或整体写入转递）。</summary>
    private static bool Composes(ManagedValue value, ManagedStatement[] statements)
    {
        var whole = statements.Select(st => st switch
            {
                ManagedAssignment x => (Local: x.Target.Variable, x.Value),
                ManagedStore { Target: IndirectValue { Address: AddressValue { Target: LocalValue l } } } x => (Local: l.Variable, x.Value),
                _ => (Local: (Variable?)null, Value: (ManagedValue?)null),
            }).Where(p => p.Local is not null).GroupBy(p => p.Local!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single().Value!);
        ManagedValue Through(ManagedValue v)
        {
            for (var guard = 0; guard < 8 && v is LocalValue local && whole.TryGetValue(local.Variable, out var next); guard++) v = next;
            return v;
        }
        if (Through(value) is not ComposedValue { StructType: DefinitionRef { Definition.Name: "Awaiter" } awaiter } composed
            || awaiter.Definition.DeclaringType?.FullName != "Cysharp.Threading.Tasks.UniTask") return false;
        foreach (var (path, leaf) in composed.Leaves)
        {
            if (path.Count < 2 || path[0].Field.Name != "task") return false;
            var current = Through(leaf);
            for (var i = path.Count - 1; i >= 1; i--)
            {
                if (current is not FieldValue field || field.Field.Field != path[i].Field) return false;
                current = Through(field.Receiver is AddressValue address ? address.Target : field.Receiver);
            }
            if (current is not (ArgumentValue { Index: -1 } or IndirectValue { Address: ArgumentValue { Index: -1 } })) return false;
        }
        return composed.Leaves.Count > 0;
    }
}
