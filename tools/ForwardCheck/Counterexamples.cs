using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Emit;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using MethodBody = Cpp2CS.Kernel.Forward.MethodBody;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>泛型实例的身份用到的夹具：同一个泛型类型的两个实例上的同名方法。</summary>
internal static class CounterexampleBox<T>
{
    public static void Call() { }
}

/// <summary>
/// 反例核对：每一项是一个具体输入，以及按出处应得的结论。出处写在各项的注释与输出里：
/// ECMA-335 的条款、CLR 上执行同一段 IL 的结果，或 docs/前端.md、docs/设计.md 的条款。
/// 需要核心库的一项从 --assemblies 给出的目录读取。
/// </summary>
internal static class Counterexamples
{
    private sealed record Item(string Name, string Source, Func<string?> Check);

    private static readonly TypeShape Int32 = new(StackKind.Int32, 32, true, default);
    private static readonly TypeShape Float32 = new(StackKind.Float32, 32, true, default);
    private static readonly TypeShape Float64 = new(StackKind.Float64, 64, true, default);
    private static readonly TypeShape Reference = new(StackKind.Object, 64, false, default);

    private static Slot Integer(int i) => new(SlotKind.Integer, i);
    private static readonly Slot Stack = new(SlotKind.StackPointer, 0);
    private static readonly Slot Link = new(SlotKind.ReturnAddress, 0);

    public static int Run(string assemblies)
    {
        var items = new List<Item>
        {
            // ---- IL 一侧的展开 ----

            // ECMA-335 III.3.63 stloc：浮点值从内部表示舍入到局部变量的大小；I.12.1.3：存入存储位置时转换到该位置的类型。
            // CLR 执行 float32 M(float64 x) { ldarg.0; stloc.0; ldloc.0; ret }，x = 1.0 时返回位型 0x3f800000。
            new("浮点存储按格式转换", "ECMA-335 III.3.63、I.12.1.3；CLR 执行结果 0x3f800000", () =>
            {
                var graph = Expand([0x02, 0x0a, 0x06, 0x2a], Float32, [Float64], [Float32]);
                var returned = Walk(graph).Single().Outcome[0];
                if (returned is not { Kind: TermKind.Operation, Op: Op.FConvert, Width: 32 } || returned.Operands[0] != graph.EntryParameters[0])
                    return $"返回 {returned}，应为参数的浮点格式转换";
                uint bits = BitConverter.SingleToUInt32Bits((float)BitConverter.Int64BitsToDouble(0x3ff0000000000000));
                return bits == 0x3f800000 ? null : $"按 IEEE 754 转换得 {bits:x8}";
            }),

            // ECMA-335 III.4.10 ldfld：对象为空且字段不是静态的才抛出 NullReferenceException。
            // CLR 执行 ldnull; ldfld static int32 F; ret（F 已为 37）正常返回 37。展开不能给出无条件的空引用抛出。
            new("ldfld 访问静态字段", "ECMA-335 III.4.10；CLR 执行结果 37", () =>
                Rejected(() => Expand([0x14, 0x7b, 1, 0, 0, 4, 0x2a], Int32, metadata: new StaticFieldView()), "目录里没有适用的变体")),

            // ECMA-335 III.1.6 表 III.9：签名为 int32 时，栈上的对象引用是无效的 CIL；III.3.57 ret 的返回值须与返回类型相容。
            new("返回类型不相容", "ECMA-335 III.1.6 表 III.9、III.3.57", () =>
                Rejected(() => Expand([0x14, 0x2a], Int32), "目录里没有适用的变体")),

            // 设计 14.6：接口查找的参数是接收者对象 (o, I, s)；运行时 vm/ClassInlines.h 的 GetInterfaceInvokeDataFromVTable(obj, itf, slot)
            // 在慢路径上把对象本身交给 GetInterfaceInvokeDataFromVTableSlowPath。
            new("接口查找保留接收者", "设计 14.6；libil2cpp vm/ClassInlines.h GetInterfaceInvokeDataFromVTable", () =>
            {
                var graph = Expand([0x02, 0x6f, 1, 0, 0, 6, 0x2a], null, [Reference], metadata: new InterfaceView());
                // 走查给出操作数在路径上的取值，换到入口：接收者就是第 0 个形参。
                var lookup = Walk(graph).Single().Steps.Single(step => graph[step.Occurrence].Kind == EffectKind.RuntimeCall);
                return lookup.Operands.Length == 1 && lookup.Operands[0] == graph.EntryParameters[0] ? null
                    : $"接口查找的操作数是 [{string.Join(", ", lookup.Operands)}]，应为接收者";
            }),

            // ECMA-335 III.3.66：switch 的项数 N 是无符号 32 位数，其后紧跟 N 个 int32 目标。声明 2^30 + 1 项而只带一个目标是不完整的指令。
            new("跳转表的长度溢出", "ECMA-335 III.3.66", () =>
                Rejected(() => IlDecoder.Decode([0x16, 0x45, 0x01, 0x00, 0x00, 0x40, 0, 0, 0, 0, 0x2a]), "IL 无法解码")),

            // ECMA-335 III.3.66：选择子不小于 N 时顺序执行下一条指令；N 为 0 时只有这一个去向。docs/前端.md 第 2 节：最后一个出口是其余取值的去向。
            new("零项跳转表", "ECMA-335 III.3.66；docs/前端.md 第 2 节", () =>
            {
                var graph = Expand([0x16, 0x45, 0, 0, 0, 0, 0x2a], null);
                var paths = Walk(graph);
                return paths.Length == 1 && paths[0].End == PathEnd.Return ? null : $"走查得到 {paths.Length} 条路径";
            }),

            // ECMA-335 II.25.4.4：CorILMethod_InitLocals 表示进入时初始化全部局部变量；I.12.3.2.2：是否初始化由方法的元数据说明。
            // 设置了这一位的方法读未赋值的 int32 局部变量得 0；没有设置的方法没有得出 0 的依据，不展开。
            new("局部变量的初始化标志", "ECMA-335 II.25.4.4、I.12.3.2.2", InitLocals),

            // ---- 核对工具的元数据 ----

            // docs/前端.md 第 7 节：模型里每个类型、方法、字段有一个稳定的编号。Box<int>.Call 与 Box<uint>.Call 是两个方法。
            new("泛型实例的方法身份", "docs/前端.md 第 7 节", GenericMembers),

            // docs/前端.md 第 7 节：同一个类型只有一个编号。签名里的 int32、string 与核心库里的 System.Int32、System.String 是同一个类型。
            new("基本类型的身份", "docs/前端.md 第 7 节", () => CoreTypes(assemblies)),

            // ---- 快照的构造 ----

            // docs/前端.md 第 4 节“展开出口”：Unwind 槽的结果只经展开出口传给着陆点；正常出口上只有正常返回的结果。
            new("展开出口的结果", "docs/前端.md 第 4 节", () =>
            {
                var b = new SnapshotBuilder(64);
                var p = b.Terms;
                var normal = b.Block(64);
                var landing = b.Block(64);
                var sp = b.EntryParameter(Stack, 64);
                var r = b.Call(b.Entry, p.Zero(64), [(Stack, sp)], [(Integer(0), 64), (new(SlotKind.Unwind, 0), 64)]);
                b.Terminate(b.Entry, Terminator.Invoke(Exit.To(normal, r[1]), Exit.To(landing, r[0])));
                b.Terminate(normal, Terminator.Single(Exit.Trap));
                b.Terminate(landing, Terminator.Single(Exit.Trap));
                return Violations(b, "正常出口使用了展开时才有的结果", "展开出口使用了正常返回才有的结果");
            }),

            // docs/前端.md 第 4 节“返回”：返回槽的身份是方法契约的一部分；第 5 节：摘要取决于图的内容。只换返回槽的类别，摘要须不同。
            new("摘要含返回槽", "docs/前端.md 第 4、5 节", () =>
            {
                string Digest(SlotKind kind)
                {
                    var b = new SnapshotBuilder(64);
                    var ra = b.EntryParameter(Link, 64);
                    var sp = b.EntryParameter(Stack, 64);
                    b.SetReturnSlots((new(kind, 0), 64), (Link, 64), (Stack, 64));
                    b.Return(b.Entry, b.Terms.Zero(64), ra, sp);
                    return b.Build().DigestText;
                }
                return Digest(SlotKind.Integer) != Digest(SlotKind.Vector) ? null : "Integer0 与 Vector0 返回的摘要相同";
            }),

            // docs/前端.md 第 4 节“内存”：地址是指针位宽的项；指针位宽是快照内容的一部分。只换指针位宽，摘要须不同。
            new("摘要含指针位宽", "docs/前端.md 第 4、5 节", () =>
            {
                string Digest(int bits)
                {
                    var b = new SnapshotBuilder(bits);
                    b.Terminate(b.Entry, Terminator.Single(Exit.Trap));
                    return b.Build().DigestText;
                }
                return Digest(32) != Digest(64) ? null : "32 位与 64 位指针的摘要相同";
            }),

            // docs/前端.md 第 4 节“调用”：前端列出各实参槽此刻的值，并列出栈指针；结果按返回值槽位各列一个。“返回”：行里列出 ReturnAddress 与 StackPointer。
            new("调用与返回的槽位", "docs/前端.md 第 4 节", () =>
            {
                var b = new SnapshotBuilder(64);
                var p = b.Terms;
                var r = b.Call(b.Entry, p.Zero(64), [(Integer(0), p.Zero(64)), (Integer(0), p.Constant(1, 64))], [(Integer(0), 64), (Integer(0), 64)]);
                b.SetReturnSlots((Integer(0), 64), (Integer(0), 64));
                b.Return(b.Entry, r[0], r[1]);
                return Violations(b, "的实参：槽位 Integer0 重复", "的结果：槽位 Integer0 重复", "调用没有列出栈指针", "返回行：槽位 Integer0 重复",
                    "返回行没有列出 ReturnAddress 槽", "返回行没有列出 StackPointer 槽");
            }),

            // docs/前端.md 第 4 节“返回”：返回出口的行里列出实际返回到的地址与栈指针。从未声明返回行的空返回不满足。
            new("没有返回行的返回", "docs/前端.md 第 4 节", () =>
            {
                var b = new SnapshotBuilder(64);
                b.Return(b.Entry);
                return Violations(b, "返回行没有列出 ReturnAddress 槽", "返回行没有列出 StackPointer 槽");
            }),

            // docs/前端.md 第 4 节槽位表：Managed 只用于模板一侧，前端不使用。
            new("快照不用模板的槽位", "docs/前端.md 第 4 节", () =>
            {
                var b = new SnapshotBuilder(64);
                b.EntryParameter(new(SlotKind.Managed, 0), 64);
                b.Terminate(b.Entry, Terminator.Single(Exit.Trap));
                return Violations(b, "入口参数不能用 Managed 槽位");
            }),

            // docs/前端.md 第 1、3、7 节：快照里没有实体；Entity 与 Attribute 由事实层使用，前端不构造。
            new("快照里没有实体", "docs/前端.md 第 1、3、7 节", () =>
            {
                var b = new SnapshotBuilder(64);
                var p = b.Terms;
                var x = b.EntryParameter(Integer(0), 64);
                b.Write(b.Entry, p.Attribute(new(3), 64, p.Entity(new(EntityKind.Type, 9), 64)), x);
                b.Terminate(b.Entry, Terminator.Single(Exit.Trap));
                return Violations(b, "使用了实体或运行时属性");
            }),

            // docs/前端.md 第 2 节：Build 不满足契约时抛出 FlowException。完全没有终结的入口块也是如此。
            new("没有终结的快照", "docs/前端.md 第 2、5 节", () => Violations(new SnapshotBuilder(64), "B0 没有终结")),

            // docs/前端.md 第 5 节：FlowException 列出全部违反之处。条件不是 1 位，两条边又都缺实参：三处都要列出。
            new("列出全部违反之处", "docs/前端.md 第 5 节", () =>
            {
                var b = new SnapshotBuilder(64);
                var p = b.Terms;
                var target = b.Block(32);
                b.Terminate(b.Entry, Terminator.Branch(p.Zero(2), Exit.To(target), Exit.To(target)));
                b.Terminate(target, Terminator.Single(Exit.Trap));
                return Violations(b, "分支条件不是 1 位", "B0 的出口 0 给出 0 个实参", "B0 的出口 1 给出 0 个实参");
            }),

            // ---- 项 ----

            // docs/前端.md 第 3 节：FEq 是两个浮点位型的比较，结果 1 位（Op.FEq 的定义）。没有操作数、结果 32 位的 FEq 没有求值语义。
            new("运算的形状", "docs/前端.md 第 3 节；Op.FEq 的定义", () =>
                Rejected(() => new TermPool().Operation(Op.FEq, 32), "")),

            // docs/前端.md 第 3 节：切片取源位向量里的一段，区间须在源的位宽之内。offset + width 在 32 位里回绕也不能放过。
            new("切片的区间", "docs/前端.md 第 3 节", () =>
            {
                var p = new TermPool();
                return Rejected(() => p.Slice(p.Constant(1, 8), int.MaxValue - 127, 128), "");
            }),

            // 设计 7.2：项在构造时驻留，结构相同就是同一个实例。另一个池的子项会破坏这一点，构造时拒绝。
            new("项池只接受本池的项", "设计 7.2", () =>
            {
                TermPool p = new(), q = new();
                return Rejected(() => p.Opaque(0, 32, q.True), "");
            }),

            // docs/前端.md 第 5 节：摘要只取决于图的内容。别的池的项不能进入图。
            new("快照只用本池的项", "docs/前端.md 第 5 节；设计 7.2", () =>
            {
                var b = new SnapshotBuilder(64);
                var ra = b.EntryParameter(Link, 64);
                var sp = b.EntryParameter(Stack, 64);
                b.SetReturnSlots((Integer(0), 8), (Link, 64), (Stack, 64));
                b.Return(b.Entry, new TermPool().Zero(8), ra, sp);
                return Violations(b, "别的项池的项");
            }),

            // docs/前端.md 第 5 节：摘要与项池里项的构造次序无关。两个结构散列相同的项按相反的次序首次构造，Xor 的摘要须相同。
            new("可交换运算与构造次序", "docs/前端.md 第 5 节", CollisionOrder),

            // ---- 值的来源 ----

            // 设计 7.3：情况里的项不再含展开范围内的合流；逐情况提升在各情况结果相同时给出这个结果。
            // 入口把 (c, c) 传给 (p, q)，返回 Select(p, ZeroExtend(q, 8), 1)：c 为 1 时是 ZeroExtend(1, 8) = 1，为 0 时是 1。
            new("代入之后的同一个条件", "设计 7.3；docs/前端.md 第 3 节 Select、ZeroExtend", () =>
            {
                var b = new SnapshotBuilder(64);
                var p = b.Terms;
                var c = b.EntryParameter(Integer(0), 1);
                var ra = b.EntryParameter(Link, 64);
                var sp = b.EntryParameter(Stack, 64);
                var join = b.Block(1, 1, 64, 64);
                b.Jump(b.Entry, join, c, c, ra, sp);
                var x = p.Select(b.Parameter(join, 0), p.ZeroExtend(b.Parameter(join, 1), 8), p.Constant(1, 8));
                b.SetReturnSlots((Integer(0), 8), (Link, 64), (Stack, 64));
                b.Return(join, x, b.Parameter(join, 2), b.Parameter(join, 3));
                var graph = b.Build();
                var sources = new ValueSources(graph, p);
                var lifted = sources.Lift(new(join, 0), x, t => t);
                return lifted.Unanimous && lifted.Value == p.Constant(1, 8) ? null
                    : $"各情况：{string.Join(" | ", lifted.Cases.Select(r => r.Result))}";
            }),

            // 设计 7.1：块只使用块内按次序产生的值；7.3 的分情况与走查在图里的程序点上进行。
            new("查询尚未产生的值与不存在的点", "设计 7.1、7.3", () =>
            {
                var b = new SnapshotBuilder(64);
                var p = b.Terms;
                var read = b.Read(b.Entry, p.Zero(64), 8);
                b.Terminate(b.Entry, Terminator.Single(Exit.Trap));
                var sources = new ValueSources(b.Build(), p);
                return Rejected(() => sources.SplitCases(new(b.Entry, 0), [read]), "")
                    ?? Rejected(() => sources.Walk(new([new(b.Entry, 99)], [])), "");
            }),

            // 设计 7.3：按边代入把目标块的参数换成这条边上对应的实参，位宽不变。位宽对不上的“参数”不是图里的参数。
            new("查询伪造的参数", "设计 7.3", () =>
            {
                var b = new SnapshotBuilder(64);
                var p = b.Terms;
                var target = b.Block(8);
                b.Jump(b.Entry, target, p.Zero(8));
                b.Terminate(target, Terminator.Single(Exit.Trap));
                var sources = new ValueSources(b.Build(), p);
                var forged = p.BlockParameter(0, target, 0, 64);
                return Rejected(() => sources.Substitute(new(b.Entry, 0), forged), "")
                    ?? Rejected(() => sources.SplitCases(new(target, 0), [forged]), "");
            }),

            // ---- 图的冻结 ----

            // 设计 7.1：快照不被改写，任何步骤都不改写它。构造之后改动调用方持有的出现对象，图的内存版本不变。
            new("图不随出现对象改变", "设计 7.1", () =>
            {
                var builder = new FlowBuilder<MutableOccurrence>(new TermPool());
                var occurrence = new MutableOccurrence();
                builder.Append(builder.Entry, occurrence);
                builder.Terminate(builder.Entry, Terminator.Single(Exit.Trap));
                var graph = builder.Build();
                var before = graph.VersionAtExit(graph.Entry);
                occurrence.DefinesMemory = true;
                var after = graph.VersionAtExit(graph.Entry);
                return before == after ? null : $"内存版本从 {before} 变成 {after}";
            }),

            // 设计 7.1：图只在校验通过之后冻结。附加的校验只能追加违反，不能改动构造器，也删不掉内置检查的结论。
            new("附加校验不能改图", "设计 7.1", () =>
            {
                var builder = new FlowBuilder<MutableOccurrence>(new TermPool());
                builder.SetReturnWidths(8);
                builder.Terminate(builder.Entry, Terminator.Single(Exit.Return()));
                string? mutation = null;
                try
                {
                    builder.Build(draft =>
                    {
                        try { builder.Append(builder.Entry, new MutableOccurrence()); mutation = "校验期间仍能向图里追加出现"; }
                        catch (InvalidOperationException) { }
                    });
                }
                catch (FlowException failure)
                {
                    return mutation ?? (failure.Violations.Any(v => v.Contains("返回 0 个值")) ? null : "内置检查的违反没有列出");
                }
                return "错误的图通过了构造";
            }),
        };

        int passed = 0;
        var clock = System.Diagnostics.Stopwatch.StartNew();
        foreach (var item in items)
        {
            string? failure;
            try { failure = item.Check(); }
            catch (Exception unexpected) when (unexpected is ArgumentException or InvalidOperationException or ExpansionException or FlowException)
            {
                failure = $"意外的 {unexpected.GetType().Name}：{unexpected.Message}";
            }
            if (failure is null) passed++;
            Console.WriteLine($"  {(failure is null ? "通过" : "不通过")}  {item.Name}（{item.Source}）{(failure is null ? "" : "：" + failure)}");
        }
        Console.WriteLine($"反例：{items.Count} 个，通过 {passed} 个，用时 {clock.Elapsed.TotalSeconds:F1} 秒");
        return passed == items.Count ? 0 : 1;
    }

    // ---- 辅助 ----

    private static FlowGraph<TemplateEffect> Expand(byte[] code, TypeShape? returns, TypeShape[]? parameters = null, TypeShape[]? locals = null,
        IMetadataView? metadata = null)
    {
        var method = new MethodShape(default, false, [.. parameters ?? []], returns, VariantCondition.StaticMethod);
        var body = new MethodBody(method, [.. locals ?? []], [.. code], 0, InitLocals: true);
        return IlExpander.Expand(body, metadata ?? new StaticFieldView(), new TermPool(), 1, 64).Graph;
    }

    private static ImmutableArray<WalkPath> Walk(IFlowGraph graph)
    {
        var result = new ValueSources(graph, graph.Terms).Walk(new([new(graph.Entry, 0)], []));
        return result.Status == WalkStatus.Complete ? result.Paths : throw new InvalidOperationException($"走查没有走完：{result.Status}");
    }

    /// <summary>动作须以约定的异常拒绝；reason 非空时，展开的异常原因须相符。</summary>
    private static string? Rejected(Action action, string reason)
    {
        try { action(); }
        catch (ExpansionException failure) { return reason.Length == 0 || failure.Reason == reason ? null : $"拒绝的原因是 {failure.Reason}"; }
        catch (ArgumentException) { return reason.Length == 0 ? null : "以参数错误拒绝，没有展开的原因"; }
        return "没有被拒绝";
    }

    /// <summary>快照须以 FlowException 拒绝，并列出每一处期望的违反。</summary>
    private static string? Violations(SnapshotBuilder builder, params string[] expected)
    {
        try { builder.Build(); }
        catch (FlowException failure)
        {
            var missing = expected.Where(e => !failure.Violations.Any(v => v.Contains(e, StringComparison.Ordinal))).ToList();
            return missing.Count == 0 ? null : $"没有列出：{string.Join("；", missing)}（列出的是：{string.Join("；", failure.Violations)}）";
        }
        return "错误的快照通过了构造";
    }

    private static string? InitLocals()
    {
        string directory = Path.Combine(Path.GetTempPath(), "cpp2cs-counterexample-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        try
        {
            var assembly = new PersistedAssemblyBuilder(new AssemblyName("InitLocalsFixture"), typeof(object).Assembly);
            var type = assembly.DefineDynamicModule("InitLocalsFixture").DefineType("Fixture", TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed);
            foreach (bool initialized in (ReadOnlySpan<bool>)[true, false])
            {
                var method = type.DefineMethod(initialized ? "Initialized" : "Uninitialized", MethodAttributes.Public | MethodAttributes.Static, typeof(int), Type.EmptyTypes);
                method.InitLocals = initialized;
                var il = method.GetILGenerator();
                il.DeclareLocal(typeof(int));
                il.Emit(OpCodes.Ldloc_0);
                il.Emit(OpCodes.Ret);
            }
            type.CreateType();
            assembly.Save(Path.Combine(directory, "InitLocalsFixture.dll"));

            using var metadata = new SrmMetadata(directory, 64);
            var module = metadata.Load("InitLocalsFixture") ?? throw new InvalidOperationException("夹具程序集没有写出");
            string? result = null;
            foreach (var handle in module.Md.MethodDefinitions)
            {
                string name = module.Md.GetString(module.Md.GetMethodDefinition(handle).Name);
                var body = metadata.Body(module, MetadataTokens.GetToken(handle));
                if (name == "Initialized")
                {
                    if (!body.InitLocals) return "设置了 InitLocals 的方法读出的标志为假";
                    var returned = Walk(IlExpander.Expand(body, metadata.View(module), new TermPool(), 1, 64).Graph).Single().Outcome[0];
                    if (!returned.IsZero) result ??= $"设置了 InitLocals 的方法返回 {returned}";
                }
                else if (name == "Uninitialized")
                {
                    if (body.InitLocals) return "没有设置 InitLocals 的方法读出的标志为真";
                    result ??= Rejected(() => IlExpander.Expand(body, metadata.View(module), new TermPool(), 1, 64), "局部变量没有初始化的保证");
                }
            }
            return result;
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    private static void TwoCalls()
    {
        CounterexampleBox<int>.Call();
        CounterexampleBox<uint>.Call();
    }

    private static string? GenericMembers()
    {
        string path = typeof(Counterexamples).Assembly.Location;
        using var metadata = new SrmMetadata(Path.GetDirectoryName(path)!, 64);
        var module = metadata.Load(Path.GetFileNameWithoutExtension(path)) ?? throw new InvalidOperationException("读不到核对工具自己的程序集");
        int token = typeof(Counterexamples).GetMethod(nameof(TwoCalls), BindingFlags.NonPublic | BindingFlags.Static)!.MetadataToken;
        var calls = IlDecoder.Decode(metadata.Body(module, token).Code.AsSpan()).Where(i => i.Opcode.Canonical == "call").ToList();
        if (calls.Count != 2) return $"夹具里有 {calls.Count} 次调用";
        var first = metadata.Method(module, (int)calls[0].Operand).Entity;
        var second = metadata.Method(module, (int)calls[1].Operand).Entity;
        return first != second ? null : $"两个实例上的方法都是 {first}";
    }

    private static string? CoreTypes(string assemblies)
    {
        using var metadata = new SrmMetadata(assemblies, 64);
        var core = metadata.Load("mscorlib") ?? throw new InvalidOperationException($"{assemblies} 里没有核心库");
        string? Compare(string type, string field)
        {
            var handle = core.FindTopLevel("System", type) ?? throw new InvalidOperationException($"核心库里没有 System.{type}");
            var fieldHandle = core.Md.GetTypeDefinition(handle).GetFields().FirstOrDefault(f => core.Md.GetString(core.Md.GetFieldDefinition(f).Name) == field);
            if (fieldHandle.IsNil) throw new InvalidOperationException($"System.{type} 里没有字段 {field}");
            var bySignature = metadata.Field(core, MetadataTokens.GetToken(fieldHandle)).Type.Entity;
            var byDefinition = metadata.Type(core, MetadataTokens.GetToken(handle)).Entity;
            return bySignature == byDefinition ? null : $"System.{type}：签名得 {bySignature}，定义得 {byDefinition}";
        }
        // System.Int32 的 m_value 是签名里的 int32；System.String 的 Empty 是签名里的 string。
        return Compare("Int32", "m_value") ?? Compare("String", "Empty");
    }

    private static string? CollisionOrder()
    {
        // 与 Term 的结构散列同一个混合函数，构造两个散列相同而结构不同的 128 位常量。
        static ulong Mix(ulong h, ulong v)
        {
            h ^= v;
            h *= 0x100000001b3UL;
            return h ^ (h >> 29);
        }
        ulong start = Mix(Mix(Mix(0xcbf29ce484222325UL, (ulong)TermKind.Constant), 128), (ulong)Op.None);
        UInt128 k = ((UInt128)(Mix(start, 0) ^ Mix(start, 1)) << 64) | 1;
        (string Digest, bool Collides) Build(bool reversed)
        {
            var b = new SnapshotBuilder(64);
            var p = b.Terms;
            Term Make(UInt128 value) => p.Opaque(17, 128, p.Bits(value, 128));
            if (reversed) Make(k);
            var a = Make(UInt128.Zero);
            var c = Make(k);
            var ra = b.EntryParameter(Link, 64);
            var sp = b.EntryParameter(Stack, 64);
            b.SetReturnSlots((new(SlotKind.Vector, 0), 128), (Link, 64), (Stack, 64));
            b.Return(b.Entry, p.Xor(a, c), ra, sp);
            return (b.Build().DigestText, a.StructuralHash == c.StructuralHash);
        }
        var (forward, collides) = Build(false);
        var (backward, _) = Build(true);
        if (!collides) return "构造的两个项散列不同，反例不成立";
        return forward == backward ? null : "两种构造次序的摘要不同";
    }

    /// <summary>字段一律是静态的、所属类有静态构造函数的元数据。</summary>
    private sealed class StaticFieldView : IMetadataView
    {
        public TypeShape Type(int token) => Int32;
        public FieldShape Field(int token) => new(new(EntityKind.Field, 11), default, Int32, IsStatic: true, HasInitializer: true, PreciseInitialization: true, -1);
        public MethodShape Method(int token) => new(new(EntityKind.Method, 17), false, [], null, VariantCondition.StaticMethod);
    }

    /// <summary>方法一律是接口上的、无参无返回值的实例方法。</summary>
    private sealed class InterfaceView : IMetadataView
    {
        public TypeShape Type(int token) => Int32;
        public FieldShape Field(int token) => throw new ExpansionException("夹具里没有字段", "");
        public MethodShape Method(int token) => new(new(EntityKind.Method, 5), true, [Reference], null, VariantCondition.InterfaceMethod);
    }

    /// <summary>调用方持有、构造之后仍可改动的出现。</summary>
    private sealed class MutableOccurrence : IFlowOccurrence
    {
        public bool DefinesMemory { get; set; }
        public ImmutableArray<Term> Operands => [];
        public ImmutableArray<int> ResultWidths => [];
        public void WriteContent(DigestWriter writer) => writer.Write(17);
    }
}
