using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Targets.Arm64;

namespace Cpp2CS.Tests;

internal static class RuntimeShapeChecks
{
    public const string Command = "runtime-shapes";
    public static int Run()
    {
        var checks = new Assertions();
        NativeFunction Body(ulong address, int constant, ulong target)
        {
            var terms = new TermTable();
            var entry = new BlockIdentity();
            var image = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64))) { ImageBase = image };
            var pointer = terms.Apply(new CoreOperator(CoreOperation.Add), 64, image, terms.Constant(address, 64));
            builder.Blocks.Add(new(entry, [], [new MemoryWrite(new(), pointer, 32, terms.Constant(constant, 32)),
                new Call(new(), new ImageFunction(target), [], [])], new Return([])));
            return builder.Freeze();
        }
        var reference = RuntimeReferenceShape.Create(Body(100, 7, 200), t => t, new InputMemoryImage())!;
        checks.True(reference.Text == RuntimeReferenceShape.Create(Body(300, 7, 400), t => t, new InputMemoryImage())!.Text, "地址平移不改变形状");
        checks.True(reference.Text != RuntimeReferenceShape.Create(Body(300, 8, 400), t => t, new InputMemoryImage())!.Text, "普通常量不抹去");
        checks.True(RuntimeReferenceShape.Create(Body(100, 7, 100), t => t, new InputMemoryImage())!.Text != reference.Text,
            "数据引用与调用目标之间的地址相等关系保留");
        checks.True(RuntimeReferenceShape.Create(Body(5000, 7, 100), t => t, new InputMemoryImage()) is null,
            "未映射的映像引用不能成为身份依据");
        var catalog = RuntimeFunctionCatalog.Select("2022.3.62f2", "aarch64-linux-android", "LP64");
        var function = catalog.Functions.First(f => f.Recognition.Symbol);
        var callee = RuntimeReferenceShape.Create(Body(300, 9, 400), t => t, new InputMemoryImage())!;
        var data = new RuntimeShapeCatalog(2, catalog.UnityVersion, catalog.Triple, catalog.DataModel,
            [new(function.MangledName, 8, reference.Text, [new(16, callee.Text)])]);
        var image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable)] };
        NativeFunction? Lift(ulong entry) => entry == 64 ? Body(300, 9, 400) : Body(500, 7, 64);
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, Lift, t => t).Count == 1, "唯一形状与调用关系一致才定位");
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, e => Body(500, 7, 64), t => t).Count == 0, "被调形状矛盾拒绝定位");
        image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(48, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable)] };
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, Lift, t => t).Count == 2, "同形且被调地址逐项相同的两个入口全部定位");
        image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable)],
            TryRegions = [new(66, 4, 100, [])] };
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, Lift, t => t).Count == 0, "被调函数有未接入 IR 的异常区域时拒绝定位");
        image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable)
            { Extents = [new(4, FunctionEvidence.UnwindTable), new(8, FunctionEvidence.SymbolTable)] }, new(64, 16, FunctionEvidence.UnwindTable)] };
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, Lift, t => t).Count == 0, "函数边界证据冲突不能作为形状依据");
        var second = catalog.Functions.Where(f => f.Recognition.Symbol).Skip(1).First();
        var leaf = RuntimeReferenceShape.Create(Body(600, 11, 400), t => t, new InputMemoryImage())!;
        data = data with { Entries = [data.Entries[0] with { Callees = [new(16, callee.Text) { Functions = [second.MangledName] }] },
            new(second.MangledName, 16, callee.Text, [new(24, leaf.Text)])] };
        image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable),
            new(96, 16, FunctionEvidence.UnwindTable), new(128, 24, FunctionEvidence.UnwindTable), new(160, 24, FunctionEvidence.UnwindTable)] };
        NativeFunction? Graph(ulong entry) => entry switch
        {
            32 => Body(500, 7, 64), 64 => Body(300, 9, 128), 96 => Body(300, 9, 160),
            128 => Body(600, 12, 400), _ => Body(600, 11, 400)
        };
        var reasons = new Dictionary<string, string>();
        var located = RuntimeShapeMatcher.Locate(image, catalog, data, Graph, t => t, reasons);
        checks.True(located.Count == 1 && located[0].Entry == 96 && reasons[function.MangledName].Contains("矛盾", StringComparison.Ordinal),
            "局部形状匹配不能覆盖目录函数之间的调用身份矛盾");
        var parallelReasons = new Dictionary<string, string>();
        var parallel = RuntimeShapeMatcher.Locate(image, catalog, data, Graph, t => t, parallelReasons, jobs: 4);
        checks.True(located.Select(p => (p.Entry, p.Location.Function.MangledName)).SequenceEqual(parallel.Select(p => (p.Entry, p.Location.Function.MangledName)))
            && reasons.OrderBy(p => p.Key).SequenceEqual(parallelReasons.OrderBy(p => p.Key)), "并行匹配不改变位置与矛盾裁定");
        data = data with { Entries = [new(function.MangledName, 8, reference.Text,
            [new(16, callee.Text) { Callees = [new(24, leaf.Text)] }])] };
        image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(48, 8, FunctionEvidence.UnwindTable),
            new(64, 16, FunctionEvidence.UnwindTable), new(96, 16, FunctionEvidence.UnwindTable),
            new(128, 24, FunctionEvidence.UnwindTable), new(160, 24, FunctionEvidence.UnwindTable)] };
        NativeFunction? NestedGraph(ulong entry) => entry switch
        {
            32 => Body(500, 7, 64), 48 => Body(500, 7, 96), 64 => Body(300, 9, 128), 96 => Body(300, 9, 160),
            128 => Body(600, 11, 400), _ => Body(600, 12, 400)
        };
        var nested = RuntimeShapeMatcher.Locate(image, catalog, data, NestedGraph, t => t);
        checks.True(nested.Count == 1 && nested[0].Entry == 32, "第二层完整被调形状消除转发入口的歧义");
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, e => e == 128 ? null : NestedGraph(e), t => t).Count == 0,
            "数据要求的第二层函数无法完整提升时拒绝定位");
        NativeFunction Indirect(int offset, TermKind targetKind = TermKind.Operation)
        {
            var terms = new TermTable(); var entry = new BlockIdentity();
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var target = targetKind switch
            {
                TermKind.Unknown => terms.Unknown(64, new("fixture.target", "未知调用目标")),
                TermKind.Undefined => terms.Undefined(64),
                _ => terms.Apply(new CoreOperator(CoreOperation.Add), 64, frame, terms.Constant(offset, 64))
            };
            var builder = new FunctionBuilder(terms, entry, 64, new(frame));
            builder.Blocks.Add(new(entry, [], [new Call(new(), new ComputedTarget(target), [], [])], new Return([])));
            return builder.Freeze();
        }
        var indirectShape = RuntimeReferenceShape.Create(Indirect(4), t => t);
        checks.True(indirectShape is not null && indirectShape.Text != RuntimeReferenceShape.Create(Indirect(8), t => t)!.Text,
            "完整间接目标按项逐项比较，保留目标计算的普通常量");
        checks.True(RuntimeReferenceShape.Create(Indirect(4, TermKind.Unknown), t => t) is null, "含未知项的间接目标不作为形状依据");
        checks.True(RuntimeReferenceShape.Create(Indirect(4, TermKind.Undefined), t => t) is null, "含未定义位的间接目标不作为形状依据");
        data = data with { Entries = [new(function.MangledName, 8, indirectShape!.Text, [])] };
        image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable)] };
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, _ => Indirect(4), t => t).Count == 0,
            "间接调用不冒充直接被调或具名导入的印证");
        var leafTerms = new TermTable(); var leafEntry = new BlockIdentity();
        var leafBuilder = new FunctionBuilder(leafTerms, leafEntry, 64, new(leafTerms.Atom(new RootAtom(AddressRoot.Frame), 64)));
        leafBuilder.Blocks.Add(new(leafEntry, [], [], new Return([])));
        var plain = leafBuilder.Freeze(); var plainShape = RuntimeReferenceShape.Create(plain, t => t)!;
        data = data with { Entries = [new(function.MangledName, 4, plainShape.Text, [])] };
        image = new InputMemoryImage { Functions = [new(32, 4, FunctionEvidence.UnwindTable)] };
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, _ => plain, t => t).Count == 0,
            "没有调用印证的叶子即使形状唯一，也不猜目录身份");
        // 导出身份本身不要求提升末端目标；每条边的来源节点则必须逐项复核。
        data = data with { Entries = [new(function.MangledName, 4, null, []) { Anchor = "export:entry" }] };
        image = new InputMemoryImage { Exports = [new("entry", new PointerTarget.Internal(32))],
            Functions = [new(32, 4, FunctionEvidence.UnwindTable)], TryRegions = [new(32, 4, 128, [])] };
        var lifts = 0;
        var direct = RuntimeShapeMatcher.Locate(image, catalog, data, _ => { lifts++; return null; }, t => t);
        checks.True(direct.Count == 1 && direct[0].Entry == 32 && direct[0].Location.Evidence == RuntimeLocationEvidence.ExportAnchor && lifts == 0,
            "export:名字 直接定位，目标有异常区域且不能提升也不调用提升器");
        var sourceShape = RuntimeReferenceShape.Create(Body(500, 7, 64), t => t, image)!;
        data = data with { Entries = [new(function.MangledName, 16, null, []) { Anchor = "export:entry>0" }],
            AnchorShapes = [new("export:entry", 8, sourceShape.Text)] };
        image = new InputMemoryImage { Exports = [new("entry", new PointerTarget.Internal(32))],
            Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable)] };
        lifts = 0;
        var followed = RuntimeShapeMatcher.Locate(image, catalog, data, e => { lifts++; return e == 32 ? Body(500, 7, 64) : null; }, t => t);
        checks.True(followed.Count == 1 && followed[0].Entry == 64 && lifts == 1, "export:名字>k 按直接调用序号定位且不提升末端");
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, _ => Body(500, 8, 64), t => t).Count == 0,
            "导出来源函数形状不同则锚点失败");
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, _ => null, t => t).Count == 0, "来源节点提升失败则锚点失败");
        var resolver = new RuntimeExportAnchorResolver(new InputMemoryImage(), data, _ => null);
        checks.True(resolver.Resolve("export:entry", out _) is null, "缺少导出则锚点失败");
        data = data with { Entries = [new(function.MangledName, 24, null, []) { Anchor = "export:entry>0>0" }],
            AnchorShapes = [new("export:entry", 8, sourceShape.Text), new("export:entry>0", 16, callee.Text)] };
        image = new InputMemoryImage { Exports = [new("entry", new PointerTarget.Internal(32))],
            Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable), new(128, 24, FunctionEvidence.UnwindTable)] };
        var multi = RuntimeShapeMatcher.Locate(image, catalog, data, e => e switch
            { 32 => Body(500, 7, 64), 64 => Body(300, 9, 128), 128 => Body(600, 11, 256), _ => null }, t => t);
        checks.True(multi.Count == 1 && multi[0].Entry == 128, "导出加两层调用路径逐层完整复核，末端不必提升");
        data = data with { Entries = [new(function.MangledName, 8, reference.Text,
            [new(16, callee.Text) { Anchor = "export:callee" }])], AnchorShapes = [] };
        image = new InputMemoryImage { Exports = [new("callee", new PointerTarget.Internal(64))],
            Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(48, 8, FunctionEvidence.UnwindTable),
                new(64, 16, FunctionEvidence.UnwindTable), new(96, 16, FunctionEvidence.UnwindTable)] };
        NativeFunction? Wrappers(ulong e) => e switch
            { 32 => Body(500, 7, 64), 48 => Body(500, 7, 96), _ => Body(300, 9, 128) };
        var distinguished = RuntimeShapeMatcher.Locate(image, catalog, data, Wrappers, t => t);
        checks.True(distinguished.Count == 1 && distinguished[0].Entry == 32, "被调锚点按身份区分两个被调形状相同的转发函数");
        data = data with { Entries = [data.Entries[0] with { Callees = [new(16, callee.Text) { Anchor = "export:absent" }] }] };
        var ambiguousReasons = new Dictionary<string, string>();
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, Wrappers, t => t, ambiguousReasons).Count == 0
            && ambiguousReasons[function.MangledName].Contains("2 个入口", StringComparison.Ordinal), "锚点失败回退形状；被调地址不同的候选仍然歧义");
        image = new InputMemoryImage { Exports = [new("entry", new PointerTarget.Internal(48))],
            Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(48, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable)] };
        data = data with { Entries = [data.Entries[0] with { Anchor = "export:entry", Callees = [new(16, callee.Text)] }] };
        var conflictReasons = new Dictionary<string, string>();
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data,
            e => e == 48 ? Body(500, 8, 64) : Lift(e), t => t, conflictReasons).Count == 0
            && conflictReasons[function.MangledName].Contains("导出锚点与形状", StringComparison.Ordinal), "自己的锚点和形状结果矛盾时两者都不采纳");
        var callImage = new InputMemoryImage { Executable = true };
        callImage.Put(32, 0x94000038, 4); // BL 256
        callImage.Put(36, 0x1400003f, 4); // B 288
        callImage.Put(40, 0x14000002, 4); // B 48，范围内分支
        callImage.Put(44, 0x97fffffd, 4); // BL 32，负向偏移
        var directSites = Arm64DirectCalls.ToCandidates(callImage, new(32, 32, FunctionEvidence.UnwindTable),
            new HashSet<ulong> { 32, 48, 256, 288 }).ToArray();
        checks.True(directSites.SequenceEqual(new (ulong, ulong)[] { (32, 256), (36, 288), (44, 32) }),
            "廉价索引保留前后向直接调用和跨范围尾调用，排除范围内普通分支");
        var metadataFunction = catalog.Functions.Single(f => !f.Recognition.UsageConditions.IsEmpty);
        data = data with { Entries = [new(metadataFunction.MangledName, 8, reference.Text, [new(16, callee.Text)])] };
        image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(48, 8, FunctionEvidence.UnwindTable),
            new(64, 16, FunctionEvidence.UnwindTable), new(96, 16, FunctionEvidence.UnwindTable)] };
        var layouts = new FieldLayouts(RuntimeSpec.Select(catalog.UnityVersion, catalog.Triple, catalog.DataModel), 8, 8);
        var binder = new MethodBinder(new(layouts, 64), new Aapcs64());
        RuntimeManagedUse Use(ulong target, int? address, int? alternative = null, bool merge = false, bool memory = false)
        {
            var terms = new TermTable(); var block = new BlockIdentity();
            var root = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(terms, block, 64, new(frame)) { ImageBase = root };
            Term Pointer(int offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, root, terms.Constant(offset, 64));
            var argument = address is { } offset ? Pointer(offset) : terms.Atom(new EntryAtom(new(SlotKind.Integer, 2)), 64);
            if (address is null) builder.Inputs.Add(new(new(SlotKind.Integer, 2), argument));
            Term? selector = alternative is not null ? terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64) : null;
            var merges = new List<Merge>(); var statements = new List<Statement>();
            if (alternative is { } other)
            {
                var condition = terms.Slice(selector!, 0, 1);
                if (merge)
                {
                    var left = new BlockIdentity(); var right = new BlockIdentity(); var join = new BlockIdentity();
                    builder.Blocks.Add(new(block, [], [], new Branch(condition, left, right)));
                    builder.Blocks.Add(new(left, [], memory ? [new MemoryWrite(new(), frame, 64, argument)] : [], new Jump(join)));
                    builder.Blocks.Add(new(right, [], memory ? [new MemoryWrite(new(), frame, 64, Pointer(other))] : [], new Jump(join)));
                    if (memory)
                    {
                        var read = new ReadIdentity(); argument = terms.Atom(new ResultAtom(read), 64);
                        statements.Add(new MemoryRead(read, frame, 64, argument));
                    }
                    else
                    {
                        var id = new MergeIdentity(); var result = terms.Atom(new ResultAtom(id), 64);
                        merges.Add(new(id, result, [new(left, argument), new(right, Pointer(other))]));
                        argument = result;
                    }
                    block = join;
                }
                else argument = terms.Apply(new CoreOperator(CoreOperation.Select), 64, condition, argument, Pointer(other));
            }
            var callId = new CallIdentity();
            var call = new Call(callId, new ImageFunction(target), [new(new(SlotKind.Integer, 0), argument)],
                [new(new(SlotKind.Integer, 0), terms.Atom(new ResultAtom(callId), 64))]);
            if (selector is not null) builder.Inputs.Add(new(new(SlotKind.Integer, 1), selector));
            statements.Add(call);
            builder.Blocks.Add(new(block, [.. merges], [.. statements], new Return([])));
            return new(target, builder.Freeze(), call);
        }
        checks.True(new[] { Use(32, 1024), Use(32, null), Use(32, 1024, 1536), Use(32, 1024, 1536, merge: true),
            Use(32, 1024, 1536, merge: true, memory: true) }.All(use => ExitChecker.Check(use.Function!).IsValid),
            "使用处合成输入满足原生 IR 出口契约");
        RuntimeManagedCaller Caller(ulong entry, RuntimeManagedUse[] sites) =>
            new(entry, sites.GroupBy(u => u.Target).ToDictionary(g => g.Key, g => g.Count()), () => sites);
        RuntimeManagedUse[] Valid(int count) => Enumerable.Range(0, count).Select(_ => Use(32, 1024)).ToArray();
        RuntimeManagedUse[] uses = [.. Valid(16), new(32, null, null), Use(32, 1024) with { Call = null }, Use(32, null)];
        var usageEvidence = new RuntimeUsageEvidence(image, binder, new SlotValidator(), _ => [Caller(100, uses)]);
        IReadOnlyList<(ulong Entry, RuntimeFunctionLocation Location)> ByUsage(Dictionary<string, string>? reasons = null) =>
            RuntimeShapeMatcher.Locate(image, catalog, data, Wrappers, t => t, reasons, usageEvidence: usageEvidence);
        var selected = ByUsage();
        var concurrentUsage = new RuntimeUsageEvidence(image, binder, new SlotValidator(),
            _ => uses.Select((use, i) => Caller((ulong)i, [use])), jobs: 4);
        var usageCandidates = new HashSet<ulong> { 32, 48 };
        checks.True(usageEvidence.Check(metadataFunction, usageCandidates).OrderBy(p => p.Key)
            .SequenceEqual(concurrentUsage.Check(metadataFunction, usageCandidates).OrderBy(p => p.Key)),
            "并行调用方检查保留每个候选的三类调用计数");
        checks.True(selected.Count == 1 && selected[0].Entry == 32
            && selected[0].Location.Source.Contains("满足 16，反例 0，未核实 3，核对 19/19", StringComparison.Ordinal),
            "有提升失败、调用未进入 IR 和不透明实参时仍可选中，并保存三类计数及核对范围");
        uses = [.. Valid(16), Use(32, 2048)];
        var usageReasons = new Dictionary<string, string>();
        checks.True(ByUsage(usageReasons).Count == 0 && usageReasons[metadataFunction.MangledName].Contains("满足 16，反例 1，未核实 0", StringComparison.Ordinal),
            "即使满足点足够且占比达标，一个反例也拒绝定位");
        uses = [.. Valid(16), Use(48, 1024), Use(48, 2048)];
        checks.True(ByUsage().Count == 0, "另一个候选有一个满足点时保持歧义，即使它也有反例");
        uses = [];
        checks.True(ByUsage().Count == 0, "空调用集不能作为使用处证据");
        uses = Valid(15);
        checks.True(ByUsage().Count == 0, "满足数不足 16 时不定位");
        uses = [.. Valid(16), .. Enumerable.Repeat(new RuntimeManagedUse(32, null, null), 4)];
        checks.True(ByUsage().Single().Entry == 32, "满足数为 16 且占比恰为 80% 时可选中");
        uses = [.. uses, new(32, null, null)];
        checks.True(ByUsage().Count == 0, "满足数足够但占比不到 80% 时不定位");
        uses = [.. Valid(15), Use(32, 1024, 1536)];
        checks.True(ByUsage().Single().Entry == 32, "选择项的所有有限来源都是合法槽地址时满足");
        uses = [.. Valid(16), Use(32, 1024, 2048)];
        checks.True(usageEvidence.Check(metadataFunction, usageCandidates)[32].Counterexamples == 1 && ByUsage().Count == 0,
            "选择项有一个非法槽来源时计为反例");
        uses = [Use(32, 1024, 1536, merge: true), Use(32, 1024, 1536, merge: true, memory: true),
            Use(32, 1024, 2048, merge: true), Use(32, 1024, 2048, merge: true, memory: true)];
        checks.True(usageEvidence.Check(metadataFunction, usageCandidates)[32] == new RuntimeUsageCounts(2, 2, 0, 4),
            "SSA 合流与内存合流均按全部有限来源判定");
        uses = [Use(32, null, 1536), Use(32, null, 2048, merge: true)];
        checks.True(usageEvidence.Check(metadataFunction, usageCandidates)[32] == new RuntimeUsageCounts(0, 0, 2, 2),
            "选择项或合流含不透明来源时计为未核实，不依据部分来源判满足或反例");
        uses = [.. Valid(2000), Use(32, 2048)];
        var reads = new System.Collections.Concurrent.ConcurrentBag<ulong>();
        RuntimeUsageEvidence Bounded(int jobs) => new(image, binder, new SlotValidator(), _ => uses.Select((use, i) =>
            new RuntimeManagedCaller((ulong)i, new Dictionary<ulong, int> { [use.Target] = 1 }, () =>
            { reads.Add((ulong)i); return [use]; })).Reverse(), jobs);
        var boundedSingle = Bounded(1).Check(metadataFunction, usageCandidates);
        var boundedParallel = Bounded(4).Check(metadataFunction, usageCandidates);
        checks.True(boundedSingle[32] == new RuntimeUsageCounts(2000, 0, 0, 2001)
            && boundedSingle.OrderBy(p => p.Key).SequenceEqual(boundedParallel.OrderBy(p => p.Key))
            && reads.Count == 4000 && reads.All(e => e < 2000),
            "超过 2000 点时只提升按入口排序的前 2000 点，线程数和来源枚举顺序不改变结果");
        uses = [.. Valid(1999), Use(32, 1024), Use(32, 2048)];
        var boundary = new RuntimeUsageEvidence(image, binder, new SlotValidator(), _ =>
            [Caller(100, uses[..1999]), Caller(200, uses[1999..])]);
        checks.True(boundary.Check(metadataFunction, usageCandidates)[32] == new RuntimeUsageCounts(2000, 1, 0, 2001),
            "预算边界包含同一调用方的全部调用点，保留其中反例");
        uses = Valid(16);
        data = data with { Entries = [data.Entries[0] with { Shape = plainShape.Text }] };
        checks.True(ByUsage().Count == 0, "使用处条件不能独立提供定位依据");
        return checks.Finish("运行时参考形状");
    }
    private sealed class SlotValidator : IRuntimeMetadataSlotValidator
    {
        public bool IsValid(ulong imageOffset) => imageOffset is 1024 or 1536;
    }
}
