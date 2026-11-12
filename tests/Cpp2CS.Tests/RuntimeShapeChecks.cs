using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Runtime;

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
        var data = new RuntimeShapeCatalog(1, catalog.UnityVersion, catalog.Triple, catalog.DataModel,
            [new(function.MangledName, 8, reference.Text, [new(16, callee.Text)])]);
        var image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable)] };
        NativeFunction? Lift(ulong entry) => entry == 64 ? Body(300, 9, 400) : Body(500, 7, 64);
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, Lift, t => t).Count == 1, "唯一形状与调用关系一致才定位");
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, e => Body(500, 7, 64), t => t).Count == 0, "被调形状矛盾拒绝定位");
        image = new InputMemoryImage { Functions = [new(32, 8, FunctionEvidence.UnwindTable), new(48, 8, FunctionEvidence.UnwindTable), new(64, 16, FunctionEvidence.UnwindTable)] };
        checks.True(RuntimeShapeMatcher.Locate(image, catalog, data, Lift, t => t).Count == 0, "两个同形入口不任取一个");
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
        return checks.Finish("运行时参考形状");
    }
}
