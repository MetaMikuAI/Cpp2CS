using Cpp2CS.Native;
using Cpp2CS.IR;

public static class AsyncChecks
{
    public static void Layouts(Action<bool, string> check, string compiler)
    {
        Directory.CreateDirectory("artifacts");
        const string path = "artifacts/abi-layout-fixture.h";
        File.WriteAllText(path, """
            typedef float Real;
            struct Task { void* source; int16_t token; };
            struct Floats { Real values[4]; };
            struct Pair { float x; float y; };
            struct Nested { Pair pair; float z; };
            union Ambiguous { float x; int y; };
            struct RecordArray { Pair pairs[2]; };
            struct Overlay {
                union {
                    #pragma pack(push, 1)
                    int32_t word;
                    uint8_t first;
                    struct { uint8_t padding[3]; uint8_t last; };
                    #pragma pack(pop)
                };
            };
            struct Container { uint8_t prefix; Overlay payload; int32_t suffix; };
            struct Context;
            typedef void (*Callback)(const Context*, void**);
            struct WithCallback { uint8_t flag; Callback invoke; Overlay payload; };
            """);
        var layout = new HeaderLayout(path, compiler);
        check(layout.Shape("Task") is { Kind: Cpp2CS.Abi.ShapeKind.Composite, Size: 16, Alignment: 8 }, "Clang 实际布局保留 source/token 尾部 padding");
        check(layout.Shape("Real").Kind == Cpp2CS.Abi.ShapeKind.Float, "浮点 typedef 不误分配到 X 寄存器");
        check(layout.Shape("Floats") is { Kind: Cpp2CS.Abi.ShapeKind.HomogeneousFloat, ElementCount: 4 }, "浮点数组参与 HFA 分类");
        check(layout.Shape("Nested") is { Kind: Cpp2CS.Abi.ShapeKind.HomogeneousFloat, ElementCount: 3 }, "嵌套结构体的浮点成员参与 HFA 分类");
        check(layout.Shape("Ambiguous").Kind == Cpp2CS.Abi.ShapeKind.Unknown, "union 未确认 ABI 不猜测寄存器类别");
        check(layout.Shape("RecordArray").Kind == Cpp2CS.Abi.ShapeKind.Unknown, "未展开的结构体数组 ABI 保持未知");
        check(layout.Size("Overlay") == 4 && layout.Size("Container") == 12, "匿名重叠聚合保留完整声明并由 Clang 计算实际布局");
        check(layout.ContainingField("Container", 8, 4) is { Name: "suffix", Type: "int32_t" }, "匿名聚合不阻断外层后续字段的偏移恢复");
        check(layout.Members("Overlay").Length == 0 && layout.ContainingField("Container", 4, 1) is null,
            "重叠存储不按声明顺序猜测活动字段");
        check(layout.Shape("Overlay").Kind == Cpp2CS.Abi.ShapeKind.Unknown && layout.Shape("Container").Kind == Cpp2CS.Abi.ShapeKind.Unknown,
            "匿名重叠聚合的 ABI 分类保持未确认");
        check(layout.Size("Callback") == 8 && layout.Size("WithCallback") == 24 &&
            layout.ContainingField("WithCallback", 8, 8) is { Name: "invoke", Type: "Callback" },
            "函数指针别名参与布局，参数所指的不完整类型不要求值布局");
    }
    public static void Run(Action<bool, string> check)
    {
        byte[] bytes = [0xff, 3, 14, 1, 4, 0, 4, 8, 3, 0, 0, 1, 0x7d, 0x78, 0x56, 0x34, 0x12];
        var regions = ExceptionTable.Read((at, size) => bytes.AsSpan((int)at, size).ToArray(), _ => throw new InvalidOperationException(), 0, 0x100, 0x110);
        check(regions is [{ LandingPad: 0x108, Actions: [{ Filter: 1, TypeInfo: 0x12345678, NextOffset: -3 }, { Filter: 0, Kind: "cleanup" }] }],
            "LSDA 负相对偏移动作链与逆序类型表准确解析");
        Array.Clear(bytes, 13, 4);
        var all = ExceptionTable.Read((at, size) => bytes.AsSpan((int)at, size).ToArray(), _ => 0, 0, 0x100, 0x110);
        check(all[0].Actions[0].Kind == "catch-all" && all[0].Actions[1].Kind == "cleanup", "catch-all 和 cleanup 独立保留");
        Instruction I(ulong pc, string op, long? target = null) => new(pc, op, "", target is null ? [] : [new(2, null, target.Value, null, null, 0, 0, 0, 0)], false, false, "");
        Instruction[] code = [I(0x100, "bl", 0x200), I(0x104, "ret"), I(0x108, "b", 0x108), I(0x10c, "ret")];
        var flow = NativeControlFlow.Build(code, new(0x100, 0x110, null) { Lsda = 0, ExceptionRegions = regions }, _ => true);
        check(flow.Nodes[0].Edges.All(e => e.Kind != "normal-return") && flow.Nodes[0].Edges.Any(e => e.Target == 0x108),
            "noreturn 调用仍可进入异常处理器");
        check(flow.Cycles is [[0x108]] && flow.Nodes[2].Reachable && !flow.Nodes[1].Reachable, "仅通过异常边可达的循环不被丢弃");
        check(flow.Nodes[0].Edges.All(e => e.Target is not null), "typed catch 后有 cleanup 时异常不能绕过清理直接展开");
        var typedOnly = regions[0] with { Actions = [regions[0].Actions[0]] };
        var typedFlow = NativeControlFlow.Build(code, new(0x100, 0x110, null) { Lsda = 0, ExceptionRegions = [typedOnly] }, _ => true);
        check(typedFlow.Nodes[0].Edges.Any(e => e.Kind == "unmatched-exception-unwind"), "只有 typed catch 时保留不匹配异常展开");
        var catchAllFlow = NativeControlFlow.Build(code, new(0x100, 0x110, null) { Lsda = 0, ExceptionRegions = all }, _ => true);
        check(catchAllFlow.Nodes[0].Edges.All(e => e.Target is not null), "catch-all 没有虚构的不匹配异常出口");
        var cleanupFlow = NativeControlFlow.Build(code, new(0x100, 0x110, null) { Lsda = 0, ExceptionRegions = [new(0x100, 0x104, 0x108, 0)] }, _ => false);
        check(cleanupFlow.Nodes[0].Edges.Any(e => e.Kind == "exception-cleanup") && cleanupFlow.Problems.Length == 0, "cleanup 与普通返回分开建边");
        var missing = NativeControlFlow.Build(code, new(0x100, 0x110, null) { Lsda = 0 }, _ => false);
        check(missing.Nodes[0].Edges.Any(e => e.Kind == "exception-missing-callsite-terminate"), "有 LSDA 但没有 call-site 不当作无处理器 unwind");
        var state = new NativeState();
        var region = new RegionId("frame", RegionKind.Stack);
        var task = new NativeValue(new InputBits("task", 128), "task-value", new NameExpression("task"));
        NativeValues.StoreStack(state, region, 0, NativeValues.Slice(task, 0, 64), "x0");
        NativeValues.StoreStack(state, region, 8, NativeValues.Slice(task, 64, 64), "x1");
        check(NativeValues.LoadStack(state, region, 0, 16).Bits == task.Bits, "双寄存器返回重组为同一个 128 位值");
        check(NativeValues.LoadStack(state, region, 8, 2) is { Bits: SliceBits { Offset: 64, BitWidth: 16 }, Expression: SliceExpression { BitOffset: 64, BitWidth: 16 } },
            "awaiter token 从第二寄存器低 16 位提取，值与表达式宽度一致");
        var token = new NativeValue(BitOps.Constant(0xbeef, 16), "uint16_t", new ConstantExpression(0xbeef));
        NativeValues.StoreStack(state, region, 8, token, "token-write");
        check(NativeValues.LoadStack(state, region, 0, 8).Bits == BitOps.Slice(task.Bits, 0, 64) &&
            NativeValues.LoadStack(state, region, 10, 6).Bits == BitOps.Slice(task.Bits, 80, 48), "部分覆盖保留 source 与尾部字节来源");
        var returned = NativeValues.LoadStack(state, region, 0, 16);
        check(returned.Expression is ComposeExpression && returned.Bits.Width == 128, "部分改写后聚合不视为原始返回值");
        state.Stack = state.Stack.Invalidate("unknown-call-write");
        check(NativeValues.LoadStack(state, region, 0, 8).Expression is UnknownExpression, "失效内存不能沿用旧栈表达式");
    }
}
