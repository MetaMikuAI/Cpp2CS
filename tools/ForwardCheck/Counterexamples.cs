using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Emit;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Facts;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using MethodBody = Cpp2CS.Kernel.Forward.MethodBody;
using M = Cpp2CS.Model;

namespace Cpp2CS.Tools.ForwardCheck;

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

    public static int Run(string assemblies, Dictionary<string, string> options)
    {
        using var metadata = ModelInput.Load(assemblies, options);
        var items = new List<Item>
        {
            new("参照类的符号登记到不同操作", "vm/Exception.cpp：RaiseNullReferenceException 与 RaiseDivideByZeroException 抛出不同的异常", () =>
            {
                const string nullReference = "_ZN6il2cpp2vm9Exception27RaiseNullReferenceExceptionEv";
                const string divideByZero = "_ZN6il2cpp2vm9Exception26RaiseDivideByZeroExceptionEv";
                if (new RuntimeName([nullReference], "符号").Operation?.Exception != ExceptionKind.NullReference ||
                    new RuntimeName([divideByZero], "符号").Operation?.Exception != ExceptionKind.DivideByZero)
                    return "单个符号的异常种类与运行时不符";
                return new RuntimeName([nullReference, divideByZero], "参照类").Operation == null ? null : "冲突的参照类取得了运行时操作";
            }),

            new("值类型只有填充位不同", "设计 7.10；核心库 DateTimeOffset 的实际成员布局；ValueType::InternalEquals 逐字段比较",
                () => PaddingComparison(metadata, padding: true)),
            new("值类型一个成员的一位不同", "设计 7.10；核心库 DateTimeOffset 的实际成员布局；ValueType::InternalEquals 逐字段比较",
                () => PaddingComparison(metadata, padding: false)),

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

            // ECMA-335 III.4.28 stfld：obj 是托管指针时，它指向的值类型须含有该字段；III.1.8.1.2.1：托管指针只有指向同一类型才相容。
            // 语料 Fields.WriteNested 的真实 IL 是 ldarg.0; ldflda Outer::Inner; ldarg.1; stfld Inner::X。内层的值位于外层偏移 0 处，
            // 两个地址数值相同；直接拿外层的地址写内层的字段，原生效果相同，但写出的 IL 类型不对。展开必须拒绝后一种写法。
            new("经地址写字段须指向含该字段的类型", "ECMA-335 III.4.28、III.1.8.1.2.1；语料 Fields.WriteNested 的真实 IL", () =>
            {
                var outer = new TypeShape(StackKind.ByRef, 64, false, new EntityRef(EntityKind.Type, 1));
                var view = new NestedFieldView();
                byte[] proper = [0x02, 0x7c, 1, 0, 0, 4, 0x03, 0x7d, 2, 0, 0, 4, 0x2a];
                byte[] direct = [0x02, 0x03, 0x7d, 2, 0, 0, 4, 0x2a];
                var graph = Expand(proper, null, [outer, Int32], metadata: view);
                if (graph.Blocks.Sum(b => b.Occurrences.Length) != 1) return "真实 IL 的写法应展开成一次写入";
                return Rejected(() => Expand(direct, null, [outer, Int32], metadata: view), "目录里没有适用的变体");
            }),

            // 设计 6.2“展开”：目标唯一的调用等于被调方法的效果图；9.1：展开只对目标唯一的调用成立。
            // 语料 Construction.NodeSwapped 的真实 IL 在 newobj 之前有 call Support::Opaque(int32); pop，Opaque 的方法体是
            // ldarg.0; ldc.i4.s 0x5a; xor; ret。原生代码把它内联后整个消去，恢复出的 IL 没有这次调用，二者等价。
            // 被调方法写静态字段时（ECMA-335 III.4.30 stsfld），少了这次调用就少了一次类初始化与一次写入；另一侧自己触发了类初始化
            // （III.4.14 ldsfld）时，仍少一次写入。调用的结果被用到时，少了它结果就不同。经虚表的调用（III.4.2 callvirt）目标不唯一，
            // 方法操作数的方法体不是它的含义。这几种都必须判为不等价。
            new("IL 对照里少一次调用", "设计 6.2、9.1；ECMA-335 III.3.19、III.4.2、III.4.14、III.4.30；语料 Construction.NodeSwapped 的真实 IL", () =>
            {
                const int Pure = 0x06000001, Writer = 0x06000002, First = 0x06000003, Second = 0x06000004;
                byte[] pure = [0x02, 0x1f, 0x5a, 0x61, 0x2a];                        // ldarg.0; ldc.i4.s 0x5a; xor; ret
                byte[] writes = [0x02, 0x80, 1, 0, 0, 4, 0x02, 0x2a];                // ldarg.0; stsfld F; ldarg.0; ret
                byte[] dropped = [0x02, 0x2a];                                       // ldarg.0; ret
                byte[] reads = [0x7e, 1, 0, 0, 4, 0x26, 0x02, 0x2a];                 // ldsfld F; pop; ldarg.0; ret
                byte[] Discard(int method) => [0x02, 0x28, (byte)method, 0, 0, 6, 0x26, 0x02, 0x2a];   // ldarg.0; call M; pop; ldarg.0; ret
                byte[] used = [0x02, 0x28, 1, 0, 0, 6, 0x2a];                        // ldarg.0; call Pure; ret
                var bodies = new Dictionary<long, byte[]> { [Pure] = pure, [Writer] = writes, [First] = [0x2a], [Second] = [0x2a] };
                bool Same(byte[] left, byte[] right, Dictionary<long, byte[]> known) =>
                    Compare(left, right, Int32, [Int32], known).Verdict == Verdict.Proved;

                if (!Same(Discard(Pure), dropped, bodies) || !Same(dropped, Discard(Pure), bodies)) return "被调方法没有可观察的效果、结果被丢弃：少了这次调用应当等价";
                if (Same(Discard(Pure), dropped, [])) return "没有被调方法的方法体时不能展开，却判了等价";
                if (!Same(Discard(Writer), writes, bodies)) return "被调方法的写入展开后应与直接写入等价";
                if (Same(Discard(Writer), dropped, bodies)) return "被调方法写静态字段，少了这次调用却判了等价";
                var unwritten = Compare(Discard(Writer), reads, Int32, [Int32], bodies);
                if (unwritten.Verdict == Verdict.Proved) return "被调方法写静态字段，另一侧只触发类初始化、没有写入，却判了等价";
                if (!unwritten.Detail.Contains("没有写")) return $"反驳的原因不是少了写入：{unwritten.Detail}";
                if (!Same(used, pure, bodies)) return "调用的结果应等于被调方法的返回值";
                if (Same(used, dropped, bodies)) return "调用的结果被用到，少了这次调用却判了等价";

                // 两次经虚表的调用，方法操作数不同。即使两个方法操作数的方法体都是空的，也不能拿它们当调用的含义。
                var asked = new List<long>();
                byte[] Virtual(int method) => [0x02, 0x6f, (byte)method, 0, 0, 6, 0x2a];   // ldarg.0; callvirt M; ret
                var result = Compare(Virtual(First), Virtual(Second), null, [Reference], bodies, asked);
                if (result.Verdict == Verdict.Proved) return "两次目标不唯一的调用方法不同，却判了等价";
                return asked.Count == 0 ? null : "目标不唯一的调用被展开了";
            }),

            // ECMA-335 III.4.31 throw：抛出的是栈顶的那个对象。设计 6.1：抛出是事件，同一个事件须同操作数。
            // 两个引用形参都非空的路径上，一侧抛出第一个、另一侧抛出第二个，必须判为不等价。
            new("抛出的须是同一个对象", "ECMA-335 III.4.31；设计 6.1", () =>
            {
                // ldarg.0; brfalse.s 末尾; ldarg.1; brfalse.s 末尾; ldarg.N; throw; ret
                byte[] Throws(byte which) => [0x02, 0x2c, 5, 0x03, 0x2c, 2, which, 0x7a, 0x2a];
                if (Compare(Throws(0x02), Throws(0x02), null, [Reference, Reference], []).Verdict != Verdict.Proved) return "两侧抛出同一个对象应当等价";
                var result = Compare(Throws(0x02), Throws(0x03), null, [Reference, Reference], []);
                if (result.Verdict == Verdict.Proved) return "两侧抛出不同的对象，却判了等价";
                return result.Detail.Contains("异常对象不同") ? null : $"反驳的原因不是抛出的对象：{result.Detail}";
            }),

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
            new("局部变量的初始化标志", "ECMA-335 II.25.4.4、I.12.3.2.2", () => InitLocals(metadata)),

            // ---- 核对工具的元数据 ----

            // docs/前端.md 第 7 节：模型里每个类型、方法、字段有一个稳定的编号。Box<int>.Call 与 Box<uint>.Call 是两个方法。
            new("泛型实例的方法身份", "docs/前端.md 第 7 节", () => GenericMembers(metadata)),

            // docs/前端.md 第 7 节：同一个类型只有一个编号。签名里的 int32、string 与核心库里的 System.Int32、System.String 是同一个类型。
            new("基本类型的身份", "docs/前端.md 第 7 节", () => CoreTypes(metadata)),

            new("List<string> 不能赋给 List<object>", "ECMA-335 I.8.7.1、II.9.5；核心库 List<T>", () =>
            {
                var facts = metadata.Facts;
                var strings = facts.TypeEntity(CoreCollection(metadata, "List`1", "String"));
                var objects = facts.TypeEntity(CoreCollection(metadata, "List`1", "Object"));
                return new EntityFacts(facts).Assignable(strings, objects) ? "接受了实参不同的列表" : null;
            }),

            new("派生类只能赋给实参相符的泛型基类", "ECMA-335 I.8.7.1、II.9.1；核心库 GenericEqualityComparer<T> 继承 EqualityComparer<T>", () =>
            {
                var facts = metadata.Facts;
                var relations = new EntityFacts(facts);
                var derived = CoreCollection(metadata, "GenericEqualityComparer`1", "Int32");
                var ints = CoreCollection(metadata, "EqualityComparer`1", "Int32");
                var longs = CoreCollection(metadata, "EqualityComparer`1", "Int64");
                if (!relations.Assignable(facts.TypeEntity(derived), facts.TypeEntity(ints))) return "没有识别 EqualityComparer<int> 基类";
                return relations.Assignable(derived, longs) ? "接受了 EqualityComparer<long> 基类" : null;
            }),

            new("数组的基类与泛型接口", "ECMA-335 I.8.7.1、I.8.9.1；语料 Fields.ReadArray 的 int[] 形参", () =>
            {
                var facts = metadata.Facts;
                var relations = new EntityFacts(facts);
                var array = new M.ArrayType(facts.CoreType("Int32"), 1, true);
                var ints = facts.TypeEntity(array);
                if (!relations.Assignable(ints, facts.TypeEntity(facts.CoreType("Array")))) return "没有识别 System.Array 基类";
                if (!relations.Assignable(ints, relations.SystemObject)) return "没有识别 System.Object 基类";
                if (relations.Assignable(ints, facts.TypeEntity(facts.CoreType("String")))) return "数组可赋给 System.String";
                if (relations.Assignable(array, CoreCollection(metadata, "IList`1", "Int32"))) return "接受了尚未支持的数组泛型接口";
                return relations.ArrayInterfaceRejections == 1 ? null : "未计入数组泛型接口的拒绝";
            }),

            new("泛型接口按定义的实参比较", "ECMA-335 I.8.7.1、II.9.5；核心库 List<T> 的接口声明", () =>
            {
                var facts = metadata.Facts;
                var relations = new EntityFacts(facts);
                var objects = CoreCollection(metadata, "List`1", "Object");
                var listInterface = CoreCollection(metadata, "IList`1", "Object");
                if (!relations.Assignable(facts.TypeEntity(objects), facts.TypeEntity(listInterface))) return "没有识别 IList<object> 接口";
                if (relations.Assignable(objects, CoreCollection(metadata, "IList`1", "String"))) return "接受了实参不同的不变接口";
                var strings = CoreCollection(metadata, "List`1", "String");
                var enumerable = CoreCollection(metadata, "IEnumerable`1", "Object");
                if (!relations.Assignable(enumerable, enumerable)) return "相同接口被当作变体转换拒绝";
                if (relations.Assignable(strings, enumerable)) return "接受了尚未支持的协变接口";
                return relations.VariantInterfaceRejections == 1 ? null : "未计入变体接口的拒绝";
            }),

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

            // 设计 7.3、7.7：分情况只按结构展开，情况行带上所选各条入边的文字；可行与否、条件下的取值问路径条件格。
            // 入口按 c 走两条平行边，分别把 (8, c)、(9, c) 传给 (v, k)，返回 Select(k, v, 0)：c 为 1 时是 8，为 0 时是 0。
            // 结构上有四行。经假边而选择条件 c=1 的一行（结果 9）、经真边而选择条件 c=0 的一行（结果 0），入边的文字与选择条件矛盾，
            // 格把这两行剔除；留下经真边的 8 与经假边的 0。
            new("分情况的不可行行", "设计 7.3、7.7", () =>
            {
                var b = new SnapshotBuilder(64);
                var p = b.Terms;
                var c = b.EntryParameter(Integer(0), 1);
                var ra = b.EntryParameter(Link, 64);
                var sp = b.EntryParameter(Stack, 64);
                var join = b.Block(8, 1, 64, 64);
                b.Terminate(b.Entry, Terminator.Branch(c, Exit.To(join, p.Constant(8, 8), c, ra, sp), Exit.To(join, p.Constant(9, 8), c, ra, sp)));
                var x = p.Select(b.Parameter(join, 1), b.Parameter(join, 0), p.Zero(8));
                b.SetReturnSlots((Integer(0), 8), (Link, 64), (Stack, 64));
                b.Return(join, x, b.Parameter(join, 2), b.Parameter(join, 3));
                var graph = b.Build();
                var table = new ValueSources(graph, p).SplitCases(new(join, 0), [x]);
                var empty = PathConditions.Empty(p);
                string Describe(Case row) => $"[{string.Join(" ", row.Edges)}] {string.Join(" ∧ ", row.Conditions)} → {row.Terms[0]}";
                if (!table.Complete || table.Cases.Length != 4) return $"情况表应有四行：{string.Join(" | ", table.Cases.Select(Describe))}";
                // 入边（真边为第 0 个出口）与结果 → 是否可行。
                var expected = new Dictionary<(int Exit, Term Result), bool>
                {
                    [(0, p.Constant(8, 8))] = true, [(0, p.Zero(8))] = false, [(1, p.Constant(9, 8))] = false, [(1, p.Zero(8))] = true,
                };
                foreach (var row in table.Cases)
                {
                    if (row.Edges.Length != 1 || row.Edges[0].Source != graph.Entry || !expected.Remove((row.Edges[0].Exit, row.Terms[0]), out bool feasible))
                        return $"多出的行：{Describe(row)}";
                    var edge = new PathLiteral(LiteralKind.Condition, c, row.Edges[0].Exit == 0 ? 1 : 0, default);
                    if (!row.Conditions.Contains(edge)) return $"情况行没有入边的文字：{Describe(row)}";
                    var values = CaseRows.Evaluate(row, empty, p);
                    if ((values is not null) != feasible) return $"{(feasible ? "剔除了可行的行" : "没有剔除不可行的行")}：{Describe(row)}";
                    if (values is { } v && v[0] != row.Terms[0]) return $"可行的行求值之后变了：{Describe(row)} → {v[0]}";
                }
                return null;
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

            // ---- 路径条件 ----

            // 设计 7.7：加入知识之后矛盾时得到空；7.4：运行时不可变的位置不被写入改变。语料 ArrayStore.StoreThenLoad 的原生代码
            // 先读数组长度做下标检查，写元素之后再读一次长度做第二次检查。长度登记为不可变之后两次读取是同一个值，
            // “第一次检查通过”与“第二次检查不通过”不能同时成立。两条文字以哪种次序加入，结果都须是矛盾。
            new("不可变位置上的两次读取使检查矛盾", "设计 7.4、7.7；语料 ArrayStore.StoreThenLoad 的原生代码", ImmutableContradiction),

            // 同上：写入前后两次读同一个不可变位置，一次已知等于 5，一次已知等于 7。登记不可变之后两次读取是同一个值，不能同时等于两个常量。
            new("不可变位置上的两次读取等于不同的常量", "设计 7.4、7.7", ImmutableConstants),

            // 设计 7.4：登记的取值范围与成立的比较一起供区间判定使用。同一个值有几条上界时用最紧的一条，与登记和文字的次序无关：
            // 数组长度登记的范围（不超过 0xFFFFFFF0）较松，下标检查 x < 15 给出的界较紧；后者成立时 x 的最高位为 0，符号扩展就是零扩展。
            new("区间判定取最紧的上界", "设计 7.4、7.7", TightestBound),

            // ---- 下降 ----

            // ECMA-335 III.3.18 brtrue：值非零（真）时转移。语料 Control.Conditional 的真实 IL 是
            // ldarg.0; brtrue.s L; ldarg.2; ret; L: ldarg.1; ret——条件成立时返回第 1 个形参。下降把选择写成带栈上汇合的转移，
            // 核对表达式时读出的项须与真实 IL 两条路径合成的选择相同；两支互换的写法读出的项须与它不同。
            new("选择的两支不能互换", "ECMA-335 III.3.18 brtrue；语料 Control.Conditional 的真实 IL", SelectArms),

            // ---- 写法的合法性 ----

            // ECMA-335 III.1.8.1.4：构造函数返回之前，须对 this 调用过本类或直接基类的构造函数；III.3.19：call 构造函数只用于此；
            // III.4.2：callvirt 不用于构造函数，值类型的方法不经虚表。行为相同的写法（直接调用祖父类的构造函数、对值类型的方法用 callvirt）
            // 通得过共同执行，通不过验证。取核心库里第一条三层的继承链与第一个带实例方法的值类型。
            new("调用的写法须通得过验证", "ECMA-335 III.1.8.1.4、III.3.19、III.4.2；设计 9.3；核心库的类型定义", () => CallForms(metadata)),
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

    private static string? ImmutableContradiction()
    {
        var p = new TermPool();
        var array = p.EntryParameter(0, Integer(0), 64);
        var index = p.Slice(p.EntryParameter(0, Integer(1), 64), 0, 32);
        var address = p.Add(array, p.Constant(0x18, 64));
        // 第一次读取在写入之前（历元 1），第二次在一次不能证明不重叠的写入之后（版本由那次写入给出）。
        var before = p.Attribute(new AttributeId(KernelAttributes.Load), 32, address, p.Constant(1, 32));
        var after = p.Attribute(new AttributeId(KernelAttributes.LoadAfter), 32, address, p.EntryParameter(0, Integer(2), 64));
        foreach (bool passedFirst in (bool[])[true, false])
        {
            (Term Condition, bool Value)[] literals = [(p.Ult(index, before), true), (p.Ult(index, after), false)];
            if (!passedFirst) Array.Reverse(literals);
            PathConditions? conditions = PathConditions.Empty(p);
            foreach (var (condition, value) in literals) conditions = conditions?.With(condition, value);
            if (conditions is null) return "登记不可变之前两条检查就被判为矛盾";
            if (conditions.WithImmutable(address, 32) is not null) return $"{(passedFirst ? "先加第一次检查" : "先加第二次检查")}：登记不可变之后仍判为相容";
        }
        return null;
    }

    private static string? ImmutableConstants()
    {
        var p = new TermPool();
        var array = p.EntryParameter(0, Integer(0), 64);
        var address = p.Add(array, p.Constant(0x18, 64));
        var before = p.Attribute(new AttributeId(KernelAttributes.Load), 32, address, p.Constant(1, 32));
        var after = p.Attribute(new AttributeId(KernelAttributes.LoadAfter), 32, address, p.EntryParameter(0, Integer(2), 64));
        foreach (bool beforeFirst in (bool[])[true, false])
        {
            Term[] equalities = [p.Eq(before, p.Constant(5, 32)), p.Eq(after, p.Constant(7, 32))];
            if (!beforeFirst) Array.Reverse(equalities);
            PathConditions? conditions = PathConditions.Empty(p);
            foreach (var equality in equalities) conditions = conditions?.With(equality, true);
            if (conditions is null) return "登记不可变之前两条等式就被判为矛盾";
            if (conditions.WithImmutable(address, 32) is not null) return $"{(beforeFirst ? "先加写入之前的读取" : "先加写入之后的读取")}：登记不可变之后仍判为相容";
        }
        return null;
    }

    private static string? TightestBound()
    {
        var p = new TermPool();
        var x = p.Slice(p.EntryParameter(0, Integer(0), 64), 0, 32);
        var widened = p.SignExtend(x, 64);
        // 15 与 0xFFFFFFE1 都不是 2 的幂：比较保持为无符号小于（小于 2 的幂的比较会化成高位全零）。
        foreach (bool tightFirst in (bool[])[true, false])
        {
            (Term Condition, bool Value)[] literals = [(p.Ult(x, p.Constant(15, 32)), true), (p.Ult(x, p.Constant(0xFFFFFFE1, 32)), true)];
            if (!tightFirst) Array.Reverse(literals);
            PathConditions? conditions = PathConditions.Empty(p).WithUpperBound(x, 0xFFFFFFF0);
            foreach (var (condition, value) in literals) conditions = conditions?.With(condition, value);
            if (conditions is null) return "几条上界被判为矛盾";
            if (conditions.Evaluate(widened) != p.ZeroExtend(x, 64)) return $"{(tightFirst ? "先加较紧的界" : "先加较松的界")}：符号扩展没有化成零扩展";
        }
        return null;
    }

    private static string? SelectArms()
    {
        var boolean = new TypeShape(StackKind.Int32, 8, false, default) { TwoValued = true };
        TypeShape[] parameters = [boolean, Int32, Int32];
        var graph = Expand([0x02, 0x2d, 0x02, 0x04, 0x2a, 0x03, 0x2a], Int32, parameters);
        // 真实 IL 的两条路径：各带分支条件的一个取值与返回值。
        var paths = Walk(graph);
        if (paths.Length != 2) return $"真实 IL 走查得到 {paths.Length} 条路径";
        Term? condition = null;
        var returned = new Term?[2];
        foreach (var path in paths)
        {
            if (path.End != PathEnd.Return || path.Conditions.Length != 1 || path.Conditions[0].Term is not { } test || (condition ??= test) != test)
                return "真实 IL 的路径应各在同一个分支条件下返回";
            returned[path.Conditions[0].Value != 0 ? 0 : 1] = path.Outcome[0];
        }
        var expected = graph.Terms.Select(condition!, returned[0]!, returned[1]!);
        var host = new MethodShape(default, false, [.. parameters], Int32, VariantCondition.StaticMethod);
        var arguments = graph.EntryParameters.OrderBy(e => e.Slot.Index).ToArray();
        // 条件成立时转到 L1 取 taken，否则顺序执行取 fallthrough，两支在 L2 汇合。
        ManagedInstruction[] Written(int taken, int fallthrough) =>
            [new("ldarg", 0), new("brtrue", Target: 1), new("ldarg", fallthrough), new("br", Target: 2), new(".label", 1), new("ldarg", taken), new(".label", 2)];
        var written = Lowering.Denote(Written(1, 2), host, arguments, new StaticFieldView(), graph.Terms, 64);
        if (written != expected) return $"下降的写法读出 {written?.ToString() ?? "空"}，真实 IL 是 {expected}";
        var swapped = Lowering.Denote(Written(2, 1), host, arguments, new StaticFieldView(), graph.Terms, 64);
        return swapped is not null && swapped != expected ? null : $"两支互换的写法读出 {swapped?.ToString() ?? "空"}，应与 {expected} 不同";
    }

    // ---- 辅助 ----

    private static FlowGraph<TemplateEffect> Expand(byte[] code, TypeShape? returns, TypeShape[]? parameters = null, TypeShape[]? locals = null,
        IMetadataView? metadata = null)
    {
        var method = new MethodShape(default, false, [.. parameters ?? []], returns, VariantCondition.StaticMethod);
        var body = new MethodBody(method, [.. locals ?? []], [.. code], 0, InitLocals: true);
        return IlExpander.Expand(body, metadata ?? new StaticFieldView(), new FixtureTokens(), new TermPool(), 1, 64).Graph;
    }

    /// <summary>
    /// 两段签名相同的 IL 的对照（没有 this）。bodies 按方法记号给出被调方法的方法体，asked 记下被问到的方法。
    /// </summary>
    private static ProofResult Compare(byte[] left, byte[] right, TypeShape? returns, TypeShape[] parameters, Dictionary<long, byte[]> bodies,
        List<long>? asked = null)
    {
        var pool = new TermPool();
        var view = new CallView();
        var tokens = new FixtureTokens();
        MethodBody Body(byte[] code, MethodShape method) => new(method, [], [.. code], 0, InitLocals: true);
        var root = new MethodShape(default, false, [.. parameters], returns, VariantCondition.StaticMethod);
        return CoExecution.Equivalent(IlExpander.Expand(Body(left, root), view, tokens, pool, 1, 64).Graph,
            IlExpander.Expand(Body(right, root), view, tokens, pool, 2, 64).Graph, Body(left, root), new LayoutFacts(), (method, graph) =>
            {
                asked?.Add(method.Key);
                return bodies.TryGetValue(method.Key, out var code) ? IlExpander.Expand(Body(code, view.Method(method)), view, tokens, pool, graph, 64).Graph : null;
            });
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

    private static string? InitLocals(SrmMetadata metadata)
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

            using var module = new Module(Path.Combine(directory, "InitLocalsFixture.dll"));
            string? result = null;
            foreach (var handle in module.Md.MethodDefinitions)
            {
                string name = module.Md.GetString(module.Md.GetMethodDefinition(handle).Name);
                var body = metadata.FixtureBody(module, handle);
                if (name == "Initialized")
                {
                    if (!body.InitLocals) return "设置了 InitLocals 的方法读出的标志为假";
                    var returned = Walk(IlExpander.Expand(body, metadata.Facts, metadata.Tokens(module), new TermPool(), 1, 64).Graph).Single().Outcome[0];
                    if (!returned.IsZero) result ??= $"设置了 InitLocals 的方法返回 {returned}";
                }
                else if (name == "Uninitialized")
                {
                    if (body.InitLocals) return "没有设置 InitLocals 的方法读出的标志为真";
                    result ??= Rejected(() => IlExpander.Expand(body, metadata.Facts, metadata.Tokens(module), new TermPool(), 1, 64), "局部变量没有初始化的保证");
                }
            }
            return result;
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    private static string? GenericMembers(SrmMetadata metadata)
    {
        if (metadata.GenericMemberPair() is not { } pair) return "没有同一个方法在不同类型实例上的两个引用";
        var tokens = metadata.Tokens(pair.Module);
        var first = tokens.Method(pair.First);
        var second = tokens.Method(pair.Second);
        return first != second ? null : $"两个实例上的方法都是 {first}";
    }

    private static string? CallForms(SrmMetadata metadata)
    {
        var core = metadata.Load("mscorlib") ?? throw new InvalidOperationException("程序集目录里没有核心库");
        var md = core.Md;
        var tokens = metadata.Tokens(core);
        var facts = new Cpp2CS.Facts.EntityFacts(metadata.Facts);
        // 没有形参的实例方法：构造函数，或别的方法。签名是 HASTHIS、0 个形参。
        EntityRef? Member(TypeDefinitionHandle type, bool constructor, bool requireVirtual = false)
        {
            foreach (var handle in md.GetTypeDefinition(type).GetMethods())
            {
                var method = md.GetMethodDefinition(handle);
                var signature = md.GetBlobBytes(method.Signature);
                if ((method.Attributes & MethodAttributes.Static) != 0 || signature.Length < 2 || signature[0] != 0x20 || signature[1] != 0) continue;
                if (requireVirtual && !method.Attributes.HasFlag(MethodAttributes.Virtual)) continue;
                if ((md.GetString(method.Name) == ".ctor") == constructor) return tokens.Method(MetadataTokens.GetToken(handle));
            }
            return null;
        }
        bool Plain(TypeDefinitionHandle type) => md.GetTypeDefinition(type).GetGenericParameters().Count == 0;
        string? Legal(string what, string? reason) => reason is null ? null : $"{what}被拒绝：{reason}";
        string? Illegal(string what, string? reason) => reason is null ? $"{what}被接受" : null;

        EntityRef? plain = null;
        var call = OperationCatalog.Get("call.instance");
        var callvirt = OperationCatalog.Get("callvirt.unique");
        string? chain = "核心库里没有三层的继承链";
        foreach (var handle in md.TypeDefinitions)
        {
            var type = md.GetTypeDefinition(handle);
            // 没有基类时 BaseType 是空句柄，它的种类也读作类型定义。
            if (!Plain(handle) || type.BaseType.IsNil || type.BaseType.Kind != HandleKind.TypeDefinition) continue;
            var parent = (TypeDefinitionHandle)type.BaseType;
            var above = md.GetTypeDefinition(parent).BaseType;
            if (!Plain(parent) || above.IsNil || above.Kind != HandleKind.TypeDefinition) continue;
            var grandparent = (TypeDefinitionHandle)above;
            if (Member(handle, true) is not { } host || Member(handle, false) is not { } other
                || Member(parent, true) is not { } direct || Member(grandparent, true) is not { } far) continue;
            if (facts.DeclaringTypeOf(host) is not { } owner || facts.IsValueType(owner) != false) continue;
            plain = other;
            chain = Legal("对 this 调用直接基类的构造函数", CallLegality.Check(call, direct, true, host, facts))
                ?? Legal("对 this 调用本类的另一个构造函数", CallLegality.Check(call, host, true, host, facts))
                ?? Illegal("对 this 调用祖父类的构造函数", CallLegality.Check(call, far, true, host, facts))
                ?? Illegal("对别的对象调用直接基类的构造函数", CallLegality.Check(call, direct, false, host, facts))
                ?? Illegal("在普通方法里用 call 调用构造函数", CallLegality.Check(call, direct, true, other, facts))
                ?? Illegal("用 callvirt 调用构造函数", CallLegality.Check(callvirt, direct, true, host, facts))
                ?? Legal("用 callvirt 调用引用类型的实例方法", CallLegality.Check(callvirt, other, true, other, facts));
            break;
        }
        if (chain is not null || plain is not { } caller) return chain;
        if (core.FindTopLevel("System", "Object") is not { } root || Member(root, false, requireVirtual: true) is not { } virtualMethod)
            return "核心库的 System.Object 没有无参虚方法";
        var virtualCall = Illegal("对别的对象用 call 调用虚方法", CallLegality.Check(call, virtualMethod, false, caller, facts))
            ?? Legal("对 this 用 call 调用基类的虚方法", CallLegality.Check(call, virtualMethod, true, caller, facts));
        if (virtualCall is not null) return virtualCall;

        foreach (var handle in md.TypeDefinitions)
        {
            if (!Plain(handle) || Member(handle, false) is not { } method) continue;
            if (facts.DeclaringTypeOf(method) is not { } owner || facts.IsValueType(owner) != true) continue;
            return Illegal("对值类型的方法用 callvirt", CallLegality.Check(callvirt, method, false, caller, facts))
                ?? Legal("对值类型的方法用 call", CallLegality.Check(call, method, false, caller, facts))
                ?? (Member(handle, true) is { } constructor
                    ? Legal("对着地址调用值类型的构造函数", CallLegality.Check(call, constructor, false, caller, facts)) : null);
        }
        return "核心库里没有带实例方法的值类型";
    }

    private static string? PaddingComparison(SrmMetadata metadata, bool padding)
    {
        var module = metadata.Load("mscorlib")!;
        var handle = module.FindTopLevel("System", "DateTimeOffset")!.Value;
        var shape = metadata.Facts.Type(metadata.Tokens(module).Type(MetadataTokens.GetToken(handle)));
        if (shape.Members.IsDefaultOrEmpty) return "没有成员布局";
        var pool = new TermPool();
        var conditions = PathConditions.Empty(pool);
        var zero = pool.Zero(shape.StorageBits);
        for (int bit = 0; bit < shape.StorageBits; bit++)
        {
            bool member = shape.Members.Any(m => bit >= m.OffsetBits && bit - m.OffsetBits < m.Bits);
            if (member == padding) continue;
            var changed = pool.Bits(UInt128.One << bit, shape.StorageBits);
            return conditions.SameMembers(zero, changed, shape.Members) == padding ? null : $"第 {bit} 位的比较与成员布局不符";
        }
        return "布局里没有待核对的位";
    }

    private static M.NamedType CoreCollection(SrmMetadata metadata, string name, string argument)
    {
        var core = metadata.Load("mscorlib") ?? throw new InvalidOperationException("程序集目录里没有核心库");
        var handle = core.FindTopLevel("System.Collections.Generic", name) ?? throw new InvalidOperationException($"核心库里没有 {name}");
        var entity = metadata.Tokens(core).Type(MetadataTokens.GetToken(handle));
        if (metadata.Facts.Keys.DescribeType(entity) is not M.NamedType definition) throw new InvalidOperationException($"缺少 {name} 的类型定义");
        return definition with { Arguments = [metadata.Facts.CoreType(argument)] };
    }

    private static string? CoreTypes(SrmMetadata metadata)
    {
        var core = metadata.Load("mscorlib") ?? throw new InvalidOperationException("程序集目录里没有核心库");
        string? Compare(string type, string field)
        {
            var handle = core.FindTopLevel("System", type) ?? throw new InvalidOperationException($"核心库里没有 System.{type}");
            var fieldHandle = core.Md.GetTypeDefinition(handle).GetFields().FirstOrDefault(f => core.Md.GetString(core.Md.GetFieldDefinition(f).Name) == field);
            if (fieldHandle.IsNil) throw new InvalidOperationException($"System.{type} 里没有字段 {field}");
            var bySignature = metadata.SignatureFieldType(core, fieldHandle);
            var byDefinition = metadata.Tokens(core).Type(MetadataTokens.GetToken(handle));
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

    private sealed class FixtureTokens : ITokenResolver
    {
        public EntityRef Method(int token) => new(EntityKind.Method, token);
        public EntityRef Field(int token) => new(EntityKind.Field, token);
        public EntityRef Type(int token) => new(EntityKind.Type, token);
        public EntityRef String(int token) => new(EntityKind.String, token);
    }

    /// <summary>字段一律是静态的、所属类有静态构造函数的元数据。</summary>
    private sealed class StaticFieldView : IMetadataView
    {
        public TypeShape Type(EntityRef entity) => Int32;
        public FieldShape Field(EntityRef entity) => new(entity, default, Int32, IsStatic: true, HasInitializer: true, PreciseInitialization: true, -1);
        public MethodShape Method(EntityRef entity) => new(entity, false, [], null, VariantCondition.StaticMethod);
    }

    /// <summary>
    /// 调用的夹具。字段是静态的 int32，所属的类有静态构造函数。方法 0x06000001、0x06000002 是 int32 → int32 的静态方法；
    /// 其余是类上的虚方法，无参无返回值。
    /// </summary>
    private sealed class CallView : IMetadataView
    {
        public TypeShape Type(EntityRef entity) => Int32;
        public FieldShape Field(EntityRef entity) => new(entity, default, Int32, IsStatic: true, HasInitializer: true, PreciseInitialization: true, -1);
        public MethodShape Method(EntityRef entity) => entity.Key is 0x06000001 or 0x06000002
            ? new(entity, false, [Int32], Int32, VariantCondition.StaticMethod)
            : new(entity, true, [Reference], null, VariantCondition.ClassVirtual);
    }

    /// <summary>IL 对照用到的现场事实：运行时布局，以及静态字段在静态区里的偏移（按字段记号的序号排开）。没有原生代码。</summary>
    private sealed class LayoutFacts : INativeFacts
    {
        public Cpp2CS.Spec.Runtime.RuntimeLayout Layout => Cpp2CS.Spec.Runtime.RuntimeLayout.Unity2022Lp64;
        public Callee Callee(ulong address) => throw new InvalidOperationException("夹具里没有原生代码");
        public ulong? Entry(EntityRef method) => null;
        public int? InstanceFieldOffset(EntityRef field) => null;
        public int? StaticFieldOffset(EntityRef field) => (int)(field.Key & 0xffff) * 8;
        public bool InImageData(ulong address) => false;
        public ulong? LinkConstant(ulong address) => null;
        public EntityRef? TypeAtSlot(ulong address) => null;
    }

    /// <summary>
    /// 嵌套的值类型：类型 1（外层）在偏移 0 处有字段 0x04000001，它的类型是类型 2（内层）；类型 2 在偏移 0 处有 int32 字段 0x04000002。
    /// </summary>
    private sealed class NestedFieldView : IMetadataView
    {
        private static readonly EntityRef Outer = new(EntityKind.Type, 1), Inner = new(EntityKind.Type, 2);
        public TypeShape Type(EntityRef entity) => Int32;
        public FieldShape Field(EntityRef entity) => entity.Key == 0x04000001
            ? new(entity, Outer, new TypeShape(StackKind.Value, 32, false, Inner), IsStatic: false, HasInitializer: false, PreciseInitialization: false, 0)
            : new(entity, Inner, Int32, IsStatic: false, HasInitializer: false, PreciseInitialization: false, 0);
        public MethodShape Method(EntityRef entity) => throw new ExpansionException("夹具里没有方法", "");
    }

    /// <summary>方法一律是接口上的、无参无返回值的实例方法。</summary>
    private sealed class InterfaceView : IMetadataView
    {
        public TypeShape Type(EntityRef entity) => Int32;
        public FieldShape Field(EntityRef entity) => throw new ExpansionException("夹具里没有字段", "");
        public MethodShape Method(EntityRef entity) => new(entity, true, [Reference], null, VariantCondition.InterfaceMethod);
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
