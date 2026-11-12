using System.Collections.Immutable;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class StructureChecks
{
    public const string Command = "structure";
    public static int Run()
    {
        var checks = new Assertions();
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        var runtime = catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is { ReturnType.Size: > 0 });
        for (int scenario = 0; scenario < 6; scenario++)
        {
            var selectedRuntime = scenario == 0 ? catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is { ReturnType.Size: 0 }) : runtime;
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(selectedRuntime), catalog);
            var terms = new TermTable();
            var entry = new BlockIdentity(); var arm = new BlockIdentity(); var join = new BlockIdentity();
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64); var image = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var slot = new AbstractSlot(SlotKind.Integer);
            var parameter = terms.Atom(new EntryAtom(slot), 64);
            var builder = new FunctionBuilder(terms, entry, 64, new(frame)) { ImageBase = image };
            builder.Inputs.Add(new(slot, parameter));
            var readId = new ReadIdentity(); var flag = terms.Atom(new ResultAtom(readId), 8);
            var callId = new CallIdentity(); var result = terms.Atom(new ResultAtom(callId, 1), 64);
            var returned = terms.Atom(new ResultAtom(callId), 64);
            var call = new Call(callId, new ImageFunction(20), [new(slot, image)], [new(slot, returned), new(new(SlotKind.Integer, 1), result)]);
            var observable = new Call(new(), new ComputedTarget(parameter), [], []);
            var mergeId = new MergeIdentity(); var merged = terms.Atom(new ResultAtom(mergeId), 64);
            if (scenario >= 4)
                builder.Blocks.Add(new(entry, [], [call], new Return([new(slot, scenario == 5 ? returned : parameter)])));
            else
            {
                builder.Blocks.Add(new(entry, [], [new MemoryRead(readId, image, 8, flag)],
                    new Branch(terms.Slice(scenario == 1 ? parameter : flag, 0, 1), arm, join)));
                builder.Blocks.Add(new(arm, [], scenario == 2 ? [observable] : [call, new MemoryWrite(new(), image, 8, terms.Constant(1, 8))], new Jump(join)));
                builder.Blocks.Add(new(join, [new(mergeId, merged, [new(entry, parameter), new(arm,
                    scenario == 3 ? terms.Constant(42, 64) : scenario == 2 ? parameter : result)])], [], new Return([new(slot, merged)])));
            }
            var function = builder.Freeze();
            checks.True(ExitChecker.Check(function).IsValid, $"场景 {scenario} 输入契约");
            var state = new StateQueries(image: new InputMemoryImage());
            var names = new ValueNamingQuery(state, calls, NamingFacts.Empty, spec, binder);
            var output = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }).Run(function);
            checks.True(ExitChecker.Check(output.Function).IsValid, $"场景 {scenario} 输出契约");
            checks.True(output.Records.Count(r => r.Kind == "branch" && r.Removed) == (scenario == 0 ? 1 : 0), $"场景 {scenario} 分支消去结果");
            if (scenario == 0) checks.True(output.Assumptions.Contains(UnobservableEffects.UndefinedAssumption), "未定义合流登记假设");
            if (scenario == 4) checks.True(!output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(), "无条件不可观察调用删除");
            if (scenario == 5) checks.True(ReferenceEquals(output.Function, function) && output.Records.Any(r => r.Kind == "runtime-result-used"), "实际返回值仍被使用时原样保留并记录");
        }
        ExceptionEntryCases(checks);
        SignatureBeforeForwarding(checks);
        SpecificationCases(checks);
        InterfaceLookupCases(checks);
        return checks.Finish("结构消去");
    }
    private static void SpecificationCases(Assertions checks)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        foreach (var operation in RuntimeOperations.All.Values)
        {
            if (operation.Result.Relation.Kind == RuntimeResultRelationKind.ResolvedPointee)
                checks.True(operation.Result.Width == RuntimeWidth.Pointer && operation.Result.Relation.Evidence is { Length: > 0 }
                    && operation.Inputs.Any(i => i.Name == operation.Result.Relation.Input && i.Use == RuntimeInputUse.Location),
                    "槽内容结果关系有位置输入、指针位宽与源码凭据");
            if (operation.RelaxedClassInput is { } input)
                checks.True(operation.Inputs.Any(i => i.Name == input && i.Kind == RuntimeValueKind.Class), "宽松类初始化属性引用类输入");
        }
        var owner = new Cpp2CS.Model.TypeDef { Index = 0, Assembly = "test", Namespace = "", Name = "Owner", Token = 0,
            Attributes = System.Reflection.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var reference = new Cpp2CS.Model.DefinitionRef(owner, []);
        var voidType = new Cpp2CS.Model.DefinitionRef(new Cpp2CS.Model.TypeDef { Index = 2, Assembly = "mscorlib.dll",
            Namespace = "System", Name = "Void", Token = 0, Attributes = System.Reflection.TypeAttributes.Public,
            IsValueType = true, IsEnum = false }, []);
        owner.Methods = [new() { Index = 0, Owner = owner, Name = ".cctor", Token = 0,
            Attributes = System.Reflection.MethodAttributes.Static | System.Reflection.MethodAttributes.SpecialName | System.Reflection.MethodAttributes.RTSpecialName, ImplAttributes = 0, Slot = -1, ReturnType = voidType, Parameters = [] }];
        var other = new Cpp2CS.Model.TypeDef { Index = 1, Assembly = "test", Namespace = "", Name = "Other", Token = 0,
            Attributes = System.Reflection.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        other.Methods = [new() { Index = 1, Owner = other, Name = ".cctor", Token = 0,
            Attributes = System.Reflection.MethodAttributes.Static | System.Reflection.MethodAttributes.SpecialName | System.Reflection.MethodAttributes.RTSpecialName, ImplAttributes = 0, Slot = -1,
            ReturnType = voidType, Parameters = [] }];
        var facts = NamingFacts.Empty with { Slots = new Dictionary<ulong, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>> {
            [100] = Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(reference)),
            [200] = Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(new Cpp2CS.Model.DefinitionRef(other, [])))
        }.ToImmutableDictionary() };
        for (int scenario = 0; scenario < 4; scenario++)
        {
            var runtime = catalog.Functions.First(f => f.Operation.Name == (scenario == 0 ? "InitializeMetadata" : scenario == 1 ? "IsInstance" : "InitializeClassPrecise")
                && f.Signature is not null && (scenario != 0 || f.Signature.ReturnType.Size > 0));
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(runtime), catalog);
            var table = new TermTable(); var entry = new BlockIdentity(); var arm = new BlockIdentity(); var join = new BlockIdentity();
            var image = table.Atom(new RootAtom(AddressRoot.Image), 64); var frame = table.Atom(new RootAtom(AddressRoot.Frame), 64);
            Term Address(Term root, long offset) => table.Apply(new CoreOperator(CoreOperation.Add), 64, root, table.Constant(offset, 64));
            var slot = new AbstractSlot(SlotKind.Integer);
            var readId = new ReadIdentity(); var entity = table.Atom(new ResultAtom(readId), 64);
            var otherId = new ReadIdentity(); var otherEntity = table.Atom(new ResultAtom(otherId), 64);
            var callId = new CallIdentity(); var returned = table.Atom(new ResultAtom(callId), 64);
            var builder = new FunctionBuilder(table, entry, 64, new(frame)) { ImageBase = image };
            var prefix = new List<Statement> { new MemoryRead(readId, Address(image, 100), 64, entity) };
            var call = new Call(callId, new ImageFunction(20), [new(slot, scenario == 0 ? Address(image, 100) : entity)],
                scenario < 2 ? [new(slot, returned)] : []);
            if (scenario == 1)
            {
                var instance = table.Atom(new EntryAtom(slot), 64);
                builder.Inputs.Add(new(slot, instance));
                call = call with { Arguments = [new(slot, instance), new(new(SlotKind.Integer, 1), entity)] };
                builder.Blocks.Add(new(entry, [], [.. prefix, call], new Return([new(slot, returned)])));
            }
            else
            {
                Term condition = table.Slice(entity, 0, 1);
                if (scenario >= 2)
                {
                    if (scenario == 3)
                    {
                        prefix.Add(new MemoryRead(otherId, Address(image, 200), 64, otherEntity));
                        call = call with { Arguments = [new(slot, otherEntity)] };
                    }
                    var flagId = new ReadIdentity(); var field = spec.Layout.Field("Il2CppClass", "cctor_finished_or_no_cctor");
                    var flag = table.Atom(new ResultAtom(flagId), checked((int)field.Size * 8));
                    prefix.Add(new MemoryRead(flagId, Address(entity, field.ByteOffset), flag.Width, flag));
                    condition = table.Apply(new CoreOperator(CoreOperation.Equal), 1, flag, table.Constant(0, flag.Width));
                }
                builder.Blocks.Add(new(entry, [], [.. prefix], new Branch(condition, arm, join)));
                builder.Blocks.Add(new(arm, [], [call], new Jump(join)));
                var mergeId = new MergeIdentity(); var merged = table.Atom(new ResultAtom(mergeId), 64);
                builder.Blocks.Add(new(join, scenario == 0 ? [new(mergeId, merged, [new(entry, entity), new(arm, returned)])] : [], [],
                    new Return([new(slot, scenario == 0 ? merged : table.Constant(7, 64))])));
            }
            var function = builder.Freeze(); var state = new StateQueries(image: new InputMemoryImage());
            var names = new ValueNamingQuery(state, calls, facts, spec, binder);
            var output = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }).Run(function);
            checks.True(ExitChecker.Check(output.Function).IsValid, $"规格场景 {scenario} 输出契约");
            var statements = output.Function.Blocks.SelectMany(b => b.Statements).ToArray();
            if (scenario == 0) checks.True(!output.Function.Blocks.Any(b => b.End is Branch) && statements.OfType<Call>().Count() == 0
                && statements.OfType<MemoryRead>().Count() == 1, "内联惰性初始化合并成一次槽读取");
            if (scenario == 1) checks.True(statements.OfType<Call>().Count() == 1 && !output.Records.Any(r => r.Kind == "specification-result"), "输入或空关系不能替换为槽读取");
            if (scenario == 2) checks.True(!output.Function.Blocks.Any(b => b.End is Branch) && statements.OfType<Call>().Single().Identity == callId,
                "同类受守卫精确初始化成为无条件事件且保留调用身份");
            if (scenario == 3) checks.True(output.Function.Blocks.Any(b => b.End is Branch) && statements.OfType<Call>().Count() == 1
                && output.Records.Any(r => r.Evidence == "守卫状态与幂等事件的对象不同"),
                "条件类与事件类不同不折叠");
        }
    }

    private static void InterfaceLookupCases(Assertions checks)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var runtime = catalog.Functions.Single(f => f.Operation.Name == "LookupInterfaceData");
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(runtime), catalog);
        var itf = new Cpp2CS.Model.TypeDef { Index = 0, Assembly = "test", Namespace = "", Name = "IAction", Token = 0,
            Attributes = System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Interface, IsValueType = false, IsEnum = false };
        var voidType = new Cpp2CS.Model.DefinitionRef(new Cpp2CS.Model.TypeDef { Index = 1, Assembly = "mscorlib.dll", Namespace = "System", Name = "Void", Token = 0,
            Attributes = System.Reflection.TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        var apply = new Cpp2CS.Model.MethodDef { Index = 0, Owner = itf, Name = "Apply", Token = 0, Attributes = System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Virtual,
            ImplAttributes = 0, Slot = 0, ReturnType = voidType, Parameters = [] };
        itf.Methods = [apply];
        var caller = new Cpp2CS.Model.MethodDef { Index = 1, Owner = itf, Name = "Caller", Token = 0, Attributes = System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1, ReturnType = voidType, Parameters = [new("value", new Cpp2CS.Model.DefinitionRef(itf, []), 0, null, false)] };
        var facts = NamingFacts.Empty with { Slots = new Dictionary<ulong, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>> {
            [128] = Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(new Cpp2CS.Model.DefinitionRef(itf, []))),
            [256] = Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(new Cpp2CS.Model.DefinitionRef(itf, [])))
        }.ToImmutableDictionary() };
        for (int scenario = 0; scenario < 9; scenario++)
        {
            var t = new TermTable(); var head = new BlockIdentity(); var scan = new BlockIdentity(); var advance = new BlockIdentity();
            var fast = new BlockIdentity(); var slow = new BlockIdentity(); var join = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var slot = new AbstractSlot(SlotKind.Integer); var receiver = t.Atom(new EntryAtom(slot), 64);
            var f = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image }; f.Inputs.Add(new(slot, receiver));
            var nativeFloat = t.Atom(new EntryAtom(new(SlotKind.Floating)), 128);
            if (scenario == 8) f.Inputs.Add(new(new(SlotKind.Floating), nativeFloat));
            Term Add(Term value, long n) => t.Apply(new CoreOperator(CoreOperation.Add), 64, value, t.Constant(unchecked((ulong)n), 64));
            Term Read(List<Statement> statements, Term address, int width = 64)
            {
                var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), width);
                statements.Add(new MemoryRead(id, address, width, value)); return value;
            }
            var start = new List<Statement>(); var iface = Read(start, Add(image, 128));
            var fastStatements = new List<Statement>(); var slowStatements = new List<Statement>();
            var klass = Read(start, Add(receiver, spec.Layout.Field("Il2CppObject", "klass").ByteOffset));
            var table = Read(start, Add(klass, spec.Layout.Field("Il2CppClass", "interfaceOffsets").ByteOffset));
            var cursorId = new MergeIdentity(); var cursor = t.Atom(new ResultAtom(cursorId), 64);
            var scanStatements = new List<Statement>();
            // 私有类字段有读取凭据，但不是可随调用移动的元数据实体读取。
            var comparedInterface = scenario == 2 ? Read(scanStatements, Add(iface, spec.Layout.Field("Il2CppClass", "element_class").ByteOffset)) : iface;
            var pairInterface = Read(scanStatements, Add(cursor, spec.Layout.Field("Il2CppRuntimeInterfaceOffsetPair", "interfaceType").ByteOffset));
            var offset = Read(fastStatements, Add(cursor, spec.Layout.Field("Il2CppRuntimeInterfaceOffsetPair", "offset").ByteOffset), 32);
            var scaled = t.Apply(new CoreOperator(CoreOperation.Multiply), 64,
                t.Apply(new CoreOperator(CoreOperation.SignExtend), 64, offset), t.Constant(spec.Layout.VtableSlotSize, 64));
            var address = t.Apply(new CoreOperator(CoreOperation.Add), 64, Add(klass, spec.Layout.VtableStart), scaled);
            var callId = new CallIdentity(); var result = t.Atom(new ResultAtom(callId), 64);
            var floatResult = t.Atom(new ResultAtom(callId, 1), 128);
            var callInterface = scenario == 2 ? Read(slowStatements, Add(iface, spec.Layout.Field("Il2CppClass", "element_class").ByteOffset)) :
                scenario == 3 ? Read(slowStatements, Add(image, 256)) : iface;
            slowStatements.Add(new Call(callId, new ImageFunction(100), [new(slot, receiver), new(new(SlotKind.Integer, 1), callInterface),
                new(new(SlotKind.Integer, 2), t.Constant(0, 64))], scenario == 8 ? [new(slot, result), new(new(SlotKind.Floating), floatResult)] : [new(slot, result)], OutgoingArgumentArea: Add(frame, -64)));
            if (scenario == 1) fastStatements.Add(new Call(new(), new ComputedTarget(receiver), [], []));
            if (scenario == 6) fastStatements.Add(new MemoryWrite(new(), Add(frame, -32), 64, t.Constant(7, 64)));
            var mergeId = new MergeIdentity(); var merged = t.Atom(new ResultAtom(mergeId), 64);
            var condition = t.Apply(new CoreOperator(CoreOperation.Equal), 1, pairInterface, comparedInterface);
            f.Blocks.Add(new(head, [], start.ToImmutableArray(), new Branch(t.Slice(receiver, 0, 1), scan, slow)));
            f.Blocks.Add(new(scan, [new(cursorId, cursor, [new(head, table), new(advance, Add(cursor, spec.Layout.Record("Il2CppRuntimeInterfaceOffsetPair").Size))])],
                scanStatements.ToImmutableArray(), new Branch(condition, fast, advance)));
            f.Blocks.Add(new(advance, [], [], new Branch(t.Slice(receiver, 1, 1), scan, slow)));
            f.Blocks.Add(new(fast, [], fastStatements.ToImmutableArray(), new Jump(join)));
            f.Blocks.Add(new(slow, [], slowStatements.ToImmutableArray(), new Jump(join)));
            var extraId = new MergeIdentity(); var extra = t.Atom(new ResultAtom(extraId), scenario == 8 ? 128 : 64);
            var merges = new List<Merge> { new(mergeId, merged, [new(fast, address), new(slow, result)]) };
            if (scenario is 4 or 5 or 7) merges.Add(new(extraId, extra, [new(fast, scenario == 4 ? cursor : t.Constant(1, 64)), new(slow, t.Constant(2, 64))]));
            if (scenario == 8) merges.Add(new(extraId, extra, [new(fast, nativeFloat), new(slow, floatResult)]));
            var joinStatements = new List<Statement>();
            if (scenario == 8)
            {
                var target = Read(joinStatements, Add(merged, spec.Layout.Field("VirtualInvokeData", "methodPtr").ByteOffset));
                var info = Read(joinStatements, Add(merged, spec.Layout.Field("VirtualInvokeData", "method").ByteOffset));
                joinStatements.Add(new Call(new(), new ComputedTarget(target), [new(slot, receiver), new(new(SlotKind.Integer, 1), info), new(new(SlotKind.Floating), extra)], []));
            }
            var outside = scenario == 6 ? Read(joinStatements, Add(frame, -32)) : merged;
            f.Blocks.Add(new(join, merges.ToImmutableArray(), joinStatements.ToImmutableArray(), new Return(scenario == 8 ? [] : [new(slot, scenario == 6 ? t.Apply(new CoreOperator(CoreOperation.Add), 64, merged, outside) :
                scenario == 4 ? t.Apply(new CoreOperator(CoreOperation.Add), 64, merged, extra) :
                scenario == 5 ? t.Apply(new CoreOperator(CoreOperation.Add), 64, merged, extra) : merged)])));
            var function = f.Freeze(); var state = new StateQueries(image: new InputMemoryImage());
            var naming = new ValueNamingQuery(state, calls, facts, spec, binder,
                scenario == 8 ? binder.Entry(Cpp2CS.Model.MethodRef.Open(caller), BindingEntryKind.Ordinary).Value : null);
            checks.True(ExitChecker.Check(function).IsValid, $"接口区域 {scenario} 输入契约");
            var data = naming.CreateContext(function).Get(new InterfaceDataQuery(state, calls, naming, spec), new(merged, new(join, 0)));
            checks.True(data.IsSuccess, $"接口区域 {scenario} 数据命名：" + data.Why);
            var managedLocations = scenario == 8 ? new Cpp2CS.Recovery.Locations.ManagedLocationQuery(state, naming, layouts, spec) : null;
            var output = new UnobservableEffects(state, calls, naming, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }, managedLocations).Run(function);
            checks.True(ExitChecker.Check(output.Function).IsValid, $"接口区域 {scenario} 输出契约");
            bool folded = scenario is 0 or 3 or 7 or 8;
            checks.True(output.Records.Any(r => r.Kind == "interface-lookup" && r.Removed) == folded, $"接口区域 {scenario} 折叠结果：" +
                string.Join("；", output.Records.Where(r => r.Kind == "interface-lookup").Select(r => r.Evidence)));
            if (folded)
            {
                checks.True(output.Function.Blocks.Length == 2 && output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Count() == (scenario == 8 ? 2 : 1)
                    && output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Count(c => c.Identity == callId) == 1,
                    "接口区域只保留一次查找且保留调用身份");
                checks.True(output.Assumptions.Contains(UnobservableEffects.InterfaceLookupAssumption), "接口区域登记终止假设");
                checks.True(output.Function.Blocks.Single(b => b.Identity == join).End is Return returned && (scenario == 8 ? returned.Results.IsEmpty : returned.Results[0].Value == result),
                    "接口区域合流由查找调用结果替换");
                if (scenario == 3) checks.True(output.Function.Blocks.Single(b => b.Identity == head).Statements.OfType<MemoryRead>().Any(r => r.Result == callInterface),
                    "区域内实体读取与查找一起移动到入口");
            }
            if (scenario == 1) checks.True(output.Records.Any(r => r.Kind == "interface-lookup" && r.Evidence.StartsWith("调用：")), "额外调用拒绝原因");
            if (scenario == 2) checks.True(output.Records.Any(r => r.Kind == "interface-lookup" && r.Evidence.StartsWith("输入：")), "非实体输入依赖拒绝原因");
            if (scenario == 8) checks.True(output.Records.Any(r => r.Kind == "unused-call-input" && r.Removed), "分派签名裁剪未使用的浮点实参后折叠区域");
            if (scenario == 6) checks.True(output.Records.Any(r => r.Kind == "interface-lookup" && r.Evidence.StartsWith("活跃性：")), "区域帧写入外泄拒绝原因");
        }
    }
}
