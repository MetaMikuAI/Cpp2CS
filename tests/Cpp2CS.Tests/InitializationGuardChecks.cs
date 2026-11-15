using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static class InitializationGuardChecks
{
    public const string Command = "init-guards";
    public static int Run()
    {
        var checks = new Assertions();
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        var klass = new TypeDef { Index = 0, Assembly = "test", Namespace = "", Name = "Owner", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var voidType = new DefinitionRef(new TypeDef { Index = 1, Assembly = "mscorlib.dll", Namespace = "System", Name = "Void", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        klass.Methods = [new() { Index = 0, Owner = klass, Name = ".cctor", Token = 0,
            Attributes = MethodAttributes.Static | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, ImplAttributes = 0,
            Slot = -1, ReturnType = voidType, Parameters = [] }];
        var metadata = catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is { ReturnType.Size: 0 });
        var classInit = catalog.Functions.First(f => f.Operation.Name == "InitializeClassPrecise" && f.Signature is not null);
        foreach (bool method in new[] { false, true })
        for (int scenario = 0; scenario < (method ? 10 : 8); scenario++)
        {
            var runtime = method ? metadata : classInit;
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(runtime), catalog);
            var t = new TermTable(); var head = new BlockIdentity(); var arm = new BlockIdentity(); var skip = new BlockIdentity();
            var join = new BlockIdentity(); var handler = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            Term Add(Term value, int offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, value, t.Constant(offset, 64));
            var slot = new AbstractSlot(SlotKind.Integer);
            var builder = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image };
            var ownerId = new ReadIdentity(); var owner = t.Atom(new ResultAtom(ownerId), 64);
            var flagId = new ReadIdentity();
            var field = spec.Layout.Field("Il2CppClass", "cctor_finished_or_no_cctor");
            int width = method ? 8 : checked((int)field.Size * 8);
            var flag = t.Atom(new ResultAtom(flagId), width);
            var flagAddress = method ? Add(image, 200) : Add(owner, checked((int)field.ByteOffset));
            var call = new Call(new(), new ImageFunction(20), [new(slot, method ? Add(image, 100) : owner)], [], Unwind: scenario == 4 ? handler : null);
            var prefix = new List<Statement>();
            if (!method) prefix.Add(new MemoryRead(ownerId, Add(image, 100), 64, owner));
            prefix.Add(new MemoryRead(flagId, flagAddress, width, flag) { Trace = new(1) });
            var extra = new Call(new(), new ImageFunction(20), [new(slot, method ? Add(image, 100) : owner), new(new(SlotKind.IndirectResult), t.Concat(flag, t.Constant(0, 64 - width)))], []);
            if (scenario == 3) prefix.Add(new Call(new(), new ComputedTarget(t.Constant(1, 64)), [new(slot, t.Concat(flag, t.Constant(0, 64 - width)))], []));
            if (scenario == 5) prefix.Add(extra);
            builder.Blocks.Add(new(head, [], prefix.ToImmutableArray(), new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, flag, t.Constant(0, width)), arm, scenario is 6 or 9 ? join : skip)));
            var inputValue = t.Atom(new EntryAtom(slot), 64);
            var clobbered = t.Atom(new ResultAtom(call.Identity), 64);
            if (scenario == 9)
            {
                builder.Inputs.Add(new(slot, inputValue));
                call = call with { Results = [new(slot, clobbered)] };
            }
            var body = new List<Statement>();
            if (scenario == 2) body.Add(new MemoryWrite(new(), frame, 32, t.Constant(3, 32)));
            if (scenario != 1) body.Add(call);
            if (method) body.Add(new MemoryWrite(new(), flagAddress, 8, t.Constant(1, 8)));
            builder.Blocks.Add(new(arm, [], body.ToImmutableArray(), scenario is 6 or 9 ? new Jump(join) : new Return([new(slot, t.Constant(7, 64))])));
            if (scenario is not (6 or 9)) builder.Blocks.Add(new(skip, [], [], scenario == 7 ? new Jump(arm) : new Return([new(slot, t.Constant(8, 64))])));
            else if (scenario == 9)
            {
                var mergeId = new MergeIdentity(); var merged = t.Atom(new ResultAtom(mergeId), 64);
                builder.Blocks.Add(new(join, [new(mergeId, merged, [new(head, inputValue), new(arm, clobbered)])], [], new Return([new(slot, merged)])));
            }
            else builder.Blocks.Add(new(join, [], [], new Return([new(slot, t.Constant(7, 64))])));
            if (scenario == 4)
            {
                var exception = t.Atom(new ExceptionAtom(handler), 64); var selector = t.Atom(new SelectorAtom(handler), 64);
                builder.Blocks.Add(new(handler, [], [], new ResumeUnwind(exception), new(exception, selector, [new(Cpp2CS.Native.Images.ClauseKind.Cleanup, [])])));
            }
            var function = builder.Freeze();
            checks.True(ExitChecker.Check(function).IsValid, $"初始化守卫 {method}/{scenario} 输入契约");
            var facts = NamingFacts.Empty with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(100, Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(klass, [])))) };
            if (method) facts = facts with { Flags = ImmutableDictionary<ulong, FlagEvidence>.Empty.Add(200, new(scenario != 8, scenario == 8 ? [new("test.evidence", "本函数的额外访问没有归类。")] : [], 1, 1)) };
            var state = new StateQueries(image: new InputMemoryImage());
            var names = new ValueNamingQuery(state, calls, facts, spec, binder);
            var output = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }).Run(function);
            checks.True(ExitChecker.Check(output.Function).IsValid, $"初始化守卫 {method}/{scenario} 输出契约");
            bool folded = output.Records.Any(r => r.Kind == "init-guard" && r.Removed);
            checks.True(folded == (scenario is 0 or 4 or 5 or 6 or 9), $"初始化守卫 {method}/{scenario} 模板改写结果");
            if (scenario == 9) checks.True(output.Assumptions.Contains(UnobservableEffects.UndefinedAssumption)
                && output.Function.Blocks.Where(b => b.End is Return).SelectMany(b => ((Return)b.End).Results).All(v => v.Value == inputValue),
                "删边前沿用已有的未定义位精化，入口实参不被未绑定结果槽覆盖");
            if (scenario == 8) checks.True(output.Records.Any(r => r.Reason is { Code: "structure.init-guard.flag-evidence", Cause.Code: "test.evidence" }), "没有凭据时保留守卫并接入凭据原因");
            if (scenario == 7) checks.True(output.Records.Any(r => r.Reason?.Code == "structure.init-guard.shared-prefix") && output.Function.Blocks.Any(b => b.End is Branch), "共享前缀保留守卫和原因");
            if (scenario is 2 or 3) checks.True(output.Records.Any(r => r.Reason?.Code == "structure.init-guard." + (scenario == 2 ? "effect-before-event" : "read-used")), "拒绝原因有独立原因码");
            if (!method && scenario == 4)
                checks.True(output.Function.Blocks.Single(b => b.Identity == head).Statements.OfType<Call>().Any(c => c.Identity == call.Identity && c.Unwind == handler), "类初始化移动后保留调用身份与展开边");
            if (!method && folded)
                checks.True(output.Function.Blocks.Single(b => b.Identity == head).Statements.OfType<Call>().Any(c => c.Identity == call.Identity), "精确类初始化在分支位置无条件执行");
        }
        {
            // 一次标志读取在分叉之前，两条路径上的守卫各测一次：两个守卫各自归位，别的守卫的零测试不算这次读取的真实使用。
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(classInit), catalog);
            var t = new TermTable(); var head = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity();
            var armL = new BlockIdentity(); var skipL = new BlockIdentity(); var armR = new BlockIdentity(); var skipR = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            Term Add(Term value, int offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, value, t.Constant(offset, 64));
            var slot = new AbstractSlot(SlotKind.Integer); var forkSlot = new AbstractSlot(SlotKind.Integer, 1);
            var builder = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image };
            var fork = t.Atom(new EntryAtom(forkSlot), 64); builder.Inputs.Add(new(forkSlot, fork));
            var ownerId = new ReadIdentity(); var owner = t.Atom(new ResultAtom(ownerId), 64);
            var field = spec.Layout.Field("Il2CppClass", "cctor_finished_or_no_cctor"); int width = checked((int)field.Size * 8);
            var flagId = new ReadIdentity(); var flag = t.Atom(new ResultAtom(flagId), width);
            var zero = t.Apply(new CoreOperator(CoreOperation.Equal), 1, flag, t.Constant(0, width));
            var callL = new Call(new(), new ImageFunction(20), [new(slot, owner)], []); var callR = new Call(new(), new ImageFunction(20), [new(slot, owner)], []);
            builder.Blocks.Add(new(head, [], [new MemoryRead(ownerId, Add(image, 100), 64, owner),
                new MemoryRead(flagId, Add(owner, checked((int)field.ByteOffset)), width, flag) { Trace = new(1) }],
                new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, fork, t.Constant(0, 64)), left, right)));
            builder.Blocks.Add(new(left, [], [], new Branch(zero, armL, skipL)));
            builder.Blocks.Add(new(armL, [], [callL], new Return([new(slot, t.Constant(7, 64))])));
            builder.Blocks.Add(new(skipL, [], [], new Return([new(slot, t.Constant(8, 64))])));
            builder.Blocks.Add(new(right, [], [], new Branch(zero, armR, skipR)));
            builder.Blocks.Add(new(armR, [], [callR], new Return([new(slot, t.Constant(9, 64))])));
            builder.Blocks.Add(new(skipR, [], [], new Return([new(slot, t.Constant(10, 64))])));
            var function = builder.Freeze();
            checks.True(ExitChecker.Check(function).IsValid, "共用读取的两个守卫 输入契约");
            var facts = NamingFacts.Empty with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(100, Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(klass, [])))) };
            var state = new StateQueries(image: new InputMemoryImage());
            var names = new ValueNamingQuery(state, calls, facts, spec, binder);
            var output = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }).Run(function);
            checks.True(ExitChecker.Check(output.Function).IsValid, "共用读取的两个守卫 输出契约");
            checks.True(output.Records.Count(r => r.Kind == "init-guard" && r.Removed) == 2, "一次读取被两条路径上的守卫共用时两个守卫各自归位："
                + string.Join("；", output.Records.Where(r => r.Reason is not null).Select(r => r.Reason!.Code + " " + r.Reason.Message)));
            checks.True(output.Function.Blocks.Count(b => b.End is Branch) == 1, "归位后只剩分叉的分支");
            checks.True(output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Select(c => c.Identity).ToHashSet().SetEquals([callL.Identity, callR.Identity]),
                "两条路径上各保留自己的初始化调用");
        }
        var ready = catalog.Functions.First(f => f.Operation.Name == "EnsureClassReady" && f.Signature is not null);
        {
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(ready), catalog);
            var t = new TermTable(); var head = new BlockIdentity(); var arm = new BlockIdentity(); var skip = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            var ownerId = new ReadIdentity(); var owner = t.Atom(new ResultAtom(ownerId), 64);
            var flagId = new ReadIdentity(); var flag = t.Atom(new ResultAtom(flagId), 8);
            var field = spec.Layout.Field("Il2CppClass", "initialized_and_no_error");
            var callId = new CallIdentity(); var result = t.Atom(new ResultAtom(callId), 64); var slot = new AbstractSlot(SlotKind.Integer);
            var f = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image };
            f.Blocks.Add(new(head, [], [new MemoryRead(ownerId, Add(image, 100), 64, owner), new MemoryRead(flagId, Add(owner, field.OffsetBits / 8), 8, flag)],
                new Branch(t.Slice(flag, checked((int)(field.OffsetBits % 8)), 1), skip, arm)));
            f.Blocks.Add(new(arm, [], [new Call(callId, new ImageFunction(20), [new(slot, owner)], [new(slot, result)])], new Return([new(slot, result)])));
            f.Blocks.Add(new(skip, [], [], new Return([new(slot, owner)])));
            var facts = NamingFacts.Empty with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(100, Outcome<MetadataEntity>.Success(new ClassEntity(new DefinitionRef(klass, [])))) };
            var state = new StateQueries(image: new InputMemoryImage()); var names = new ValueNamingQuery(state, calls, facts, spec, binder);
            var output = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }).Run(f.Freeze());
            checks.True(!output.Records.Any(r => r.Kind == "init-guard" && r.Removed) && ExitChecker.Check(output.Function).IsValid,
                "带返回值的类布局就绪保持既有处理，不纳入静态构造守卫");
        }
        GenericContextCases(checks, spec, catalog, binder, klass, voidType);
        MethodBodyCases(checks, spec, catalog, binder, klass, voidType);
        return checks.Finish("初始化守卫");
    }

    private sealed class MetadataRuntimeMap(RuntimeFunction metadata) : IRuntimeFunctionMap
    {
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 20 } ? metadata : null;
    }

    private sealed class SlotDecoder(TypeRef type) : IMetadataSlotDecoder
    {
        public Outcome<MetadataEntity> Decode(ulong address) => Outcome<MetadataEntity>.Success(new ClassEntity(type));
    }

    private static void MethodBodyCases(Assertions checks, RuntimeSpec spec, RuntimeFunctionCatalog catalog,
        MethodBinder binder, TypeDef owner, TypeRef voidType)
    {
        var type = new DefinitionRef(owner, []);
        var step = new MethodRef(new MethodDef { Index = 1, Owner = owner, Name = "Step", Token = 0x06000002,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = voidType,
            Parameters = [new("value", type, 0, null, false)] }, [], []);
        var metadata = catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is { ReturnType.Size: 0 });
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(step, BindingEntryKind.Ordinary)]), new MetadataRuntimeMap(metadata), catalog);
        string[] primitives = ["Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle"];
        var definitions = primitives.Select((name, index) => new TypeDef { Index = index + 2, Assembly = "mscorlib.dll", Namespace = "System", Name = name,
            Token = (uint)(0x02000003 + index), Attributes = TypeAttributes.Public, IsValueType = name is not ("Object" or "String"), IsEnum = false }).ToArray();
        var caller = new MethodRef(new MethodDef { Index = 2, Owner = owner, Name = "Caller", Token = 0x06000003,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = voidType,
            Parameters = [new("control", new DefinitionRef(definitions.Single(t => t.Name == "Int32"), []), 0, null, false)] }, [], []);
        TypeDef[] types = [owner, ((DefinitionRef)voidType).Definition, .. definitions];
        var model = new ProgramModel { MetadataVersion = 0, Types = types, Methods = [.. owner.Methods, step.Method, caller.Method],
            Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = types.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var codeEntry = new CodeEntry(64, EntryKind.Method, caller, 2, null);
        CodeEntry[] entries = [new(10, EntryKind.Method, step, 1, null), codeEntry];
        var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = entries,
            ByAddress = entries.ToDictionary(e => e.Address, e => ImmutableArray.Create(e)), Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(),
            MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
        var entryBinding = binder.Entry(caller, BindingEntryKind.Ordinary).Value;
        string[] cases = ["调用和分支之后", "分支的一臂", "循环体", "两个不同标志", "同一标志重复", "其他写入", "其他调用", "标志额外读取", "槽位提前读取", "异常区域", "第二个模板失败", "两臂各自初始化同一槽位", "槽位读取绕过守卫", "异常路径未完成初始化", "未使用的提前读取", "槽位实体合流物化"];
        for (int scenario = 0; scenario < cases.Length; scenario++)
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var before = new BlockIdentity(); var head = new BlockIdentity();
            var arm = new BlockIdentity(); var join = new BlockIdentity(); var exit = new BlockIdentity(); var handler = new BlockIdentity(); var alternative = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            Term Address(int offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(offset, 64));
            var slot = new AbstractSlot(SlotKind.Integer);
            var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
            var parameter = t.Atom(new EntryAtom(slot), 64); f.Inputs.Add(new(slot, parameter));
            var control = t.Apply(new CoreOperator(CoreOperation.NotEqual), 1, t.Slice(parameter, 0, 32), t.Constant(0, 32));
            Call Step(Term? value = null) => new(new(), new ImageFunction(10), [new(slot, value ?? t.Constant(0, 64)), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], []);
            Term Read(List<Statement> statements, int offset, int width, ulong trace)
            {
                var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), width);
                statements.Add(new MemoryRead(id, Address(offset), width, value) { Trace = new(trace) }); return value;
            }
            var first = new List<Statement> { Step() };
            if (scenario == 8) first.Add(Step(Read(first, 100, 64, 9)));
            if (scenario == 14) Read(first, 100, 64, 9);
            f.Blocks.Add(new(entry, [], [.. first], scenario == 2 ? new Jump(head) : new Branch(control, before, scenario is 1 or 12 ? exit : scenario == 11 ? alternative : head)));
            if (scenario != 2) f.Blocks.Add(new(before, [], [Step()], new Jump(head)));
            void Guard(BlockIdentity test, BlockIdentity initialize, BlockIdentity continuation, int flag, int metadataSlot, ulong trace, bool bad = false)
            {
                var reads = new List<Statement>(); var value = Read(reads, flag, 8, trace);
                // 补零后的全宽测试与原字节的零测试相同；无关读取不改变模板凭据。
                Read(reads, 400, 32, trace + 1);
                if (scenario == 7) Read(reads, flag, 8, trace + 2);
                var zero = t.Apply(new CoreOperator(CoreOperation.Equal), 1, t.Concat(value, t.Constant(0, 24)), t.Constant(0, 32));
                f.Blocks.Add(new(test, [], [.. reads], new Branch(zero, initialize, continuation)));
                var body = new List<Statement>();
                if (scenario == 5) body.Add(new MemoryWrite(new(), frame, 32, t.Constant(3, 32)));
                if (scenario == 6 || bad) body.Add(Step());
                body.Add(new Call(new(), new ImageFunction(20), [new(slot, Address(metadataSlot))], [], Unwind: scenario is 9 or 13 ? handler : null));
                if (scenario == 15) body.Add(new Call(new(), new ImageFunction(20), [new(slot, Address(108))], []));
                body.Add(new MemoryWrite(new(), Address(flag), 8, t.Constant(1, 8)));
                f.Blocks.Add(new(initialize, [], [.. body], new Jump(continuation)));
            }
            Guard(head, arm, join, 200, 100, 10);
            if (scenario is 3 or 4 or 10)
            {
                var secondArm = new BlockIdentity(); var secondJoin = new BlockIdentity();
                Guard(join, secondArm, secondJoin, scenario == 3 ? 201 : 200, scenario == 3 ? 108 : 100, 20, scenario == 10);
                f.Blocks.Add(new(secondJoin, [], [], new Jump(exit)));
            }
            else
            {
                var after = new List<Statement>(); after.Add(Step(Read(after, 100, 64, 30)));
                if (scenario == 15)
                {
                    var read = (MemoryRead)after[0];
                    after[0] = read with { Address = t.Apply(new CoreOperator(CoreOperation.Select), 64, control, Address(100), Address(108)) };
                }
                f.Blocks.Add(new(join, [], [.. after], scenario == 2 ? new Branch(control, head, exit) : new Jump(exit)));
            }
            if (scenario == 11)
            {
                var alternativeArm = new BlockIdentity(); var alternativeJoin = new BlockIdentity();
                Guard(alternative, alternativeArm, alternativeJoin, 201, 100, 40);
                var after = new List<Statement>(); after.Add(Step(Read(after, 100, 64, 50)));
                f.Blocks.Add(new(alternativeJoin, [], [.. after], new Jump(exit)));
            }
            var end = new List<Statement>();
            if (scenario == 12) end.Add(Step(Read(end, 100, 64, 60)));
            f.Blocks.Add(new(exit, [], [.. end], new Return([])));
            if (scenario is 9 or 13)
            {
                var exception = t.Atom(new ExceptionAtom(handler), 64); var selector = t.Atom(new SelectorAtom(handler), 64);
                var body = new List<Statement>();
                if (scenario == 13) body.Add(Step(Read(body, 100, 64, 70)));
                f.Blocks.Add(new(handler, [], [.. body], new ResumeUnwind(exception), new(exception, selector, [new(Cpp2CS.Native.Images.ClauseKind.Cleanup, [])])));
            }
            var function = f.Freeze();
            checks.True(ExitChecker.Check(function).IsValid, cases[scenario] + "输入契约");
            var memory = new InputMemoryImage();
            var survey = new NamingSurvey(calls, new SlotDecoder(type), memory, binder, spec, entryBinding); survey.Observe(function);
            var facts = survey.Finish();
            checks.True(facts.Flags[200].IsFlag == (scenario is not (5 or 6 or 7 or 10)), cases[scenario] + "标志凭据");
            var state = new StateQueries(image: memory); var names = new ValueNamingQuery(state, calls, facts, spec, binder, entryBinding);
            var output = new UnobservableEffects(state, calls, names, memory, new HashSet<AbstractSlot>()).Run(function);
            checks.True(ExitChecker.Check(output.Function).IsValid, cases[scenario] + "输出契约");
            int expected = scenario is 3 or 4 or 11 ? 2 : scenario is 5 or 6 or 7 or 8 or 10 or 12 or 13 or 14 ? 0 : 1;
            checks.True(output.Records.Count(r => r.Kind == "init-guard" && r.Removed) == expected, cases[scenario] + "各次模板独立证明");
            if (expected > 0)
            {
                checks.True(!output.Function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Any(r => r.Width == 8)
                    && output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().All(call => call.Target is ImageFunction { EntryOffset: 10 }),
                    cases[scenario] + "只消去初始化效果");
                checks.True(output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Count() == (scenario is 2 or 3 or 4 ? 2 : scenario == 11 ? 4 : 3),
                    cases[scenario] + "保留业务调用");
            }
            else
            {
                var diagnostic = output.Records.FirstOrDefault(r => !r.Removed && r.Address == 10 && r.Reason is not null);
                checks.True(output.Function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Any(r => r.Width == 8)
                    && diagnostic is not null, cases[scenario] + "保留守卫并在读取位置携带原因链");
                var codes = new List<string>();
                for (var why = diagnostic?.Reason; why is not null; why = why.Cause) codes.Add(why.Code);
                checks.True(codes.Contains(scenario is 8 or 12 or 13 or 14 ? "structure.init-guard.slot-before-init" : scenario == 7 ? "naming.flag-read" : "structure.init-guard.effect-before-event"),
                    cases[scenario] + "具体拒绝原因：" + string.Join("、", codes));
                var global = new GlobalFacts(memory, model, map, spec, "arm64") { Symbols = [new(metadata.MangledName, 20, 4)] };
                var recovered = new IntegerRecoveryStage(enableAccessorInlining: false, enableConstructorInlining: false).Run(function, new(caller.Method, codeEntry, global));
                var reasons = new List<string>();
                for (var why = (recovered as Missing<Cpp2CS.Managed.ManagedBody>)?.Hole.Reason; why is not null; why = why.Cause) reasons.Add(why.Code);
                checks.True(recovered is Missing<Cpp2CS.Managed.ManagedBody> && reasons.Contains(scenario is 8 or 12 or 13 or 14
                    ? "structure.init-guard.slot-before-init" : scenario == 7 ? "naming.flag-read" : "structure.init-guard.effect-before-event"),
                    cases[scenario] + "下降保持洞且传播具体原因：" + string.Join("、", reasons));
            }
        }
    }

    private sealed class GuardContextDecoder(MethodRef method, TypeRef type) : IRgctxDecoder
    {
        public Outcome<MetadataEntity> Decode(MethodRef owner, bool methodContext, int index) => owner == method && methodContext && index == 0
            ? Outcome<MetadataEntity>.Success(new ClassEntity(type)) : Outcome<MetadataEntity>.Failure(new("test.rgctx", "上下文项没有凭据。"));
        public Outcome<MetadataEntity> Decode(DefinitionRef owner, int index) => Outcome<MetadataEntity>.Failure(new("test.rgctx", "没有类型上下文。"));
    }

    private static void GenericContextCases(Assertions checks, RuntimeSpec spec, RuntimeFunctionCatalog catalog, MethodBinder binder, TypeDef owner, TypeRef voidType)
    {
        var definition = new MethodDef { Index = 1, Owner = owner, Name = "Generic", Token = 0x06000002,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = voidType,
            Parameters = [], GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }] };
        var argument = new DefinitionRef(new TypeDef { Index = 3, Assembly = "mscorlib.dll", Namespace = "System", Name = "Object", Token = 0x02000004,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false }, []);
        var method = new MethodRef(definition, [], [argument]);
        var other = new MethodRef(new MethodDef { Index = 2, Owner = owner, Name = "Other", Token = 0x06000003,
            Attributes = definition.Attributes, ImplAttributes = 0, Slot = -1, ReturnType = voidType,
            Parameters = [], GenericParameters = definition.GenericParameters }, [], [argument]);
        var runtime = catalog.Functions.First(f => f.Operation.Name == "InitializeMethodRgctx" && f.Signature is { ReturnType.Size: > 0 });
        for (int scenario = 0; scenario < 26; scenario++)
        {
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(runtime), catalog);
            var t = new TermTable(); var head = new BlockIdentity(); var arm = new BlockIdentity(); var skip = new BlockIdentity();
            var join = new BlockIdentity(); var handler = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            var slot = new AbstractSlot(SlotKind.Integer);
            var builder = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image };
            var prefix = new List<Statement>();
            Term Read(List<Statement> statements, Term address)
            {
                var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), 64);
                statements.Add(new MemoryRead(id, address, 64, value) { Trace = new(1) }); return value;
            }
            var open = MethodRef.Open(definition);
            var information = scenario == 6 ? t.Atom(new EntryAtom(slot), 64) : Read(prefix, Add(image, 100));
            if (scenario == 6) builder.Inputs.Add(new(slot, information));
            var address = Add(information, spec.Layout.Field("MethodInfo", "rgctx_data").ByteOffset);
            var guard = Read(prefix, address);
            if (scenario == 2) prefix.Add(new Call(new(), new ComputedTarget(t.Constant(1, 64)), [new(slot, guard)], []));
            var tested = scenario == 11 ? t.Slice(guard, 0, 1) : guard;
            var condition = t.Apply(new CoreOperator(scenario is 8 or 24 ? CoreOperation.NotEqual : CoreOperation.Equal), 1, tested, t.Constant(0, tested.Width));
            builder.Blocks.Add(new(head, [], [.. prefix], new Branch(condition, scenario == 8 ? skip : arm, scenario == 8 ? arm : skip)));
            var body = new List<Statement>();
            if (scenario == 3) body.Add(new MemoryWrite(new(), frame, 32, t.Constant(1, 32)));
            var input = scenario is 4 or 7 ? Read(body, Add(image, scenario == 4 ? 200 : 100)) : information;
            var callId = new CallIdentity(); var returned = t.Atom(new ResultAtom(callId), 64);
            var call = new Call(callId, new ImageFunction(20), [new(slot, input)], [new(slot, returned)], Unwind: scenario == 12 ? handler : null);
            body.Add(call);
            var continuation = scenario == 5 ? new List<Statement>() : body;
            // 初始化后的读取有独立身份；守卫读取只供分支使用。
            var table = Read(continuation, scenario == 12 ? Add(returned, spec.Layout.Field("MethodInfo", "rgctx_data").ByteOffset) : address);
            var item = Read(continuation, table);
            if (scenario >= 13)
            {
                // 快路径复用守卫读取；初始化后独立重读，经合流用于取条目。
                body.RemoveAt(body.Count - 1);
                body.RemoveAt(body.Count - 1);
                if (scenario == 25) body.Insert(0, new Call(new(), new ComputedTarget(t.Constant(1, 64)), [], []));
                if (scenario == 15) table = Read(body, Add(Read(body, Add(image, 200)), spec.Layout.Field("MethodInfo", "rgctx_data").ByteOffset));
                else if (scenario == 21) table = Read(body, Add(Read(body, Add(image, 100)), spec.Layout.Field("MethodInfo", "rgctx_data").ByteOffset));
                else if (scenario == 19) table = Read(prefix, address);
                else table = Read(body, address);
                var mergeId = new MergeIdentity(); var merged = t.Atom(new ResultAtom(mergeId), 64);
                var continued = new List<Statement>();
                item = Read(continued, merged);
                if (scenario == 16) continued.Add(new Call(new(), new ComputedTarget(t.Constant(1, 64)), [new(slot, guard)], []));
                var fastValue = scenario == 20 ? Add(guard, 8) : guard;
                var slowValue = scenario == 14 ? t.Constant(7, 64) : scenario == 23 ? t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, t.Slice(table, 0, 32)) : table;
                var fast = scenario is 17 or 24 ? skip : head;
                builder.Blocks.Clear();
                builder.Blocks.Add(new(head, [], [.. prefix], new Branch(condition,
                    scenario == 24 ? skip : arm, scenario == 24 ? arm : fast == skip ? skip : join)));
                builder.Blocks.Add(new(arm, [], [.. body], new Jump(join)));
                if (fast == skip) builder.Blocks.Add(new(skip, [], [new Call(new(), new ComputedTarget(t.Constant(1, 64)), [new(slot, guard)], [])], new Jump(join)));
                builder.Blocks.Add(new(join, [new(mergeId, merged, [new(fast, fastValue), new(arm, slowValue)])], [.. continued], new Return([new(slot, item)])));
                if (scenario == 18)
                {
                    builder.Blocks.Clear();
                    builder.Blocks.Add(new(head, [], [.. prefix], new Branch(condition, arm, skip)));
                    builder.Blocks.Add(new(arm, [], [.. body, .. continued.Select(statement => SnapshotRewrite.Rewrite(statement, value => value == merged ? table : value))], new Return([new(slot, item)])));
                    builder.Blocks.Add(new(skip, [], [], new Return([new(slot, guard)])));
                }
            }
            if (scenario == 10)
            {
                var second = new AbstractSlot(SlotKind.Integer, 1); var control = t.Atom(new EntryAtom(second), 64);
                builder.Inputs.Add(new(second, control));
                builder.Blocks.Add(new(arm, [], [], new Branch(t.Slice(control, 0, 1), join, skip)));
                builder.Blocks.Add(new(join, [], [.. body], new Return([new(slot, item)])));
            }
            else if (scenario < 13)
            {
                builder.Blocks.Add(new(arm, [], [.. body], scenario == 5 ? new Jump(join) : new Return([new(slot, item)])));
                if (scenario == 5) builder.Blocks.Add(new(join, [], [.. continuation], new Return([new(slot, item)])));
            }
            if (scenario < 13) builder.Blocks.Add(new(skip, [], [], scenario == 5 ? new Jump(join) : scenario == 9 ? new Jump(arm) : new Return([new(slot, t.Constant(0, 64))])));
            if (scenario == 12)
            {
                var exception = t.Atom(new ExceptionAtom(handler), 64); var selector = t.Atom(new SelectorAtom(handler), 64);
                builder.Blocks.Add(new(handler, [], [], new ResumeUnwind(exception), new(exception, selector, [new(Cpp2CS.Native.Images.ClauseKind.Cleanup, [])])));
            }
            var facts = NamingFacts.Empty with { Slots = NamingFacts.Empty.Slots
                .Add(100, Outcome<MetadataEntity>.Success(new MethodEntity(method)))
                .Add(200, Outcome<MetadataEntity>.Success(new MethodEntity(other))) };
            if (scenario == 1) facts = NamingFacts.Empty;
            var state = new StateQueries(image: new InputMemoryImage());
            var layouts = new FieldLayouts(spec, 8, 8);
            var selectedSpec = spec;
            if (scenario is 18 or 22)
            {
                var json = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(Path.Combine(ArchitectureChecks.FindRoot(), "spec", "unity-2022.3.62f2-android-lp64.json")))!;
                foreach (var field in json["records"]!["MethodInfo"]!["fields"]!.AsArray()) field!.AsObject().Remove("stable_after_nonzero");
                using var stream = new MemoryStream(System.Text.Encoding.UTF8.GetBytes(json.ToJsonString()));
                selectedSpec = RuntimeSpec.Read(stream, "test", spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
            }
            var names = new ValueNamingQuery(state, calls, facts, selectedSpec, binder,
                scenario == 6 ? binder.Definition(open, BindingEntryKind.SharedGeneric, method).Value : null,
                new GuardContextDecoder(scenario == 6 ? open : method, argument), scenario == 6 ? new GenericWitness(open, method, layouts) : null);
            var function = builder.Freeze();
            checks.True(ExitChecker.Check(function).IsValid, $"泛型上下文守卫 {scenario} 输入契约");
            var output = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }).Run(function);
            checks.True(ExitChecker.Check(output.Function).IsValid, $"泛型上下文守卫 {scenario} 输出契约");
            if (scenario == 13)
            {
                checks.True(spec.Layout.Field("Il2CppClass", "rgctx_data").StableAfterNonzeroEvidence is { Length: > 0 }
                    && spec.Layout.Field("MethodInfo", "rgctx_data").StableAfterNonzeroEvidence is { Length: > 0 }, "两个 RGCTX 字段登记非零后稳定依据");
                checks.True(names.SameValue(names.CreateContext(function), guard, table) is not { IsSuccess: true, Value: true },
                    "非零后稳定性不作为全局不可变凭据消去初始化前后的读取版本");
            }
            bool folded = scenario is 0 or 5 or 6 or 7 or 8 or 12 or 13 or 17 or 18 or 21 or 24;
            checks.True(output.Records.Any(r => r.Kind == "init-guard" && r.Removed) == folded,
                $"泛型上下文守卫 {scenario} 统一模板改写：" + string.Join("；", output.Records.Where(r => r.Reason is not null).Select(r => r.Reason)));
            if (folded)
            {
                checks.True(!output.Function.Blocks.Any(b => b.End is Branch) && !output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(),
                    $"泛型上下文守卫 {scenario} 事件与守卫消去");
                var results = output.Function.Blocks.Select(b => b.End).OfType<Return>().SelectMany(r => r.Results).ToArray();
                checks.True(results.Length == 1 && names.CreateContext(output.Function).Get(names, results[0].Value).Value.Name is EntityName { Entity: ClassEntity { Type: var type } } && type == argument,
                    $"泛型上下文守卫 {scenario} 保留重读与条目使用");
            }
            else
            {
                var reason = scenario switch { 2 => "read-used", 3 => "effect-before-event", 4 => "entity-mismatch", 9 => "shared-prefix", 10 => "branch-before-event", 11 => "test-width", 25 => "effect-before-event", >= 13 => "read-used", _ => "" };
                checks.True(output.Function.Blocks.Any(b => b.End is Branch) && (scenario == 1
                    ? output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any()
                    : output.Records.Any(r => r.Reason?.Code == "structure.init-guard." + reason)),
                    $"泛型上下文守卫 {scenario} 保留控制流和具体原因");
                if (scenario is 14 or 15 or 19 or 20 or 22 or 23)
                    checks.True(output.Records.Any(r => r.Reason?.Code == "structure.init-guard.read-used" && r.Reason.Message.Contains("合流", StringComparison.Ordinal)),
                        $"泛型上下文守卫 {scenario} 拒绝消息指明合流");
            }
        }
    }
}
