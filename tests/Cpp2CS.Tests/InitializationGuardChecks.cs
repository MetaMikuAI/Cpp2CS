using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
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
        return checks.Finish("初始化守卫");
    }
}
