using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static class InitializationFlagChecks
{
    public const string Command = "init-flags";
    private sealed class Decoder : IMetadataSlotDecoder
    { public Outcome<MetadataEntity> Decode(ulong address) => Outcome<MetadataEntity>.Failure(new("test.slot", "合成槽位没有实体。")); }
    public static int Run()
    {
        var checks = new Assertions(); var spec = InputCorpusChecks.Spec("arm64-v8a");
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var runtime = catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is { ReturnType.Size: 0 });
        var type = new TypeDef { Index = 0, Assembly = "test", Namespace = "", Name = "Owner", Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        DefinitionRef Primitive(string name, int size) => new(new TypeDef { Index = size, Assembly = "mscorlib.dll", Namespace = "System", Name = name, Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false, Size = size }, []);
        var single = Primitive("Single", 4); var voidType = Primitive("Void", 0);
        var method = new MethodRef(new MethodDef { Index = 0, Owner = type, Name = "Apply", Token = 0, Attributes = MethodAttributes.Static, ImplAttributes = 0,
            Slot = -1, ReturnType = voidType, Parameters = [new("value", single, 0, null, false)] }, [], []);
        var caller = new MethodRef(new MethodDef { Index = 1, Owner = type, Name = "Caller", Token = 0, Attributes = MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = single, Parameters = [] }, [], []);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(method, BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(runtime), catalog);
        for (int scenario = 0; scenario < 15; scenario++)
        {
            var t = new TermTable(); var head = new BlockIdentity(); var arm = new BlockIdentity(); var skip = new BlockIdentity(); var join = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            Term Add(int offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(offset, 64));
            var flag = Add(200); var slot = new AbstractSlot(SlotKind.Integer); var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), 8);
            var statements = new List<Statement> { new MemoryRead(id, flag, 8, value) { Trace = new(100) } };
            var metadata = new Call(new(), new ImageFunction(20), [new(slot, Add(300))], []);
            if (scenario == 4) statements.Add(new Call(new(), new ComputedTarget(t.Constant(1, 64)), [new(slot, t.Concat(value, t.Constant(0, 56)))], []));
            if (scenario == 5)
            {
                var other = new ReadIdentity(); statements.Add(new MemoryRead(other, flag, 8, t.Atom(new ResultAtom(other), 8)) { Trace = new(101) });
            }
            if (scenario == 6) statements.Add(metadata with { Identity = new(), Arguments = metadata.Arguments.Add(new(new(SlotKind.IndirectResult), t.Concat(value, t.Constant(0, 56)))) });
            if (scenario == 8) statements.Add(new Call(new(), new ImageFunction(10), [new(slot, t.Constant(0, 64)), new(new(SlotKind.Floating), t.Concat(t.Constant(0, 32), value, t.Undefined(88)))], []));
            if (scenario is 13 or 14)
            {
                var otherRead = new ReadIdentity();
                var address = scenario == 13
                    ? t.Apply(new CoreOperator(CoreOperation.Select), 64, t.Unknown(1, new("test.choice", "地址选择")), flag, Add(201))
                    : t.Apply(new CoreOperator(CoreOperation.Add), 64, Add(400), t.Concat(t.Unknown(1, new("test.index", "独立表的下标")), t.Constant(0, 63)));
                statements.Add(new MemoryRead(otherRead, address, 8, t.Atom(new ResultAtom(otherRead), 8)) { Trace = new(104) });
            }
            if (scenario == 10) statements.Add(new MemoryWrite(new(), Add(199), 16, t.Constant(0, 16)) { Trace = new(102) });
            var write = new MemoryWrite(new(), flag, 8, t.Constant(scenario == 2 ? 0 : scenario == 3 ? 2 : 1, 8)) { Trace = new(103) };
            var body = scenario == 1 ? ImmutableArray.Create<Statement>(write) : ImmutableArray.Create<Statement>(metadata, write);
            var start = scenario == 11 ? new BlockIdentity() : head;
            var builder = new FunctionBuilder(t, start, 64, new(frame)) { ImageBase = image };
            if (scenario == 11) builder.Blocks.Add(new(start, [], [], new Branch(t.Unknown(1, new("test.path", "另一入口")), head, arm)));
            builder.Blocks.Add(new(head, [], statements.ToImmutableArray(), new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, value, t.Constant(0, 8)), arm, skip)));
            bool merged = scenario is 7 or 9 or 12;
            builder.Blocks.Add(new(arm, [], body, merged ? new Jump(join) : new Return([])));
            builder.Blocks.Add(new(skip, [], [], merged ? new Jump(join) : new Return([])));
            SignatureBinding? entry = null;
            if (merged)
            {
                var merge = new MergeIdentity(); var result = t.Atom(new ResultAtom(merge), 128);
                var input = scenario == 12 ? t.Concat(value, t.Constant(0, 24), t.Undefined(96)) : t.Concat(t.Constant(0, 32), value, t.Undefined(88));
                builder.Blocks.Add(new(join, [new(merge, result, [new(arm, input), new(skip, input)])], [], scenario is 9 or 12 ? new Return([new(new(SlotKind.Floating), result)]) : new Return([])));
                if (scenario is 9 or 12) entry = binder.Entry(caller, BindingEntryKind.Ordinary).Value;
            }
            var function = builder.Freeze(); checks.True(ExitChecker.Check(function).IsValid, $"字节凭据 {scenario} 输入契约");
            var survey = new NamingSurvey(calls, new Decoder(), new InputMemoryImage(), binder, spec, entry);
            survey.Observe(function); var evidence = survey.Finish().Flags[200];
            bool expected = scenario is 0 or 3 or 6 or 7 or 8 or 9 or 14;
            checks.True(evidence.IsFlag == expected, $"字节凭据 {scenario} 判定：{string.Join("；", evidence.Reasons.Select(r => r.Message))}");
            if (scenario is 1 or 5) checks.True(evidence.Reasons.Any(r => r.Message.Contains(scenario == 1 ? "0x67" : "0x65", StringComparison.Ordinal)), "凭据拒绝指出具体访问");
            survey.Incomplete(); checks.True(survey.Finish().Flags[200].IsFlag == evidence.IsFlag, "未观察函数不影响当前函数的模板凭据");
        }
        checks.True(InitializationFlagCorpusChecks.NoIndirectResult("_ZN4test5OwnerC2EPv")
            && InitializationFlagCorpusChecks.NoIndirectResult("_ZN4test5OwnerD2Ev")
            && !InitializationFlagCorpusChecks.NoIndirectResult("_ZN4test5Owner3D2EEv"), "C++ 特殊成员的间接结果协议按名字语法区分，普通同形标识符不匹配");
        return checks.Finish("方法初始化标志凭据");
    }
}
