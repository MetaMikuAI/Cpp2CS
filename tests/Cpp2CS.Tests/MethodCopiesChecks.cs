using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Pipeline;
using Cpp2CS.Input;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.MethodCopies;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;

namespace Cpp2CS.Tests;

internal static class MethodCopiesChecks
{
    public const string Command = "method-copies";
    public static int Run()
    {
        var checks = new Assertions();
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Cpp2CS.Targets.Arm64.Abi.Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        IsomorphismChecks(checks);
        CandidateChecks(checks, spec, binder, catalog);
        return checks.Finish("托管方法副本");
    }
    private static void IsomorphismChecks(Assertions checks)
    {
        var owner = new TypeDef { Index = 0, Assembly = "test", Namespace = "", Name = "Owner", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var type = new DefinitionRef(owner, []);
        MethodRef Method(string name) => new(new MethodDef { Index = 0, Owner = owner, Name = name, Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = type, Parameters = [] }, [], []);
        var method = Method("Body"); var called = Method("Called"); var other = Method("Other");
        var field = new FieldDef { Index = 0, Owner = owner, Name = "first", Token = 0, Attributes = FieldAttributes.Public, Offset = 0, Type = type };
        var second = new FieldDef { Index = 1, Owner = owner, Name = "second", Token = 1, Attributes = FieldAttributes.Public, Offset = 0, Type = type };
        Cpp2CS.Managed.ManagedBody Body(bool reorder = false, bool inverse = false, int local = 0, int constant = 7,
            bool extra = false, MethodRef? call = null, FieldDef? member = null)
        {
            var value = new Cpp2CS.Managed.LocalValue(new(local), type, 64);
            var one = new Cpp2CS.Managed.ConstantValue((ulong)constant, type, 64);
            var argument = new Cpp2CS.Managed.ArgumentValue(0, type, 64);
            var condition = new Cpp2CS.Managed.ComparisonValue(inverse ? Cpp2CS.Managed.ComparisonKind.NotEqual : Cpp2CS.Managed.ComparisonKind.Equal, value, one, type);
            ulong offset = reorder ? 100UL : 0;
            var head = new Cpp2CS.Managed.ManagedBlock(offset, [new Cpp2CS.Managed.ManagedAssignment(offset, value, one),
                new Cpp2CS.Managed.ManagedCall(offset, new(call ?? called, null, [], false), null),
                new Cpp2CS.Managed.ManagedStore(offset, new Cpp2CS.Managed.FieldValue(argument, new(member ?? field, type), type, 64), value),
                new Cpp2CS.Managed.ManagedBranch(offset, condition, new(offset + (inverse ? 2UL : 1UL), []), new(offset + (inverse ? 1UL : 2UL), []))]);
            var yes = new Cpp2CS.Managed.ManagedBlock(offset + 1, extra
                ? [new Cpp2CS.Managed.ManagedAssignment(offset + 1, value, one), new Cpp2CS.Managed.ManagedReturn(offset + 1, value)]
                : [new Cpp2CS.Managed.ManagedReturn(offset + 1, value)]);
            var no = new Cpp2CS.Managed.ManagedBlock(offset + 2, [new Cpp2CS.Managed.ManagedReturn(offset + 2, one)]);
            return new(method, reorder ? [head, no, yes] : [head, yes, no]);
        }
        var reference = Body();
        checks.True(ManagedBodyIsomorphism.Compare(reference, Body(reorder: true, local: 17)).Isomorphic, "块排布与局部编号不同仍同构");
        checks.True(ManagedBodyIsomorphism.Compare(reference, Body(reorder: true, inverse: true, local: 17)).Isomorphic, "条件取反且目标交换仍同构");
        foreach (var (body, reason) in new[] { (Body(extra: true), "多一条语句"), (Body(constant: 8), "常量不同"), (Body(call: other), "方法不同"), (Body(member: second), "字段不同") })
        {
            var comparison = ManagedBodyIsomorphism.Compare(reference, body);
            checks.True(!comparison.Isomorphic && comparison.Difference!.Message.Contains("语句", StringComparison.Ordinal), reason + "不成立并报告首处差异");
        }
        var changed = Body(reorder: true, local: 17);
        var branch = (Cpp2CS.Managed.ManagedBranch)changed.Blocks[0].Statements[^1];
        var wrongEdges = changed with { Blocks = [changed.Blocks[0] with { Statements = [.. changed.Blocks[0].Statements.Take(3),
            branch with { Taken = branch.Fallthrough, Fallthrough = branch.Taken }] }, .. changed.Blocks.Skip(1)] };
        checks.True(!ManagedBodyIsomorphism.Compare(reference, wrongEdges).Isomorphic, "只交换目标但不取反条件时不成立");
        var wrongLocal = changed with { Blocks = [.. changed.Blocks.Take(2), changed.Blocks[2] with
            { Statements = [new Cpp2CS.Managed.ManagedReturn(101, new Cpp2CS.Managed.LocalValue(new(18), type, 64))] }] };
        checks.True(!ManagedBodyIsomorphism.Compare(reference, wrongLocal).Isomorphic, "同一局部不能对应两个局部");
        var negated = wrongEdges with { Blocks = [wrongEdges.Blocks[0] with { Statements = [.. wrongEdges.Blocks[0].Statements.Take(3),
            ((Cpp2CS.Managed.ManagedBranch)wrongEdges.Blocks[0].Statements[^1]) with { Condition = new Cpp2CS.Managed.NegatedValue(branch.Condition, type) }] }, .. wrongEdges.Blocks.Skip(1)] };
        checks.True(ManagedBodyIsomorphism.Compare(reference, negated).Isomorphic, "显式取反与目标对调相对应");
        var l = Body(); var r = Body(reorder: true, local: 1);
        l = l with { Regions = [new([0], 1, [1], null, Cpp2CS.Managed.ManagedRegionKind.Finally)] };
        r = r with { Regions = [new([100], 101, [101], null, Cpp2CS.Managed.ManagedRegionKind.Finally)] };
        checks.True(ManagedBodyIsomorphism.Compare(l, r).Isomorphic, "异常子句按块对应相等");
        checks.True(!ManagedBodyIsomorphism.Compare(l, r with { Regions = [r.Regions[0] with { Kind = Cpp2CS.Managed.ManagedRegionKind.Fault }] }).Isomorphic, "异常子句种类不同不成立");
    }
    private static void CandidateChecks(Assertions checks, RuntimeSpec spec, MethodBinder binder, RuntimeFunctionCatalog catalog)
    {
        TypeDef Type(string name, string assembly = "test", bool value = false) => new()
        { Index = 0, Assembly = assembly, Namespace = assembly == "mscorlib.dll" ? "System" : "", Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false };
        var objectType = Type("Object", "mscorlib.dll"); var stringType = Type("String", "mscorlib.dll"); var voidType = Type("Void", "mscorlib.dll", true);
        var a = Type("First"); var b = Type("Second"); var owner = Type("Caller");
        a.BaseType = b.BaseType = new DefinitionRef(objectType, []);
        MethodRef Method(TypeDef type, string name, bool isStatic = false, TypeRef? parameter = null, bool native = false, bool inline = false) => new(new MethodDef
        { Index = 0, Owner = type, Name = name, Token = 0, Attributes = MethodAttributes.Public | (isStatic ? MethodAttributes.Static : 0) | (native ? MethodAttributes.PinvokeImpl : 0),
            ImplAttributes = inline ? MethodImplAttributes.AggressiveInlining : 0, Slot = -1, ReturnType = new DefinitionRef(voidType, []), Parameters = parameter is null ? [] : [new("value", parameter, 0, null, false)] }, [], []);
        var first = Method(a, "Apply", inline: true); var second = Method(b, "Apply", inline: true);
        var primitives = new[] { "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64",
            "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle" }
            .Select(name => Type(name, "mscorlib.dll", true)).ToArray();
        var model = new ProgramModel { MetadataVersion = 0, Assemblies = [], Types = [objectType, stringType, voidType, a, b, owner, .. primitives],
            Methods = [first.Method, second.Method], Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [] };
        var image = new InputMemoryImage { Executable = true, Functions = [new(64, 4, FunctionEvidence.UnwindTable),
            new(128, 16, FunctionEvidence.UnwindTable), new(192, 4, FunctionEvidence.UnwindTable), new(256, 12, FunctionEvidence.UnwindTable), new(384, 8, FunctionEvidence.UnwindTable), new(448, 4, FunctionEvidence.UnwindTable)] };
        foreach (ulong address in new ulong[] { 64, 96, 128, 192, 264, 388, 448 }) image.Put(address, 0xd65f03c0, 4);
        image.Put(128, 0xa9bf7bfd, 4); // 保存帧与返回地址。
        image.Put(132, 0x910003fd, 4);
        image.Put(136, 0xa8c17bfd, 4);
        image.Put(140, 0xd65f03c0, 4);
        image.Put(256, 0x97ffffd0, 4);
        image.Put(260, 0x97ffffd7, 4); // 分别调用有范围的 64 与无范围的 96。
        image.Put(384, 0x94000010, 4);
        var nativeEntry = Method(owner, "Native", true, native: true);
        var callerEntry = Method(owner, "Entry", true, first.DeclaringType);
        var entries = new CodeEntry[] { new(128, EntryKind.Method, first, 0, null), new(192, EntryKind.Method, second, 1, null),
            new(256, EntryKind.Method, callerEntry, 2, null), new(384, EntryKind.Method, nativeEntry, 3, null) };
        var registrations = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = entries,
            ByAddress = entries.ToDictionary(e => e.Address, e => ImmutableArray.Create(e)), Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(),
            MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
        var global = new GlobalFacts(image, model, registrations, spec, "arm64");
        var copies = global.MethodCopies.Facts;
        checks.True(global.MethodCopies.LiftedTargets == 0, "普查与索引不提前恢复全部未注册目标");
        checks.True(copies.At(64).Length == 2 && copies.At(64).Select(e => e.Method).ToHashSet().SetEquals([first, second]),
            "帧保存不同的原生体恢复同构，两个注册身份均保留");
        checks.True(!global.MethodCopies.Callers.ContainsKey(448), "没有 CIL 方法体的原生包装不作为托管调用方");
        copies.At(96);
        checks.True(global.MethodCopies.Callers.ContainsKey(96) && global.MethodCopies.Missing[96].Code == "method-copy.range",
            "没有函数范围的直接目标也进入普查，并保持带原因的未知");
        checks.True(global.MethodCopies.LiftedTargets == 1 && global.MethodCopies.LiftedRegistered == 3,
            "只提升被调用目标与索引命中的候选，递归候选不污染已证明身份");
        var brokenImage = new InputMemoryImage { Executable = true, Functions = image.Functions };
        foreach (ulong address in new ulong[] { 64, 264 }) brokenImage.Put(address, 0xd65f03c0, 4);
        brokenImage.Put(128, 0xffffffff, 4); brokenImage.Put(256, 0x97ffffd0, 4); brokenImage.Put(260, 0x97ffffd7, 4);
        var brokenEntries = new[] { entries[0], entries[2] with { Method = Method(owner, "BodylessCandidateCaller", true) } };
        var brokenMap = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = brokenEntries,
            ByAddress = brokenEntries.ToDictionary(e => e.Address, e => ImmutableArray.Create(e)), Rgctx = registrations.Rgctx,
            MetadataUsageSlots = [], TypePointers = registrations.TypePointers, InvokerOf = registrations.InvokerOf, UsageEntities = registrations.UsageEntities };
        var broken = new GlobalFacts(brokenImage, model, brokenMap, spec, "arm64").MethodCopies;
        checks.True(broken.Facts.At(64).IsEmpty && broken.Missing[64].Code == "method-copy.registered-hole"
            && broken.Missing[64].Cause is not null, "候选的注册体有洞时拒绝，并保留原始原因");
        var types = new ManagedTypes(model, new FieldLayouts(spec, 8, 8), 8);
        foreach (var arguments in new[] { false, true })
        foreach (var specific in new[] { true, false })
        {
            var caller = Method(owner, "Use", true, new DefinitionRef(specific ? a : objectType, []));
            var currentFirst = arguments ? Method(owner, "First", true, first.DeclaringType) : first;
            var currentSecond = arguments ? Method(owner, "Second", true, second.DeclaringType) : second;
            var currentCopies = arguments ? new MethodCopyFacts(new Dictionary<ulong, ImmutableArray<MethodCopyCandidate>>
            { [64] = [new(128, new(currentFirst, BindingEntryKind.Ordinary, "method-copy")), new(192, new(currentSecond, BindingEntryKind.Ordinary, "method-copy"))] }) : copies;
            var t = new TermTable(); var block = new BlockIdentity(); var value = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
            var call = new Call(new(), new ImageFunction(64), [new(new(SlotKind.Integer), value), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], []);
            var builder = new FunctionBuilder(t, block, 64, new(frame)); builder.Inputs.Add(new(new(SlotKind.Integer), value));
            builder.Blocks.Add(new(block, [], [call], new Return([])));
            var function = builder.Freeze();
            var calls = new CallNamingQuery(binder, currentCopies, new NamingChecks.RuntimeMap(), catalog);
            var state = new StateQueries(); var names = new ValueNamingQuery(state, calls, NamingFacts.Empty, spec, binder, binder.Entry(caller, BindingEntryKind.Ordinary).Value);
            var result = names.CreateContext(function).Get(new DirectCallQuery(calls, names, new(state), types), call.Identity);
            checks.True(specific ? result.IsSuccess && result.Value.Entry.Method == currentFirst
                : !result.IsSuccess && result.Why!.Message.Contains("2 个候选", StringComparison.Ordinal), specific ? (arguments ? "实参静态类型唯一时采纳" : "接收者类型唯一时采纳") : "类型不能区分时保留候选数与歧义原因");
            var lowered = new IntegerLowering(function, caller, binder, types, new InputMemoryImage(), calls,
                spec: spec).Run();
            checks.True(specific ? lowered.Body is not null
                : lowered.Failure?.Reason.Code == "lowering.MethodCopy.Ambiguous" && lowered.Failure.Reason.Message.Contains("2 个候选", StringComparison.Ordinal),
                specific ? $"唯一候选走普通调用下降（实参模式={arguments}）：{lowered.Failure}" : "身份歧义成为带候选数的洞");
        }
    }
}
