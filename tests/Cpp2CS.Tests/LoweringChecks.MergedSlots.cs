using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;
namespace Cpp2CS.Tests;
internal static partial class LoweringChecks
{
    private sealed class MergedSlotDecoder(NamingFacts facts) : IMetadataSlotDecoder
    {
        public Outcome<MetadataEntity> Decode(ulong address) => facts.Slots.GetValueOrDefault(address)
            is { IsSuccess: true } entity ? entity : Outcome<MetadataEntity>.Failure(new("test.slot", "不是已登记的元数据槽位。"));
    }
    private static void MergedSlotChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = "MergedSlots.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, BaseType = Type("Object") };
            definitions.Add(type); return type;
        }
        var owner = Define("Cases"); var error = Define("MessageError"); var other = Define("OtherError");
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, bool constructor = false)
        {
            var method = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (constructor ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : MethodAttributes.Static), ImplAttributes = 0, Slot = -1,
                ReturnType = Type("Void"), Parameters = [new("value", Type(constructor ? "String" : "Boolean"), 0, null, false)] };
            methods.Add(method); type.Methods = type.Methods.Append(method).ToArray(); return method;
        }
        var constructor = Method(error, ".ctor", true);
        string[] modes = ["Phi", "Select", "InlinePhi", "InlineSelect", "ReadPhi", "ReadSelect", "ConditionSelect", "Invalid", "InvalidSelect", "ReadInvalidPhi", "ReadInvalidSelect", "SameClass", "DifferentClass", "SameMethod", "DifferentMethod", "UnusedClass"];
        var callers = modes.ToDictionary(mode => mode, mode => Method(owner, mode));
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new ReferenceCodeMap(constructor), new NamingChecks.RuntimeMap(catalog.Functions[0]), catalog);
        using var source = new CompiledSource("""
            public class MessageError : System.Exception { public MessageError(string message) : base(message) { } }
            public class OtherError : System.Exception { }
            public static class Cases {
                public static void Reference(bool value) { if (value) throw new MessageError("left message"); throw new MessageError("right message"); }
                public static void Output(bool value) { }
            }
            """);
        foreach (var mode in modes)
        {
            var t = new TermTable(); var head = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity(); var join = new BlockIdentity();
            var slow = new BlockIdentity(); var tail = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var slot = new AbstractSlot(SlotKind.Integer); var parameter = t.Atom(new EntryAtom(slot), 64);
            var f = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = image }; f.Inputs.Add(new(slot, parameter));
            Term Address(ulong offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(offset, 64));
            var facts = NamingFacts.Empty with { Slots = new Dictionary<ulong, Outcome<MetadataEntity>> {
                [128] = Outcome<MetadataEntity>.Success(mode is "SameClass" or "DifferentClass" ? new ClassEntity(Type("MessageError")) : new StringEntity("left message")),
                [136] = Outcome<MetadataEntity>.Success(mode is "SameClass" or "DifferentClass" ? new ClassEntity(Type(mode == "SameClass" ? "MessageError" : "OtherError")) : new StringEntity("right message")),
                [144] = Outcome<MetadataEntity>.Success(new ClassEntity(Type("MessageError"))) }.ToImmutableDictionary() };
            if (mode == "UnusedClass") facts = facts with { Slots = facts.Slots
                .SetItem(128, Outcome<MetadataEntity>.Success(new ClassEntity(Type("MessageError"))))
                .SetItem(136, Outcome<MetadataEntity>.Success(new ClassEntity(Type("OtherError")))) };
            if (mode is "SameMethod" or "DifferentMethod") facts = facts with { Slots = facts.Slots
                .SetItem(128, Outcome<MetadataEntity>.Success(new MethodEntity(MethodRef.Open(callers["Phi"]))))
                .SetItem(136, Outcome<MetadataEntity>.Success(new MethodEntity(MethodRef.Open(callers[mode == "SameMethod" ? "Phi" : "Select"])))) };
            var id = new MergeIdentity(); var address = t.Atom(new ResultAtom(id), 64); var condition = t.Slice(parameter, 0, 1);
            bool select = mode.EndsWith("Select", StringComparison.Ordinal);
            var headStatements = new List<Statement>();
            if (mode == "ConditionSelect")
            {
                var flag = new ReadIdentity(); var value = t.Atom(new ResultAtom(flag), 64);
                headStatements.Add(new MemoryRead(flag, Address(160), 64, value)); condition = t.Slice(value, 0, 1);
            }
            var second = mode.Contains("Invalid", StringComparison.Ordinal) ? parameter : Address(136);
            if (select) { address = t.Apply(new CoreOperator(CoreOperation.Select), 64, condition, Address(128), second); f.Blocks.Add(new(head, [], [.. headStatements], new Jump(join))); }
            else
            {
                f.Blocks.Add(new(head, [], [], new Branch(condition, left, right)));
                f.Blocks.Add(new(left, [], [], new Jump(join))); f.Blocks.Add(new(right, [], [], new Jump(join)));
            }
            var statements = new List<Statement>();
            Term Read(Term at, List<Statement> list)
            {
                var read = new ReadIdentity(); var value = t.Atom(new ResultAtom(read), 64); list.Add(new MemoryRead(read, at, 64, value)); return value;
            }
            Term Invoke(string name, List<Statement> list, params Term[] args)
            {
                var runtime = catalog.Functions.First(r => r.Operation.Name == name && r.Signature is not null && (name != "InitializeMetadata" || r.Signature.ReturnType.Size > 0));
                var call = new CallIdentity(); var value = t.Atom(new ResultAtom(call), 64);
                list.Add(new Call(call, new NamedFunction(runtime.MangledName), args.Select((v, i) => new SlotValue(new(SlotKind.Integer, i), v)).ToImmutableArray(),
                    runtime.Operation.Result.Kind == RuntimeValueKind.Void ? [] : [new(slot, value)], runtime.Operation.DoesNotReturn) { Trace = new(name == "InitializeMetadata" ? 40UL : name == "AllocateObject" ? 48UL : 64UL) });
                return value;
            }
            Term contents;
            if (mode.StartsWith("Inline", StringComparison.Ordinal))
            {
                var fast = Read(address, statements); var slowStatements = new List<Statement>(); var initialized = Invoke("InitializeMetadata", slowStatements, address);
                f.Blocks.Add(new(join, select ? [] : [new(id, address, [new(left, Address(128)), new(right, second)])], [.. statements],
                    new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, t.Apply(new CoreOperator(CoreOperation.And), 64, fast, t.Constant(1, 64)), t.Constant(0, 64)), tail, slow)));
                f.Blocks.Add(new(slow, [], [.. slowStatements], new Jump(tail)));
                var merged = new MergeIdentity(); contents = t.Atom(new ResultAtom(merged), 64); statements = [];
                f.Blocks.Add(new(tail, [new(merged, contents, [new(join, fast), new(slow, initialized)])], [], new Unreachable()));
            }
            else contents = mode.StartsWith("Read", StringComparison.Ordinal) ? Read(address, statements) : Invoke("InitializeMetadata", statements, address);
            if (mode == "UnusedClass") Invoke("GetThreadStaticData", statements, contents);
            var klass = mode is "SameClass" or "DifferentClass" ? contents : Read(Address(144), statements);
            var allocated = Invoke("AllocateObject", statements, klass);
            statements.Add(new Call(new(), new ImageFunction(10), [new(slot, allocated), new(new(SlotKind.Integer, 1), mode is "SameClass" or "DifferentClass" or "SameMethod" or "DifferentMethod" or "UnusedClass" ? t.Constant(0, 64) : contents), new(new(SlotKind.Integer, 2), t.Constant(0, 64))], []) { Trace = new(56) });
            Invoke("ThrowManaged", statements, allocated, mode is "SameMethod" or "DifferentMethod" ? contents : t.Constant(0, 64));
            if (mode.StartsWith("Inline", StringComparison.Ordinal)) f.Blocks[^1] = f.Blocks[^1] with { Statements = [.. statements] };
            else f.Blocks.Add(new(join, select ? [] : [new(id, address, [new(left, Address(128)), new(right, second)])], [.. statements], new Unreachable()));
            var input = f.Freeze(); checks.True(ExitChecker.Check(input).IsValid, mode + " 输入契约");
            if (!mode.StartsWith("Read", StringComparison.Ordinal))
            {
                var survey = new NamingSurvey(calls, new MergedSlotDecoder(facts), new InputMemoryImage(), binder, spec);
                survey.Observe(input);
                checks.True(survey.Finish().Slots.ContainsKey(128) && (mode.Contains("Invalid", StringComparison.Ordinal)
                    || survey.Finish().Slots.ContainsKey(136)), mode + " 调查解码每个合流或选择槽位");
            }
            var state = new StateQueries(image: new InputMemoryImage()); var naming = new ValueNamingQuery(state, calls, facts, spec, binder, binder.Entry(MethodRef.Open(callers[mode]), BindingEntryKind.Ordinary).Value, stringType: types.String);
            var output = new UnobservableEffects(state, calls, naming, new InputMemoryImage(), new HashSet<AbstractSlot>()).Run(input);
            checks.True(ExitChecker.Check(output.Function).IsValid, mode + " 改写契约");
            var remaining = output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Count(c => c.Target is NamedFunction target && catalog.Functions.Any(r => r.MangledName == target.Name && r.Operation.Name == "InitializeMetadata"));
            checks.True(remaining == (mode.StartsWith("Invalid", StringComparison.Ordinal) ? 1 : 0), mode + " 初始化结果分配后消去调用");
            if (mode.Contains("Invalid", StringComparison.Ordinal)) { checks.True(ReferenceEquals(output.Function, input), "未证明输入不提交部分槽位改写"); checks.True(output.Records.Any(r => r.Reason?.Code.StartsWith("structure.merged-slot.", StringComparison.Ordinal) == true), "非槽位输入保留逐输入拒绝原因"); continue; }
            if (mode == "ConditionSelect")
            {
                var used = SnapshotRewrite.Dependencies(output.Function.Blocks.SelectMany(b => b.Statements.SelectMany(SnapshotRewrite.Uses)));
                checks.True(used.Any(t => t.Operator is CoreOperator { Operation: CoreOperation.Select } && t.Operands[0] == condition), "值选择保留原始读取条件，不写入内存状态词汇");
                continue;
            }
            if (!select && mode is not ("SameClass" or "SameMethod"))
                checks.True(output.Function.Blocks.Single(b => b.Identity == join).Merges.Any(m => m.Identity.Origin == id
                    && m.Inputs.Select(i => i.Predecessor).SequenceEqual(new[] { left, right })), mode + " 内容合流保留原块、来源身份与入边顺序");
            if (mode.StartsWith("Inline", StringComparison.Ordinal)) checks.True(output.Function.Blocks.Count(b => b.End is Branch) == (select ? 0 : 1), mode + " 快慢路径同值合流消去");
            if (mode == "DifferentMethod")
            {
                checks.True(output.Records.Any(r => r.Why?.Code == "structure.merged-slot.use.ThrowManaged.method"), "路径变化的方法信息不作为不可观察抛出输入放行");
                continue;
            }
            var lowered = new IntegerLowering(output.Function, MethodRef.Open(callers[mode]), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            if (mode == "DifferentClass") { checks.True(lowered.Body is null && output.Records.Any(r => r.Why?.Code == "structure.merged-slot.use.AllocateObject.class"), "不同类的初始化可消去，newobj 保持路径实体洞"); continue; }
            checks.True(lowered.Body is not null, mode + " 下降：" + lowered.Failure); if (lowered.Body is not { } body) continue;
            checks.True(emitter.Emit([body]).Count == 0, mode + " CIL 校验");
            if (mode == "UnusedClass")
            {
                checks.True(!output.Records.Any(r => r.Why?.Code.StartsWith("structure.merged-slot.use.", StringComparison.Ordinal) == true), "唯一不可观察使用消去后不保留路径实体洞");
                continue;
            }
            if (mode is "SameClass" or "SameMethod") continue;
            var tested = source.Method("Cases", "Output"); tested.Body = skeleton.Method(callers[mode]).Body;
            var core = source.Module.TypeSystem.Object.Resolve().Module;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => source.Module.ImportReference(source.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
            foreach (var local in tested.Body.Variables) local.VariableType = MapType(local.VariableType);
            foreach (var instruction in tested.Body.Instructions) instruction.Operand = instruction.Operand switch {
                Mono.Cecil.MethodReference method => source.Module.ImportReference(source.Module.GetType(method.DeclaringType.FullName).Methods.Single(m => m.FullName == method.FullName)),
                Mono.Cecil.TypeReference type => MapType(type), Mono.Cecil.ParameterDefinition p => tested.Parameters[p.Index], _ => instruction.Operand };
            var comparison = CilComparison.Compare(source.Method("Cases", "Reference"), tested);
            checks.True(comparison.Status == CilComparisonStatus.Match, mode + " 两条路径异常消息执行对照：" + comparison);
            checks.True(comparison.Coverage?.Branches.All(b => b.Directions.All(x => x)) == true, mode + " 两个方向均执行");
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
