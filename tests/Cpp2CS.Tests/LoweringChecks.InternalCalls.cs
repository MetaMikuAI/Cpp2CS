using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.RuntimeFunctions;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Output;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private sealed class InternalCallImage(string name) : IImage
    {
        private readonly InputMemoryImage data = Make(name);
        private static InputMemoryImage Make(string value)
        {
            var image = new InputMemoryImage(); var bytes = Encoding.UTF8.GetBytes(value + "\0");
            for (int i = 0; i < bytes.Length; i++) image.Put((ulong)(512 + i), bytes[i], 1);
            return image;
        }
        public ulong PreferredBase => data.PreferredBase;
        public int PointerWidth => 8;
        public ByteOrder ByteOrder => data.ByteOrder;
        public ImmutableArray<ImageRange> Ranges => [new(0, 512, StorageKind.FileContent, false, true), new(512, 3584, StorageKind.FileContent, false, false)];
        public IReadOnlyList<ImageRelocation> Relocations => [];
        public ImmutableArray<ImportSymbol> Imports => [];
        public ImmutableArray<ExportSymbol> Exports => [];
        public ImmutableArray<FunctionSymbol> FunctionSymbols => [];
        public ImmutableArray<FunctionRange> Functions => [];
        public ImmutableArray<TryRegion> TryRegions => [];
        public ImmutableArray<string> Diagnostics => [];
        public AddressInfo Query(ulong offset) => data.Query(offset) with { Writable = offset < 512, AvailableBytes = offset < 512 ? 512 - offset : data.Query(offset).AvailableBytes };
        public bool IsExecutable(ulong offset, ulong length = 1) => false;
        public bool IsWritable(ulong offset, ulong length = 1) => offset < 512 && length <= 512 - offset;
        public void ReadBytes(ulong offset, Span<byte> destination) => data.ReadBytes(offset, destination);
        public ulong ReadUnsigned(ulong offset, int width) => data.ReadUnsigned(offset, width);
        public PointerTarget ReadPointer(ulong offset) => data.ReadPointer(offset);
    }

    private static void InternalCallWrapperChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var layouts = new FieldLayouts(spec, 8, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var owner = new TypeDef { Index = primitives.Types.Count, Assembly = "WrapperChecks.dll", Namespace = "Checks", Name = "Wrappers", Token = 0x02000001,
            Attributes = TypeAttributes.Public | TypeAttributes.BeforeFieldInit, IsValueType = false, IsEnum = false,
            BaseType = new DefinitionRef(primitives.Types.Single(t => t.FullName == "System.Object"), []) };
        var methods = new List<MethodDef>(primitives.Methods);
        TypeRef integer = new DefinitionRef(primitives.Types.Single(t => t.FullName == "System.Int32"), []);
        MethodRef Method(string name, int parameters, bool instance = false, bool internalCall = true)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = (uint)(0x06000001 + owner.Methods.Count),
                Attributes = MethodAttributes.Public | MethodAttributes.HideBySig | (instance ? 0 : MethodAttributes.Static), ImplAttributes = internalCall ? MethodImplAttributes.InternalCall : 0, Slot = -1,
                ReturnType = integer, Parameters = Enumerable.Range(0, parameters).Select(i => new ParameterDef("p" + i, integer, 0, null, false)).ToArray() };
            methods.Add(method); owner.Methods = methods.Where(m => m.Owner == owner).ToArray(); return MethodRef.Open(method);
        }
        var getter = Method("Read", 0); var argument = Method("Apply", 2); var receiver = Method("Receiver", 1, true); var cached = Method("Cached", 1);
        var ordinary = Method("ThrowManaged", 0, internalCall: false); var ordinaryCaller = Method("ManagedCaller", 0, internalCall: false);
        var assembly = new AssemblyDef { Name = owner.Assembly, AssemblyName = "WrapperChecks", Version = new(1, 0), Culture = "", PublicKey = [], Types = [owner] };
        var model = new ProgramModel { MetadataVersion = 0, Assemblies = [.. primitives.Assemblies, assembly], Types = [.. primitives.Types, owner], Methods = methods,
            Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [] };
        var types = new ManagedTypes(model, layouts, 8);
        var state = new StateQueries();
        var discovered = new List<(ulong Entry, InternalCallForwarder Forwarder)>();
        foreach (var (method, scenario) in new[] { (getter, "Getter"), (argument, "Arguments"), (receiver, "Receiver"), (receiver, "ReceiverReordered"), (argument, "Reordered"), (argument, "InformationFirst"), (argument, "ExtraWrite"), (argument, "Adjusted") })
        {
            var t = new TermTable(); var block = new BlockIdentity(); var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
            var f = new FunctionBuilder(t, block, 64, new(frame));
            var signature = binder.Entry(method, BindingEntryKind.Ordinary).Value!;
            var args = new List<SlotValue>();
            for (int i = 0; i < signature.Slots.Parameters.Length; i++)
            foreach (var piece in signature.Slots.Parameters[i].Pieces)
            {
                var value = t.Atom(new EntryAtom(piece.Slot), 64); f.Inputs.Add(new(piece.Slot, value));
                if (i != signature.Managed!.MethodInformationIndex) args.Add(new(piece.Slot, value));
            }
            if (scenario == "InformationFirst")
            {
                var information = f.Inputs.Single(i => i.Slot == signature.Slots.Parameters[signature.Managed!.MethodInformationIndex].Pieces.Single().Slot).Value;
                args = [new(new(SlotKind.Integer), information), new(new(SlotKind.Integer, 1), args[0].Value), new(new(SlotKind.Integer, 2), args[1].Value)];
            }
            if (scenario is "Reordered" or "ReceiverReordered") (args[0], args[1]) = (args[0] with { Value = args[1].Value }, args[1] with { Value = args[0].Value });
            if (scenario == "Adjusted") args[0] = args[0] with { Value = t.Apply(new CoreOperator(CoreOperation.Add), 64, args[0].Value, t.Constant(1, 64)) };
            var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
            var statements = new List<Statement> { new Call(id, new ImageFunction(40), [.. args], [new(new(SlotKind.Integer), result)]) };
            if (scenario == "ExtraWrite") statements.Add(new MemoryWrite(new(), args[0].Value, 32, t.Constant(1, 32)));
            f.Blocks.Add(new(block, [], [.. statements], new Return([new(new(SlotKind.Integer), result)])));
            var proof = InternalCallWrappers.Forwarder(method, f.Freeze(), binder, state);
            bool positive = scenario is not ("ExtraWrite" or "Adjusted");
            checks.True(proof.IsSuccess == positive, "内部调用包装纯转发判定：" + scenario + " " + proof.Why);
            if (!proof.IsSuccess) continue;
            var facts = new InternalCallFacts([(40, proof.Value)], []);
            var naming = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog, facts);
            var classified = state.CreateContext(f.Freeze()).Get(naming, id);
            checks.True(classified.Value.Candidates?.Candidates.Single().Entry.Method == method, "内部调用直接实现得到包装身份：" + scenario);
            var bound = classified.Value.Candidates!.Candidates.Single().Binding.Value!;
            checks.True(bound.Parameters.Length == method.Method.Parameters.Count && (bound.This is not null) == !method.Method.IsStatic, "内部调用实参和接收者由包装给出：" + scenario);
            var lowered = new IntegerLowering(f.Freeze(), method, binder, types, calls: naming, effects: new ManagedCallEffects(naming), spec: spec).Run();
            checks.True(lowered.Body is not null, "直接内部调用完整下降：" + scenario + " " + lowered.Failure);
            if (lowered.Body is { } managedBody)
                checks.True(managedBody.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Invocation.Method == method,
                    "直接内部调用写出包装给出的同一方法：" + scenario);
            if (scenario == "Reordered") checks.True(proof.Value.Inputs.Take(2).SequenceEqual([1, 0]), "固定重排实际记录，现场逆向绑定");
            if (method == getter) discovered.Add((40, proof.Value));
        }
        var alias = Method("Alias", 0); var ambiguous = new InternalCallFacts([discovered[0], (40, discovered[0].Forwarder with { Method = alias })], []);
        checks.True(ambiguous.Direct.Count == 0 && ambiguous.Ambiguous == 1, "同实现被两个不同内部调用定义转发时无身份");
        {
            var t = new TermTable(); var block = new BlockIdentity(); var f = new FunctionBuilder(t, block, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
            f.Blocks.Add(new(block, [], [new Call(id, new ImageFunction(40), [], [new(new(SlotKind.Integer), result)])], new Jump(block)));
            checks.True(InternalCallWrappers.Forwarder(getter, f.Freeze(), binder, state).Why?.Code == "icall.wrapper.control", "重复调用的无返回循环不登记为纯转发");
        }
        {
            var t = new TermTable(); var block = new BlockIdentity(); var f = new FunctionBuilder(t, block, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
            f.Blocks.Add(new(block, [], [new Call(id, new ImageFunction(40), [], [new(new(SlotKind.Integer), result)], DoesNotReturn: true)], new Unreachable()));
            var naming = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog, new InternalCallFacts(discovered, []));
            var lowered = new IntegerLowering(f.Freeze(), getter, binder, types, calls: naming, effects: new ManagedCallEffects(naming), spec: spec).Run();
            checks.True(lowered.Body is null && lowered.Failure?.Reason is { Code: "lowering.CallTermination", Message: var message }
                && message.Contains("内部调用", StringComparison.Ordinal), "内部调用的运行时实现不返回时保留洞并区分原因");
            f.Blocks[0] = f.Blocks[0] with { Statements = [new Call(id, new ImageFunction(10), [new(new(SlotKind.Integer), t.Constant(0, 64))],
                [new(new(SlotKind.Integer), result)], DoesNotReturn: true)] };
            var ordinaryNaming = new CallNamingQuery(binder, new NamingChecks.Map([new(ordinary, BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
            var normal = new IntegerLowering(f.Freeze(), ordinaryCaller, binder, types, calls: ordinaryNaming,
                effects: new ManagedCallEffects(ordinaryNaming), spec: spec, runtimeThrowStub: _ => Outcome<bool>.Success(false)).Run();
            checks.True(normal.Body is not null && normal.Body.Blocks.SelectMany(b => b.Statements).Last() is ManagedThrow,
                "普通托管体不返回时沿用不可达收尾：" + normal.Failure);
            if (normal.Body is { } body)
            {
                var skeleton = new Skeleton(model, 16); var emitter = new BodyEmitter(skeleton, types);
                var target = new ManagedBody(ordinary, [new(0, [new ManagedThrow(0, new ConstantValue(0, types.Object, 64))])]);
                checks.True(emitter.Emit([target, body]).Count == 0, "普通托管不返回调用和不可达收尾通过写出契约");
                using var reference = new CompiledSource("""
                    namespace Checks { public static class Wrappers {
                        public static int ThrowManaged() { throw null; }
                        public static int ManagedCaller() { ThrowManaged(); return 7; }
                        public static int ManagedCallerOut() => 0;
                    } }
                    """);
                // 恢复体导入真实 C# 夹具，核心库引用沿用宿主；对照仍完整校验类型元数据。
                var output = reference.Method("Checks.Wrappers", "ManagedCallerOut");
                output.Body = skeleton.Method(ordinaryCaller.Method).Body;
                var core = reference.Module.TypeSystem.Object.Resolve().Module;
                foreach (var local in output.Body.Variables)
                    local.VariableType = reference.Module.ImportReference(reference.Module.GetType(local.VariableType.FullName) ?? core.GetType(local.VariableType.FullName));
                foreach (var instruction in output.Body.Instructions)
                    if (instruction.Operand is Mono.Cecil.MethodReference invoked)
                        instruction.Operand = reference.Module.ImportReference(reference.Method("Checks.Wrappers", invoked.Name));
                var comparison = CilComparison.Compare(reference.Method("Checks.Wrappers", "ManagedCaller"), output);
                checks.True(comparison.Status == CilComparisonStatus.Match, "普通托管不返回调用与参考 IL 执行一致：" + comparison);
            }
            var stubTerms = new TermTable(); var stubBlock = new BlockIdentity();
            var profile = catalog.Functions.Single(c => c.Operation.Il.Name == "ThrowProfile");
            var stubBuilder = new FunctionBuilder(stubTerms, stubBlock, 64, new(stubTerms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var thrown = new Call(new(), new NamedFunction(profile.MangledName), [], [], DoesNotReturn: true);
            stubBuilder.Blocks.Add(new(stubBlock, [], [thrown], new Unreachable()));
            var stub = stubBuilder.Freeze();
            checks.True(RuntimeThrowStubs.IsStub(stub, ordinaryNaming), "唯一登记的 ThrowProfile 抛出构成替换桩事实");
            var rejected = new IntegerLowering(f.Freeze(), ordinaryCaller, binder, types, calls: ordinaryNaming,
                effects: new ManagedCallEffects(ordinaryNaming), spec: spec,
                runtimeThrowStub: _ => Outcome<bool>.Success(RuntimeThrowStubs.IsStub(stub, ordinaryNaming))).Run();
            checks.True(rejected.Body is null && rejected.Failure?.Reason is { Code: "lowering.CallTermination", Message: var stubMessage }
                && stubMessage.Contains("ThrowProfile", StringComparison.Ordinal), "被调方是替换桩时保留洞并区分原因");
            stubBuilder.Blocks[0] = new(stubBlock, [], [thrown, new MemoryWrite(new(), stubTerms.Atom(new RootAtom(AddressRoot.Image), 64), 64, stubTerms.Constant(1, 64))], new Unreachable());
            checks.True(!RuntimeThrowStubs.IsStub(stubBuilder.Freeze(), ordinaryNaming), "有可观察写入的函数不登记为只有一次抛出的桩");
            stubBuilder.Blocks[0] = new(stubBlock, [], [thrown, new Call(new(), new ImageFunction(40), [], [])], new Unreachable());
            checks.True(!RuntimeThrowStubs.IsStub(stubBuilder.Freeze(), ordinaryNaming), "另有调用事件的函数不登记为替换桩");
            var readId = new ReadIdentity();
            stubBuilder.Blocks[0] = new(stubBlock, [], [new MemoryRead(readId, stubTerms.Atom(new RootAtom(AddressRoot.Frame), 64), 64,
                stubTerms.Atom(new ResultAtom(readId), 64)) { Acquire = true }, thrown], new Unreachable());
            checks.True(!RuntimeThrowStubs.IsStub(stubBuilder.Freeze(), ordinaryNaming), "同步读取的可观察效果不归入替换桩");
        }
        {
            var t = new TermTable(); var block = new BlockIdentity(); var f = new FunctionBuilder(t, block, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
            f.Blocks.Add(new(block, [], [new Call(id, new ImageFunction(40), [], [new(new(SlotKind.Integer), result)])], new Return([new(new(SlotKind.Integer), result)])));
            var naming = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(catalog.Functions[0]), catalog, ambiguous);
            checks.True(state.CreateContext(f.Freeze()).Get(naming, id).Value is { Kind: CallKind.Unknown, Why.Code: "naming.icall-ambiguous" }
                && naming.RuntimeIdentity(new ImageFunction(40)) is null, "内部调用身份歧义不会落回另一条目录托管身份");
        }

        foreach (string scenario in new[] { "Reread", "Result", "OldValue", "OtherWrite", "UnknownWrite", "WrongName" })
        {
            var image = new InternalCallImage(scenario == "WrongName" ? "Checks.Wrappers::Other(System.Int32)" : "Checks.Wrappers::Cached(System.Int32)");
            var t = new TermTable(); var head = new BlockIdentity(); var arm = new BlockIdentity(); var join = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var root = t.Atom(new RootAtom(AddressRoot.Image), 64);
            Term Add(int offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            var f = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = root };
            var slot = new AbstractSlot(SlotKind.Integer); var input = t.Atom(new EntryAtom(slot), 64); f.Inputs.Add(new(slot, input));
            var guardId = new ReadIdentity(); var guard = t.Atom(new ResultAtom(guardId), 64);
            var resolveId = new CallIdentity(); var result = t.Atom(new ResultAtom(resolveId), 64);
            var resolver = catalog.ByName("il2cpp_codegen_resolve_icall").Single();
            var resolve = new Call(resolveId, new NamedFunction(resolver.MangledName), [new(slot, Add(512))], [new(slot, result)]);
            var rereadId = new ReadIdentity(); var reread = t.Atom(new ResultAtom(rereadId), 64);
            var slow = new List<Statement> { resolve, new MemoryWrite(new(), Add(128), 64, result) };
            if (scenario != "Result") slow.Add(new MemoryRead(rereadId, Add(128), 64, reread));
            var mergeId = new MergeIdentity(); var merged = t.Atom(new ResultAtom(mergeId), 64);
            var invokeId = new CallIdentity(); var returned = t.Atom(new ResultAtom(invokeId), 64);
            var invoke = new Call(invokeId, new ComputedTarget(scenario == "OldValue" ? guard : merged), [new(slot, input)], [new(slot, returned)]);
            var tail = new List<Statement>();
            if (scenario is "OtherWrite" or "UnknownWrite") tail.Add(new MemoryWrite(new(), scenario == "OtherWrite" ? Add(128) : input, 64, t.Constant(0, 64)));
            tail.Add(invoke);
            f.Blocks.Add(new(head, [], [new MemoryRead(guardId, Add(128), 64, guard)], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, guard, t.Constant(0, 64)), arm, join)));
            f.Blocks.Add(new(arm, [], [.. slow], new Jump(join)));
            f.Blocks.Add(new(join, [new(mergeId, merged, [new(head, guard), new(arm, scenario == "Result" ? result : reread)])], [.. tail], new Return([new(slot, returned)])));
            var function = f.Freeze(); var cacheState = new StateQueries(image: image);
            var naming = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
            var signature = binder.Entry(cached, BindingEntryKind.Ordinary).Value;
            var names = new ValueNamingQuery(cacheState, naming, NamingFacts.Empty, spec, binder, signature);
            var discovery = new UnobservableEffects(cacheState, naming, names, image, new HashSet<AbstractSlot> { slot }, discoverInternalCall: cached, wrapperEntry: 10).Run(function);
            bool positive = scenario is "Reread" or "Result";
            checks.True(!discovery.InternalCallCaches.IsEmpty == positive, "缓存包装发现正反例：" + scenario + " " + string.Join("；", discovery.Records.Where(r => !r.Removed).Select(r => r.Reason)));
            if (!positive || discovery.InternalCallCaches.IsEmpty) continue;
            var facts = new InternalCallFacts([], discovery.InternalCallCaches);
            var recovered = new UnobservableEffects(cacheState, naming, names, image, new HashSet<AbstractSlot> { slot }, internalCalls: facts).Run(function);
            checks.True(recovered.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().All(c => c.Target == new ImageFunction(10)), "缓存初始化只留下已命名托管调用：" + scenario);
            if (scenario == "Result")
            {
                var head2 = new BlockIdentity(); var arm2 = new BlockIdentity(); var join2 = new BlockIdentity();
                var oldId = new ReadIdentity(); var old = t.Atom(new ResultAtom(oldId), 64);
                var resolve2Id = new CallIdentity(); var resolved2 = t.Atom(new ResultAtom(resolve2Id), 64);
                var merge2Id = new MergeIdentity(); var merged2 = t.Atom(new ResultAtom(merge2Id), 64);
                var invoke2Id = new CallIdentity(); var output2 = t.Atom(new ResultAtom(invoke2Id), 64);
                var chained = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = root };
                chained.Inputs.AddRange(function.Inputs);
                chained.Blocks.AddRange(function.Blocks.Select(b => b.Identity == join ? b with { End = new Jump(head2) } : b));
                chained.Blocks.Add(new(head2, [], [new MemoryRead(oldId, Add(256), 64, old)], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, old, t.Constant(0, 64)), arm2, join2)));
                chained.Blocks.Add(new(arm2, [], [new Call(resolve2Id, new NamedFunction(resolver.MangledName), [new(slot, Add(512))], [new(slot, resolved2)]),
                    new MemoryWrite(new(), Add(256), 64, resolved2)], new Jump(join2)));
                chained.Blocks.Add(new(join2, [new(merge2Id, merged2, [new(head2, old), new(arm2, resolved2)])],
                    [new Call(invoke2Id, new ComputedTarget(merged2), [new(slot, returned)], [new(slot, output2)])], new Return([new(slot, output2)])));
                var twoCaches = new InternalCallFacts([], [discovery.InternalCallCaches[0], (256, discovery.InternalCallCaches[0].Forwarder)]);
                var effects = new UnobservableEffects(cacheState, naming, names, image, new HashSet<AbstractSlot> { slot }, internalCalls: twoCaches);
                var both = effects.Run(chained.Freeze());
                var remainingCalls = both.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().ToArray();
                checks.True(effects.VerifiedInternalCallCaches.Count == 2 && remainingCalls.Length == 2 && remainingCalls.All(c => c.Target == new ImageFunction(10)),
                    "相邻两个缓存守卫的完整快照编辑互不覆盖");
            }

        }
    }
}
