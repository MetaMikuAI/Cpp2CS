using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Pipeline;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private sealed class ContextDecoder(MethodRef owner, bool methodContext, TypeRef parameter, MethodRef target) : IRgctxDecoder
    {
        public Outcome<MetadataEntity> Decode(DefinitionRef type, int index) => type == owner.DeclaringType
            ? Decode(owner, false, index) : Outcome<MetadataEntity>.Failure(new("naming.rgctx-scope", "类型不属于当前上下文"));
        public Outcome<MetadataEntity> Decode(MethodRef definition, bool method, int index)
        {
            MetadataEntity? entity = definition != owner || method != methodContext ? null : index switch
            { 0 => new ClassEntity(new ArrayRef(parameter, 1)), 1 => new MethodEntity(target), 2 => new TypeEntity(parameter), _ => null };
            return entity is null ? Outcome<MetadataEntity>.Failure(new("naming.rgctx-index", "没有对应的上下文项")) : Outcome<MetadataEntity>.Success(entity);
        }
    }

    private static void GenericContextChecks(Assertions checks, ProgramModel program, MethodDef[] methods, MethodBinder binder, ITypeLayouts layouts, RuntimeSpec spec)
    {
        NamedGenericContextChecks(checks, program, methods, binder, layouts, spec);
        var obj = new DefinitionRef(program.Types.Single(t => t.FullName == "System.Object"), []);
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        using var assemblies = new ContextAssemblies(new Skeleton(program, 16));
        var emitter = new BodyEmitter(assemblies.Skeleton, new(program, layouts, 8));
        foreach (bool methodContext in new[] { false, true })
        {
            var definition = MethodRef.Open(methods[methodContext ? 8 : 0]);
            var instance = new MethodRef(definition.Method, [obj], methodContext ? [obj] : []);
            var witness = new GenericWitness(definition, instance, layouts);
            var parameter = definition.Concrete(definition.Method.Parameters[0].Type);
            var target = methodContext ? new MethodRef(methods[0], [parameter], []) : new MethodRef(methods[8], definition.TypeArguments, [parameter]);
            var canonical = witness.Close(target);
            var decoder = new ContextDecoder(definition, methodContext, parameter, target);
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(canonical, BindingEntryKind.SharedGeneric)]), new NamingChecks.RuntimeMap(), catalog);
            var terms = new TermTable(); var block = new BlockIdentity();
            var builder = new FunctionBuilder(terms, block, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var argument = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var information = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            builder.Inputs.Add(new(new(SlotKind.Integer), argument)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), information));
            var statements = new List<Statement>();
            Term Read(Term root, long offset)
            {
                var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new MemoryRead(id, terms.Apply(new CoreOperator(CoreOperation.Add), 64, root, terms.Constant(offset, 64)), 64, value));
                return value;
            }
            var owner = methodContext ? information : Read(information, spec.Layout.Field("MethodInfo", "klass").ByteOffset);
            var table = Read(owner, spec.Layout.Field(methodContext ? "MethodInfo" : "Il2CppClass", "rgctx_data").ByteOffset);
            long size = spec.Layout.Record("Il2CppRGCTXData").Size;
            var klass = Read(table, 0); var called = Read(table, size); var type = Read(table, size * 2); var absent = Read(table, size * 3);
            var callId = new CallIdentity(); var result = terms.Atom(new ResultAtom(callId), 64);
            statements.Add(new Call(callId, new ImageFunction(10), [new(new(SlotKind.Integer), argument), new(new(SlotKind.Integer, 1), called)], [new(new(SlotKind.Integer), result)]));
            builder.Blocks.Add(new(block, [], [.. statements], new Return([new(new(SlotKind.Integer), result)])));
            var function = builder.Freeze(); var state = new StateQueries();
            var names = new ValueNamingQuery(state, calls, NamingFacts.Empty, spec, binder, binder.Definition(definition, BindingEntryKind.SharedGeneric, instance).Value, decoder, witness);
            var locations = new ManagedLocationQuery(state, names, witness, spec); var context = locations.CreateContext(function);
            checks.True(context.Get(names, klass).Value.Name is EntityName { Entity: ClassEntity { Type: ArrayRef array } } && array.Element == parameter,
                "RGCTXData 类项保留定义的类型参数：" + methodContext);
            checks.True(context.Get(names, type).Value.Name is EntityName { Entity: TypeEntity typeEntity } && typeEntity.Type == parameter,
                "RGCTXData 类型项保留定义的类型参数：" + methodContext);
            checks.True(context.Get(names, absent).Value.Kind == ValueKind.Unnamed, "RGCTXData 越界项不猜实体：" + methodContext);
            var shared = context.Get(new SharedCallQuery(binder, calls, names, new(state)), callId);
            checks.True(shared.IsSuccess && shared.Value.Method == target, "开放方法信息以封闭见证核对共享签名：" + shared.Why);
            checks.True(context.Get(names, result).Value.StaticType == parameter, "共享调用结果命名保留开放返回类型");
            var lowered = new IntegerLowering(function, definition, binder, new(program, witness, 8), calls: calls, spec: spec, witness: instance, rgctx: decoder).Run(BindingEntryKind.SharedGeneric);
            checks.True(lowered.Body is not null, "开放共享调用下降：" + lowered.Failure);
            if (lowered.Body is { } body)
            {
                checks.True(emitter.Emit([body]).Count == 0, "开放共享调用通过 CIL 校验");
                checks.True(assemblies.Skeleton.Method(definition.Method).Body.Instructions.Select(i => i.Operand).OfType<Mono.Cecil.MethodReference>()
                    .Any(m => m.ContainsGenericParameter), "共享调用 IL 目标保留类型参数");
            }
            if (methodContext)
            {
                var initialize = catalog.Functions.First(f => f.Name == "il2cpp_rgctx_method_init" && f.Signature is not null);
                var initCalls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(initialize), catalog);
                var head = new BlockIdentity(); var slow = new BlockIdentity(); var join = new BlockIdentity();
                var guarded = new FunctionBuilder(terms, head, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
                guarded.Inputs.AddRange(builder.Inputs);
                var readId = new ReadIdentity(); var rgctxValue = terms.Atom(new ResultAtom(readId), 64);
                var address = terms.Apply(new CoreOperator(CoreOperation.Add), 64, information, terms.Constant(spec.Layout.Field("MethodInfo", "rgctx_data").ByteOffset, 64));
                guarded.Blocks.Add(new(head, [], [new MemoryRead(readId, address, 64, rgctxValue)],
                    new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1, rgctxValue, terms.Constant(0, 64)), slow, join)));
                guarded.Blocks.Add(new(slow, [], [new Call(new(), new ImageFunction(20), [new(new(SlotKind.Integer), information)], [])], new Jump(join)));
                guarded.Blocks.Add(new(join, [], [], new Return([new(new(SlotKind.Integer), argument)])));
                var memory = new StateQueries();
                var initNames = new ValueNamingQuery(memory, initCalls, NamingFacts.Empty, spec, binder,
                    binder.Definition(definition, BindingEntryKind.SharedGeneric, instance).Value, decoder, witness);
                var transformed = new UnobservableEffects(memory, initCalls, initNames, new InputMemoryImage(),
                    new HashSet<AbstractSlot> { new(SlotKind.Integer) }).Run(guarded.Freeze());
                checks.True(!transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any()
                    && transformed.Function.Blocks.All(b => b.End is not Branch), "方法 RGCTX 惰性初始化及其私有守卫消去");
            }
            var foreign = target with { TypeArguments = [new GenericParameterRef("Foreign", true, 0)] };
            checks.True(!witness.Knows(foreign), "开放见证拒绝本定义之外的类型参数");
        }
    }

    private sealed class ContextAssemblies(Skeleton skeleton) : IDisposable
    {
        public Skeleton Skeleton => skeleton;
        public void Dispose() { foreach (var assembly in skeleton.Assemblies) assembly.Dispose(); }
    }
}

internal static partial class LoweringChecks
{
    private sealed class ContextRuntimeMap(RuntimeFunction initialize, RuntimeFunction ready) : IRuntimeFunctionMap
    {
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 20 } ? initialize : ready;
    }

    private static void NamedGenericContextChecks(Assertions checks, ProgramModel program, MethodDef[] methods, MethodBinder binder, ITypeLayouts layouts, RuntimeSpec spec)
    {
        TypeRef Type(string name) => new DefinitionRef(program.Types.Single(t => t.FullName == "System." + name), []);
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var initialize = catalog.Functions.First(f => f.Operation.Name == "InitializeMethodRgctx" && f.Signature is not null);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(initialize), catalog);
        foreach (bool methodContext in new[] { true, false })
        {
            var open = MethodRef.Open(methods[methodContext ? 8 : 9]);
            var method = new MethodRef(open.Method, [Type("Int32")], methodContext ? [Type("String")] : []);
            var parameter = methodContext ? open.MethodArguments[0] : open.TypeArguments[0];
            var concrete = methodContext ? Type("String") : Type("Int32");
            var target = new MethodRef(methods[0], [parameter], []);
            var map = new Registrations
            {
                CodeRegistration = 0, MetadataRegistration = 0, Entries = [], ByAddress = new Dictionary<ulong, ImmutableArray<CodeEntry>>(),
                Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>
                {
                    [(open.Method.Owner.Assembly, methodContext ? open.Method.Token : open.Method.Owner.Token)] =
                        [new(RgctxKind.Class, new ArrayRef(parameter, 1)), new(RgctxKind.Type, parameter),
                         new(RgctxKind.Method, target), new(RgctxKind.Constrained, null)],
                },
                MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>(),
            };
            var decoder = new MetadataRgctxDecoder(new(new InputMemoryImage(), program, map, spec, "arm64"));
            var terms = new TermTable(); var head = new BlockIdentity();
            var image = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var builder = new FunctionBuilder(terms, head, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64))) { ImageBase = image };
            var statements = new List<Statement>();
            Term Read(Term root, long offset)
            {
                var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new MemoryRead(id, terms.Apply(new CoreOperator(CoreOperation.Add), 64, root, terms.Constant(offset, 64)), 64, value));
                return value;
            }
            var information = Read(image, 128);
            var owner = methodContext ? information : Read(information, spec.Layout.Field("MethodInfo", "klass").ByteOffset);
            var table = Read(owner, spec.Layout.Field(methodContext ? "MethodInfo" : "Il2CppClass", "rgctx_data").ByteOffset);
            long size = spec.Layout.Record("Il2CppRGCTXData").Size;
            var klass = Read(table, 0); var type = Read(table, size); var called = Read(table, size * 2);
            var unsupported = Read(table, size * 3); var absent = Read(table, size * 4);
            builder.Blocks.Add(new(head, [], [.. statements], new Return([])));
            var evidence = NamingFacts.Empty with { Slots = NamingFacts.Empty.Slots.Add(128, Outcome<MetadataEntity>.Success(new MethodEntity(method))) };
            var state = new StateQueries();
            var names = new ValueNamingQuery(state, calls, evidence, spec, binder, rgctx: decoder);
            var c = names.CreateContext(builder.Freeze());
            checks.True(c.Get(names, klass).Value.Name is EntityName { Entity: ClassEntity { Type: ArrayRef array } } && array.Element == concrete,
                "常量方法实体的上下文类项封闭：" + methodContext);
            checks.True(c.Get(names, type).Value.Name is EntityName { Entity: TypeEntity typeEntity } && typeEntity.Type == concrete,
                "常量方法实体的上下文类型项封闭：" + methodContext);
            checks.True(c.Get(names, called).Value.Name is EntityName { Entity: MethodEntity entity } && entity.Method == target with { TypeArguments = [concrete] },
                "常量方法实体的上下文方法项封闭：" + methodContext);
            checks.True(c.Get(names, unsupported).Value is { Kind: ValueKind.Unnamed, Why.Code: "naming.rgctx-kind" }, "不支持的上下文条目保留原因");
            checks.True(c.Get(names, absent).Value is { Kind: ValueKind.Unnamed, Why.Code: "naming.rgctx-index" }, "常量上下文越界保留原因");
            {
                var ensure = catalog.Functions.First(f => f.Operation.Name == "EnsureClassReady" && f.Signature is { ReturnType.Size: > 0 });
                var readyCalls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(ensure), catalog);
                var id = new CallIdentity(); var returned = terms.Atom(new ResultAtom(id), 64);
                var ready = new FunctionBuilder(terms, head, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64))) { ImageBase = image };
                ready.Blocks.Add(new(head, [], [.. statements, new Call(id, new ImageFunction(30), [new(new(SlotKind.Integer), klass)], [new(new(SlotKind.Integer), returned)])],
                    new Return([new(new(SlotKind.Integer), returned)])));
                var memory = new StateQueries(); var readyNames = new ValueNamingQuery(memory, readyCalls, evidence, spec, binder, rgctx: decoder);
                checks.True(readyNames.CreateContext(ready.Freeze()).Get(readyNames, klass).Value.Name is EntityName { Entity: ClassEntity },
                    "类初始化实参的种类不覆盖上下文解出的实体");
                var transformed = new UnobservableEffects(memory, readyCalls, readyNames, new InputMemoryImage(), new HashSet<AbstractSlot> { new(SlotKind.Integer) }).Run(ready.Freeze());
                checks.True(!transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any()
                    && transformed.Function.Blocks.Select(b => b.End).OfType<Return>().Single().Results.Single().Value == klass,
                    "上下文解出的封闭类消去布局初始化并保留同一类结果");
            }
            var foreign = method with { TypeArguments = [new GenericParameterRef("Foreign", true, 0)] };
            var foreignNames = new ValueNamingQuery(new(), calls, evidence with { Slots = evidence.Slots.SetItem(128, Outcome<MetadataEntity>.Success(new MethodEntity(foreign))) }, spec, binder, rgctx: decoder);
            checks.True(foreignNames.CreateContext(builder.Freeze()).Get(foreignNames, klass).Value.Kind == ValueKind.Unnamed, "无见证的开放实体不解码");
            var witnessed = new GenericWitness(open, new(open.Method, [Type("Object")], methodContext ? [Type("Object")] : []), layouts);
            var openNames = new ValueNamingQuery(new(), calls, evidence with { Slots = evidence.Slots.SetItem(128, Outcome<MetadataEntity>.Success(new MethodEntity(open))) }, spec, binder, rgctx: decoder, witness: witnessed);
            checks.True(openNames.CreateContext(builder.Freeze()).Get(openNames, klass).Value.Name is EntityName { Entity: ClassEntity { Type: ArrayRef openArray } }
                && openArray.Element == parameter, "已命名的开放实体沿用当前定义的参数");
            if (!methodContext) continue;
            {
                var id = new CallIdentity(); var returned = terms.Atom(new ResultAtom(id), 64);
                var direct = new FunctionBuilder(terms, head, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64))) { ImageBase = image };
                direct.Blocks.Add(new(head, [], [statements[0], new Call(id, new ImageFunction(20), [new(new(SlotKind.Integer), information)], [new(new(SlotKind.Integer), returned)])],
                    new Return([new(new(SlotKind.Integer), returned)])));
                var returning = catalog.Functions.First(f => f.Operation.Name == "InitializeMethodRgctx" && f.Signature is { ReturnType.Size: > 0 });
                var directCalls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(returning), catalog);
                var memory = new StateQueries(); var initNames = new ValueNamingQuery(memory, directCalls, evidence, spec, binder, rgctx: decoder);
                var transformed = new UnobservableEffects(memory, directCalls, initNames, new InputMemoryImage(), new HashSet<AbstractSlot> { new(SlotKind.Integer) }).Run(direct.Freeze());
                checks.True(!transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any()
                    && transformed.Function.Blocks.Select(b => b.End).OfType<Return>().Single().Results.Single().Value == information,
                    "常量方法初始化的实际结果替换为同一方法信息");
            }
            {
                var ensure = catalog.Functions.First(f => f.Operation.Name == "EnsureClassReady" && f.Signature is { ReturnType.Size: > 0 });
                var stagedCalls = new CallNamingQuery(binder, new NamingChecks.Map([]), new ContextRuntimeMap(initialize, ensure), catalog);
                var slow = new BlockIdentity(); var join = new BlockIdentity();
                var staged = new FunctionBuilder(terms, head, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64))) { ImageBase = image };
                var tableId = new ReadIdentity(); var slowTable = terms.Atom(new ResultAtom(tableId), 64);
                var merge = new MergeIdentity(); var merged = terms.Atom(new ResultAtom(merge), 64);
                var classId = new ReadIdentity(); var afterClass = terms.Atom(new ResultAtom(classId), 64);
                var callId = new CallIdentity(); var returned = terms.Atom(new ResultAtom(callId), 64);
                staged.Blocks.Add(new(head, [], [.. statements.Take(2)],
                    new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1, table, terms.Constant(0, 64)), slow, join)));
                staged.Blocks.Add(new(slow, [], [new Call(new(), new ImageFunction(20), [new(new(SlotKind.Integer), information)], []),
                    new MemoryRead(tableId, ((MemoryRead)statements[1]).Address, 64, slowTable)], new Jump(join)));
                staged.Blocks.Add(new(join, [new Merge(merge, merged, [new(head, table), new(slow, slowTable)])],
                    [new MemoryRead(classId, merged, 64, afterClass), new Call(callId, new ImageFunction(30), [new(new(SlotKind.Integer), afterClass)], [new(new(SlotKind.Integer), returned)])],
                    new Return([new(new(SlotKind.Integer), returned)])));
                var memory = new StateQueries(); var stagedNames = new ValueNamingQuery(memory, stagedCalls, evidence, spec, binder, rgctx: decoder);
                var effects = new UnobservableEffects(memory, stagedCalls, stagedNames, new InputMemoryImage(), new HashSet<AbstractSlot> { new(SlotKind.Integer) });
                var transformed = effects.Run(staged.Freeze());
                checks.True(!transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any()
                    , "方法初始化消去后解出的类继续消去布局初始化：" + string.Join("；", transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
                        .Select(call => stagedNames.CreateContext(transformed.Function).Get(stagedCalls, call.Identity).Value.Operation?.Name)));
                checks.True(transformed.Function.Blocks.All(b => b.End is not Branch)
                    && transformed.Records.Any(r => r.Kind == "init-guard" && r.Removed)
                    && !transformed.Records.Any(r => r.Reason?.Code == "structure.init-guard.read-used" && !r.Removed),
                    "快路径复用守卫读取、慢路径同位置重读的合流随删边消去");
                checks.True(ReferenceEquals(effects.Run(transformed.Function).Function, transformed.Function), "不可观察效果消去在当前快照上收敛");
            }
            foreach (bool named in new[] { true, false })
            foreach (bool joined in new[] { true, false })
            {
                var slow = new BlockIdentity(); var join = new BlockIdentity(); var other = new BlockIdentity();
                var guarded = new FunctionBuilder(terms, head, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64))) { ImageBase = image };
                guarded.Blocks.Add(new(head, [], [.. statements.Take(2)],
                    new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1, table, terms.Constant(0, 64)), slow, join)));
                guarded.Blocks.Add(new(slow, [], [new Call(new(), new ImageFunction(20), [new(new(SlotKind.Integer), information)], [])], new Jump(joined ? join : other)));
                guarded.Blocks.Add(new(join, [], [], new Return([new(new(SlotKind.Integer), terms.Constant(7, 32))])));
                if (!joined) guarded.Blocks.Add(new(other, [], [], new Return([new(new(SlotKind.Integer), terms.Constant(8, 32))])));
                var memory = new StateQueries();
                var initNames = new ValueNamingQuery(memory, calls, named ? evidence : NamingFacts.Empty, spec, binder, rgctx: decoder);
                var transformed = new UnobservableEffects(memory, calls, initNames, new InputMemoryImage(), new HashSet<AbstractSlot> { new(SlotKind.Integer) }).Run(guarded.Freeze());
                checks.True(transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any() != named, "仅已命名实体消去初始化");
                checks.True(transformed.Function.Blocks.Any(b => b.End is Branch) != named, "已命名方法的直接汇合及不汇合守卫共用改写");
                var caller = new MethodDef { Index = -1, Owner = program.Types.Single(t => t.FullName == "System.Object"), Name = "ContextGuard", Token = 0x0600ffff,
                    Attributes = System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, ReturnType = Type("Int32"), ImplAttributes = 0, Slot = -1 };
                var lowered = new IntegerLowering(transformed.Function, MethodRef.Open(caller), binder, new(program, layouts, 8), calls: calls, spec: spec, names: named ? evidence : NamingFacts.Empty, rgctx: decoder).Run();
                checks.True((lowered.Body is not null) == named, "已命名方法守卫改写后可下降；未命名方法信息保留洞：" + lowered.Failure);
            }
        }
    }
}
