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
        public Outcome<MetadataEntity> Decode(MethodRef definition, bool method, int index)
        {
            MetadataEntity? entity = definition != owner || method != methodContext ? null : index switch
            { 0 => new ClassEntity(new ArrayRef(parameter, 1)), 1 => new MethodEntity(target), 2 => new TypeEntity(parameter), _ => null };
            return entity is null ? Outcome<MetadataEntity>.Failure(new("naming.rgctx-index", "没有对应的上下文项")) : Outcome<MetadataEntity>.Success(entity);
        }
    }

    private static void GenericContextChecks(Assertions checks, ProgramModel program, MethodDef[] methods, MethodBinder binder, ITypeLayouts layouts, RuntimeSpec spec)
    {
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
