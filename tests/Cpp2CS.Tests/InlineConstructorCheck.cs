using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class InlineConstructorCheck
{
    public class BaseProbe
    {
        public static readonly List<int> Observed = [];
        public static object? Escaped;
        public static bool Fail;
        public BaseProbe()
        {
            Escaped = this;
            Observed.Add((int)GetType().GetField("Value")!.GetValue(this)!);
            if (Fail) throw new InvalidOperationException("base constructor failure");
        }
    }

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        Synthetic(session.Types);
        Native(session);
        return 0;
    }

    public static int Saved(string path)
    {
        using var assembly = AssemblyDefinition.ReadAssembly(path);
        Action<SR.Assembly> execute = assembly.Name.Name == "InlineConstructorChecks" ? Execute : ExecuteNative;
        execute(SR.Assembly.Load(File.ReadAllBytes(path)));
        ObjectAllocationCheck.Source(assembly, execute, "inline-constructor-source-check");
        Console.WriteLine("已保存内联构造程序集的 CIL/C# 往返执行通过");
        return 0;
    }

    private static void Synthetic(ManagedTypes types)
    {
        TypeDef Owner(string name) => new() { Index = -1, Assembly = "InlineConstructorChecks.dll", Namespace = "Checks", Name = name,
            Token = 0, Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false, BaseType = types.Object };
        var parent = Owner("Parent"); var owner = Owner("Constructed"); var factory = Owner("Factory");
        var parentType = new DefinitionRef(parent, []); var ownerType = new DefinitionRef(owner, []); owner.BaseType = parentType;
        MethodRef Method(TypeDef host, string name, TypeRef result, bool isStatic, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = host, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | (isStatic ? SR.MethodAttributes.Static : 0),
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result,
            Parameters = parameters.Select((p, i) => new ParameterDef("p" + i, p, 0, null, false)).ToArray(),
        }, [], []);
        var baseConstructor = Method(parent, ".ctor", types.Void, false);
        var constructor = Method(owner, ".ctor", types.Void, false, types.Object); owner.Methods = [constructor.Method];
        var create = Method(factory, "Create", ownerType, true, types.Object);
        var value = new FieldDef { Index = -1, Owner = owner, Name = "Value", Type = types.Int32, Offset = 16, Attributes = SR.FieldAttributes.Public | SR.FieldAttributes.InitOnly };
        var reference = new FieldDef { Index = -1, Owner = owner, Name = "Reference", Type = types.Object, Offset = 24, Attributes = SR.FieldAttributes.Public | SR.FieldAttributes.InitOnly };
        owner.Fields = [value, reference];
        var self = new ArgumentValue(-1, "this", ownerType, 64);
        var input = new ArgumentValue(0, "input", types.Object, 64);
        var local = new LocalValue(new(Storage.Temp(0), 1), ownerType, 64);
        ManagedStore Store(ManagedValue receiver, FieldDef field, ManagedValue stored) => new(0x1004, new FieldValue(receiver, new(field, ownerType), field.Type, types.Size(field.Type) * 8), stored);
        ManagedCall Base(ManagedValue receiver) => new(0x1008, new(baseConstructor, receiver, []), null, false);
        var constant = new ConstantValue(2000, types.Int32, 32);
        var proof = new ConstructorProof(0x2000, new(constructor, [new(0x2000,
            [Store(self, value, constant), Base(self), Store(self, reference, input), new ManagedReturn(0x2010, null)])]));
        var allocation = new ManagedAssignment(0x1000, local, new ObjectAllocationValue(ownerType));
        var write = Store(local, value, constant); var initialize = Base(local); var copy = Store(local, reference, input);
        var returned = new ManagedReturn(0x1010, local);
        ManagedBody Body(params ManagedStatement[] statements) => new(create, [new(0x1000, statements)]);
        var source = Body(allocation, write, initialize, copy, returned);
        var matched = InlineConstructors.Match(types, source, 0, 0, proof);
        Require(matched is not null && matched.Constructors.Single() == proof, "匹配完整构造片段并保存真实实现依赖");
        var recovered = ObjectConstruction.Recover(matched!);
        Require(recovered.Blocks[0].Statements is [ManagedAssignment { Value: NewObjectValue }, ManagedReturn], "完整片段合并为同类型构造");
        Require(InlineConstructors.Match(types, Body(allocation, write with { Value = new ConstantValue(1999, types.Int32, 32) }, initialize, copy, returned), 0, 0, proof) is null,
            "字段值不同不能匹配");
        Require(InlineConstructors.Match(types, Body(allocation, initialize, write, copy, returned), 0, 0, proof) is null, "字段写入与基类调用顺序不同不能匹配");
        Require(InlineConstructors.Match(types, Body(allocation, write, initialize, returned), 0, 0, proof) is null, "不能省去构造后半段");
        Require(InlineConstructors.Match(types, Body(allocation, write, write, initialize, copy, returned), 0, 0, proof) is null, "不能跨过额外副作用");
        var readInput = new FieldValue(new ArgumentValue(0, "input", ownerType, 64), new(reference, ownerType), types.Object, 64);
        var lateRead = Body(allocation, write, initialize, copy with { Value = readInput }, returned) with { Method = Method(factory, "LateRead", ownerType, true, ownerType) };
        Require(InlineConstructors.Match(types, lateRead, 0, 0, proof) is null, "构造后读取的字段不能提前为调用参数");
        var slot = new LocalValue(new(Storage.Temp(1), 1), types.Object, 64);
        var remember = Method(factory, "Remember", types.Void, true, new ByRefRef(types.Object));
        var addressed = Body(new ManagedAssignment(0x900, slot, input), new ManagedCall(0x904, new(remember, null, [new AddressValue(slot, new ByRefRef(types.Object))]), null, false),
            allocation, write, initialize, copy with { Value = slot }, returned);
        Require(InlineConstructors.Match(types, addressed, 0, 2, proof) is null, "被取地址的局部不能提前复制为构造参数");
        var expectedTemp = new LocalValue(new(Storage.Temp(2), 1), types.Int32, 32); var actualTemp = new LocalValue(new(Storage.Temp(3), 1), types.Int32, 32);
        var privateProof = proof with { Body = proof.Body with { Blocks = [new(0x2000,
            [Store(self, value, constant), new ManagedAssignment(0x2004, expectedTemp, new FieldValue(self, new(value, ownerType), types.Int32, 32)), Base(self), Store(self, reference, input), new ManagedReturn(0x2010, null)])] } };
        var consume = Method(factory, "Consume", types.Void, true, types.Int32);
        var escapingTemp = Body(allocation, write, new ManagedAssignment(0x1006, actualTemp, new FieldValue(local, new(value, ownerType), types.Int32, 32)), initialize, copy,
            new ManagedCall(0x100e, new(consume, null, [actualTemp]), null, false), returned);
        Require(InlineConstructors.Match(types, escapingTemp, 0, 0, privateProof) is null, "片段局部仍被外部使用时不得提取为构造调用");
        var unused = Method(owner, ".ctor", types.Void, false, types.Object, types.Int32);
        Require(InlineConstructors.Match(types, source, 0, 0, proof with { Body = proof.Body with { Method = unused } }) is null, "不能猜测未使用构造参数");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("InlineConstructorChecks", new Version(1, 0)), "InlineConstructorChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Constructed", TypeAttributes.Public, module.ImportReference(typeof(BaseProbe))); module.Types.Add(host);
        var harness = new TypeDefinition("Checks", "Factory", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(harness);
        var fields = new Dictionary<FieldDef, FieldReference>();
        foreach (var field in owner.Fields)
        {
            var actual = new FieldDefinition(field.Name, FieldAttributes.Public | FieldAttributes.InitOnly, field.Type == types.Int32 ? module.TypeSystem.Int32 : module.TypeSystem.Object);
            host.Fields.Add(actual); fields.Add(field, actual);
        }
        var ctor = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
        ctor.Parameters.Add(new ParameterDefinition(module.TypeSystem.Object)); host.Methods.Add(ctor);
        var method = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static, host); method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Object)); harness.Methods.Add(method);
        TypeReference Reference(TypeRef type) => type == ownerType ? host : type == parentType ? module.ImportReference(typeof(BaseProbe))
            : type == types.Object ? module.TypeSystem.Object : type == types.Int32 ? module.TypeSystem.Int32 : ManagedTypes.IsVoid(type) ? module.TypeSystem.Void
            : throw new NotSupportedException(type.ToString());
        var emitter = new BodyEmitter(types, Reference, f => fields[f.Field], m => m == constructor ? ctor : m == baseConstructor
            ? module.ImportReference(typeof(BaseProbe).GetConstructor(Type.EmptyTypes)) : throw new NotSupportedException(m.ToString()));
        var problem = emitter.Emit(proof.Body, ctor); Require(problem is null, problem ?? "真实证明体输出");
        problem = emitter.Emit(recovered, method); Require(problem is null, problem ?? "合并调用输出");
        using var stream = new MemoryStream(); assembly.Write(stream); Execute(SR.Assembly.Load(stream.ToArray()));
        ObjectAllocationCheck.Source(assembly, Execute, "inline-constructor-source-check");
        Console.WriteLine("内联构造 CIL/C# 执行通过：只读字段先写、基类观察、参数引用身份、构造失败与对象逃逸；完整片段和反例检查通过");
    }

    private static void Execute(SR.Assembly assembly)
    {
        BaseProbe.Fail = false; BaseProbe.Observed.Clear(); BaseProbe.Escaped = null;
        var create = assembly.GetType("Checks.Factory", true)!.GetMethod("Create")!;
        foreach (var input in new object?[] { null, new object(), "共享引用" })
        {
            var value = create.Invoke(null, [input])!;
            Require((int)value.GetType().GetField("Value")!.GetValue(value)! == 2000 && ReferenceEquals(value.GetType().GetField("Reference")!.GetValue(value), input),
                "默认字段和引用参数保持");
            Require(ReferenceEquals(BaseProbe.Escaped, value), "基类看到的对象仍是返回对象");
        }
        Require(BaseProbe.Observed.SequenceEqual([2000, 2000, 2000]), "字段初始化发生在基类构造之前");
        BaseProbe.Fail = true;
        var failed = Task.Run(() => create.Invoke(null, [new object()])); Task.WhenAny(failed).GetAwaiter().GetResult();
        Require(failed.Exception?.InnerException is SR.TargetInvocationException { InnerException: InvalidOperationException }
            && BaseProbe.Observed.SequenceEqual([2000, 2000, 2000, 2000])
            && BaseProbe.Escaped!.GetType().GetField("Reference")!.GetValue(BaseProbe.Escaped) is null, "失败时不执行剩余字段赋值，已逃逸对象保留");
        BaseProbe.Fail = false;
    }

    private static void Native(RecoverySession session)
    {
        var types = session.Types;
        var source = session.Model.Code[0x55d246c].Single().Method;
        Require(source.ToString() == "Sekai.Mysekai.DebugAddedFixtureListDialog.<>c..cctor", "真实静态构造身份");
        var recovered = BodyRecovery.Recover(session, session.Analyze(source, source.Method.Address)); Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
        var proof = recovered.Body!.Constructors.Single(); Require(proof.Address == 0x55d24d4, "闭包实例构造的真实完整实现");
        Require(recovered.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Any(a => a.Value is NewObjectValue), "本类静态初始化期间可以合并本类分配");
        var storage = source.Method.Owner.Fields.Single(f => f.IsStatic && f.Type == source.DeclaringType);
        var queue = session.Model.Code[0xa45dad0].Single().Method;
        var queueProof = session.Constructors.Prove(queue); Require(queueProof is not null, "真实默认字段构造可以完整证明");
        var outer = session.Model.Code[0xa45d4c8].Single().Method;
        var outerBody = BodyRecovery.Recover(session, session.Analyze(outer, outer.Method.Address));
        Require(outerBody.Body is not null && outerBody.Body.Constructors.Any(p => p.Body.Method == queue), "真实 MaterialRenderingSettings 方法匹配内联字段和基类调用");
        var queueField = queue.Method.Owner.Fields.Single(f => !f.IsStatic && f.Name == "renderQueue");
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeInlineConstructorChecks", new Version(1, 0)), "NativeInlineConstructorChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Singleton", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(host);
        var queueHost = new TypeDefinition("Checks", "Queue", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(queueHost);
        var actualStorage = new FieldDefinition("Instance", FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.InitOnly, host); host.Fields.Add(actualStorage);
        var actualQueueField = new FieldDefinition("renderQueue", FieldAttributes.Public, module.TypeSystem.Int32); queueHost.Fields.Add(actualQueueField);
        MethodDefinition Constructor(TypeDefinition owner, bool isStatic) => new(isStatic ? ".cctor" : ".ctor",
            (isStatic ? MethodAttributes.Private | MethodAttributes.Static : MethodAttributes.Public) | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
        var ctor = Constructor(host, false); host.Methods.Add(ctor); var cctor = Constructor(host, true); host.Methods.Add(cctor);
        var queueCtor = Constructor(queueHost, false); queueHost.Methods.Add(queueCtor);
        TypeReference Reference(TypeRef type) => type == source.DeclaringType ? host : type == queue.DeclaringType ? queueHost
            : type == types.Int32 ? module.TypeSystem.Int32 : type == types.Object ? module.TypeSystem.Object : ManagedTypes.IsVoid(type) ? module.TypeSystem.Void
            : throw new NotSupportedException(type.ToString());
        var emitter = new BodyEmitter(types, Reference, f => f.Field == storage ? actualStorage : f.Field == queueField ? actualQueueField : throw new NotSupportedException(f.ToString()),
            m => m == proof.Body.Method ? ctor : m.Method.Owner == types.Object.Definition && m.Method.Name == ".ctor"
                ? module.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)) : throw new NotSupportedException(m.ToString()));
        foreach (var (body, method) in new[] { (proof.Body, ctor), (recovered.Body, cctor), (queueProof!.Body, queueCtor) })
        {
            var problem = emitter.Emit(body, method); Require(problem is null, problem ?? body.Method.ToString());
        }
        using var stream = new MemoryStream(); assembly.Write(stream); ExecuteNative(SR.Assembly.Load(stream.ToArray()));
        ObjectAllocationCheck.Source(assembly, ExecuteNative, "inline-constructor-source-check");
        Console.WriteLine("真实闭包 .cctor 0x55d246c 与构造 0x55d24d4、MaterialRenderQueueSettings..ctor 0xa45dad0：CIL/C# 执行通过；完整外层方法 0xa45d4c8 的内联片段已匹配，外层尚未运行");
    }

    private static void ExecuteNative(SR.Assembly assembly)
    {
        var singleton = assembly.GetType("Checks.Singleton", true)!;
        var instance = singleton.GetField("Instance")!;
        var first = instance.GetValue(null);
        Require(first is not null && first.GetType() == singleton && ReferenceEquals(first, instance.GetValue(null)), "本类静态构造不递归初始化并保存单一实例");
        var queue = assembly.GetType("Checks.Queue", true)!; var value = Activator.CreateInstance(queue)!;
        Require((int)queue.GetField("renderQueue")!.GetValue(value)! == 2000, "真实原生默认队列值保持");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
