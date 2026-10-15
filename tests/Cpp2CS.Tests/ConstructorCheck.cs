using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class ConstructorCheck
{
    public class BaseProbe
    {
        public static int Calls;
        public static readonly List<int?> Observed = [];
        public BaseProbe()
        {
            Calls++;
            Observed.Add(GetType().GetField("Value") is { } field ? (int)field.GetValue(this)! : null);
        }
    }

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        TypeDef Type(string name) => new() { Index = -1, Assembly = "ConstructorChecks.dll", Namespace = "Checks", Name = name,
            Token = 0, Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var parent = Type("Base"); var owner = Type("Harness");
        var parentRef = new DefinitionRef(parent, []); var ownerRef = new DefinitionRef(owner, []);
        owner.BaseType = parentRef;
        MethodRef Method(TypeDef host, string name, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = host, Name = name, Token = 0, Slot = -1, Attributes = host == parent ? SR.MethodAttributes.Family : SR.MethodAttributes.Public,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = types.Void,
            Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
        }, [], []);
        var baseConstructor = Method(parent, ".ctor");
        var constructor = Method(owner, ".ctor", types.Boolean);
        var field = new FieldDef { Index = -1, Owner = owner, Name = "Value", Type = types.Int32, Offset = 16, Token = 0, Attributes = SR.FieldAttributes.Public };
        var self = new ArgumentValue(-1, "this", ownerRef, 64);
        var alias = new LocalValue(new Variable(Storage.Temp(0), 1), ownerRef, 64);
        var location = new FieldValue(self, new FieldRef(field, ownerRef), types.Int32, 32);
        var returned = new ManagedReturn(0x4000, null);
        ManagedCall Initialize(ManagedValue? receiver = null) => new(0x2000, new(baseConstructor, receiver ?? self, []), null, false);
        ManagedStore Store(int value) => new(0x1004, location, new ConstantValue((ulong)value, types.Int32, 32));
        ManagedJump Jump(ulong target) => new(0x1000, new(target, []));
        ManagedBody Body(params ManagedStatement[] statements) => new(constructor, [new ManagedBlock(0x1000, statements)]);
        Require(ConstructorInitialization.Check(Body(Initialize(), returned)) is null, "直接基类初始化");
        Require(ConstructorInitialization.Check(Body(Store(3), Initialize(), returned)) is null, "本类字段可以先初始化");
        Require(ConstructorInitialization.Check(Body(new ManagedAssignment(0x1000, alias, self), Initialize(alias), returned)) is null, "this 的局部副本");
        Require(ConstructorInitialization.Check(Body(returned)) is not null, "缺少基类初始化");
        Require(ConstructorInitialization.Check(Body(Initialize(), Initialize(), returned)) is not null, "重复初始化");
        Require(ConstructorInitialization.Check(Body(new ManagedAssignment(0x1000, new(new Variable(Storage.Temp(1), 1), types.Int32, 32), location), Initialize(), returned)) is not null,
            "初始化前读取 this 字段");
        var sink = Method(parent, "Sink", ownerRef);
        Require(ConstructorInitialization.Check(Body(new ManagedCall(0x1000, new(sink, null, [self]), null, false), Initialize(), returned)) is not null,
            "初始化前 this 逃逸到调用参数");
        Require(ConstructorInitialization.Check(Body(new ManagedCall(0x1000, new(baseConstructor, self, [self]), null, false), returned)) is not null,
            "基类调用参数不能使用未初始化 this");
        var inherited = new FieldValue(self, new FieldRef(new FieldDef { Index = -1, Owner = parent, Name = "BaseValue", Type = types.Int32,
            Offset = 16, Token = 0, Attributes = SR.FieldAttributes.Public }, parentRef), types.Int32, 32);
        Require(ConstructorInitialization.Check(Body(new ManagedStore(0x1000, inherited, new ConstantValue(0, types.Int32, 32)), Initialize(), returned)) is not null,
            "初始化前不得写基类字段");
        var both = new ManagedBody(constructor,
        [
            new(0x1000, [new ManagedBranch(0x1000, new ArgumentValue(0, "choose", types.Boolean, 1), new(0x2000, []), new(0x3000, []))]),
            new(0x2000, [Store(3), Initialize(), Jump(0x4000)]),
            new(0x3000, [Initialize(), Store(4), Jump(0x4000)]),
            new(0x4000, [returned]),
        ]);
        Require(ConstructorInitialization.Check(both) is null, "每条路径分别初始化一次");
        Require(ConstructorInitialization.Check(both with { Blocks = [both.Blocks[0], both.Blocks[1], new(0x3000, [Jump(0x4000)]), both.Blocks[3]] }) is not null,
            "单条已初始化路径不能掩盖另一条路径");
        Require(ConstructorInitialization.Check(new(constructor, [new(0x1000, [Initialize(), Jump(0x1000)])])) is not null,
            "回边不能重复初始化 this");

        var copied = new LocalValue(new Variable(Storage.Temp(9), 1), types.Int32, 32);
        var argument = new ArgumentValue(0, "value", types.Int32, 32);
        var mutate = new MethodRef(new MethodDef
        {
            Index = -1, Owner = owner, Name = "Mutate", Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = types.Void,
            Parameters = [new ParameterDef("value", new ByRefRef(types.Int32), 0, null, false)],
        }, [], []);
        var parameterStore = new ManagedStore(0x3000, location, argument);
        var delegationTarget = new ManagedBody(Method(owner, ".ctor", types.Int32), [new(0x1000, [Initialize(), parameterStore, returned])]);
        var addressedCopy = new ManagedBody(Method(owner, ".ctor", types.Int32, types.Boolean), [new(0x1000,
        [
            new ManagedAssignment(0x1000, copied, argument),
            new ManagedCall(0x1004, new(mutate, null, [new AddressValue(copied, new ByRefRef(types.Int32))]), null, false),
            Initialize(), parameterStore, returned,
        ])]);
        Require(ConstructorDelegations.Match(types, addressedCopy, new(0x2000, delegationTarget)) is null,
            "被取地址的局部副本不能替换为参数本身，否则 ref 写入会改变后续构造参数");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ConstructorChecks", new Version(1, 0)), "ConstructorChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.ImportReference(typeof(BaseProbe)));
        module.Types.Add(host);
        var actualField = new FieldDefinition("Value", FieldAttributes.Public, module.TypeSystem.Int32); host.Fields.Add(actualField);
        var actual = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
        actual.Parameters.Add(new ParameterDefinition(module.TypeSystem.Boolean)); host.Methods.Add(actual);
        TypeReference Reference(TypeRef type) => type == ownerRef ? host : type == parentRef ? module.ImportReference(typeof(BaseProbe))
            : module.ImportReference(System.Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var emitter = new BodyEmitter(types, Reference, f => f.Field == field ? actualField : throw new NotSupportedException(f.ToString()),
            m => m == baseConstructor ? module.ImportReference(typeof(BaseProbe).GetConstructor(System.Type.EmptyTypes)) : throw new NotSupportedException(m.ToString()));
        var problem = emitter.Emit(both, actual);
        Require(problem is null, problem ?? "构造函数输出");
        var aliasActual = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
        aliasActual.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32)); host.Methods.Add(aliasActual);
        var aliasBody = Body(new ManagedAssignment(0x1000, alias, self), Initialize(alias), Store(5), returned)
            with { Method = Method(owner, ".ctor", types.Int32) };
        problem = emitter.Emit(aliasBody, aliasActual);
        Require(problem is null, problem ?? "this 副本构造函数输出");
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
        BaseProbe.Calls = 0;
        BaseProbe.Observed.Clear();
        foreach (var choice in new[] { false, true })
        {
            var instance = Activator.CreateInstance(runtime, [choice])!;
            Require((int)runtime.GetField("Value")!.GetValue(instance)! == (choice ? 3 : 4), "分支字段初始化结果");
        }
        Require(BaseProbe.Calls == 2, "每个实例恰好调用一次基类构造函数");
        var aliased = Activator.CreateInstance(runtime, [0])!;
        Require(BaseProbe.Calls == 3 && (int)runtime.GetField("Value")!.GetValue(aliased)! == 5, "CLR 执行 this 副本上的基类构造调用");
        Require(BaseProbe.Observed.SequenceEqual(new int?[] { 0, 3, 0 }), "基类观察到的字段值保留初始化先后顺序");
        Console.WriteLine("构造初始化检查通过：准备语句、字段初始化、this 副本、分支、回边，以及缺失、重复、读取和逃逸拒绝");
        Native(session);
        ConstructorDelegationCheck.Run(session);
        return 0;
    }

    private static void Native(RecoverySession session)
    {
        var source = session.Model.Code[0x51f7578].Single().Method;
        Require(source.ToString() == "Sekai.Api.GetSuiteUserPartsApi..ctor" && source.Method.Parameters is [var parameter] && parameter.Type == session.Types.Int64,
            "真实 API 构造函数签名");
        var recovered = BodyRecovery.Recover(session, session.Analyze(source, source.Method.Address));
        Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
        var baseCall = recovered.Body!.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single();
        Require(baseCall.Invocation.Method.DeclaringType == source.Method.Owner.BaseType && baseCall.Invocation.Arguments.Count == 0, "实际基类构造调用");
        Require(ManagedAccess.Method(session.Types, source.Method.Owner, baseCall.Invocation.Method, source.DeclaringType), "具体泛型基类的 protected 构造函数可从派生类调用");
        Require(!ManagedAccess.Method(session.Types, source.Method.Owner, baseCall.Invocation.Method, baseCall.Invocation.Method.DeclaringType),
            "protected 访问不能绕过接收者限制");
        var field = source.Method.Owner.Fields.Single(f => f.Name == "userId");
        Require(field.Offset == 0x48 && field.Type == session.Types.Int64, "真实字段偏移与类型");
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeConstructorChecks", new Version(1, 0)), "NativeConstructorChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Api", TypeAttributes.Public, module.ImportReference(typeof(BaseProbe))); module.Types.Add(host);
        var actualField = new FieldDefinition("userId", FieldAttributes.Public | FieldAttributes.InitOnly, module.TypeSystem.Int64); host.Fields.Add(actualField);
        var actual = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
        actual.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int64)); host.Methods.Add(actual);
        TypeReference Reference(TypeRef type) => type == source.DeclaringType ? host : type == source.Method.Owner.BaseType ? module.ImportReference(typeof(BaseProbe))
            : type == session.Types.Int64 ? module.TypeSystem.Int64 : ManagedTypes.IsVoid(type) ? module.TypeSystem.Void : throw new NotSupportedException(type.ToString());
        var emitter = new BodyEmitter(session.Types, Reference, f => f.Field == field ? actualField : throw new NotSupportedException(f.ToString()),
            m => m == baseCall.Invocation.Method ? module.ImportReference(typeof(BaseProbe).GetConstructor(System.Type.EmptyTypes)) : throw new NotSupportedException(m.ToString()));
        var problem = emitter.Emit(recovered.Body, actual); Require(problem is null, problem ?? "真实构造函数输出");
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Api", true)!;
        BaseProbe.Calls = 0;
        foreach (var value in new[] { long.MinValue, -1L, 0L, 1L, long.MaxValue })
        {
            var instance = Activator.CreateInstance(runtime, [value])!;
            Require((long)runtime.GetField("userId")!.GetValue(instance)! == value, "真实构造函数保存完整 64 位字段");
        }
        Require(BaseProbe.Calls == 5, "真实构造函数的基类调用次数");
        Console.WriteLine("真实 API 构造函数 0x51f7578 执行通过：基类调用与 long 边界值字段写入；基类为记录宿主，未执行 API 请求");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
