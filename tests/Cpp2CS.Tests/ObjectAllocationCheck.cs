using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Runtime;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class ObjectAllocationCheck
{
    public static readonly List<string> Events = [];
    public static object? Escaped;
    public static void Record(string value) => Events.Add(value);
    public static void Observe(object value)
    {
        Escaped = value;
        Record("observe:" + value.GetType().GetField("Value")!.GetValue(value));
    }
    public static void CheckArgument(int value)
    {
        Record("ctor");
        if (value < 0) throw new InvalidOperationException("constructor failure");
    }

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        Require(session.Resolver.Resolve(0x49c8830) is HelperCallee { Helper.Kind: HelperKind.ObjectNew }, "普通分配辅助函数身份");
        Require(session.Resolver.Resolve(session.Model.Image.Exports["il2cpp_object_new"]) is not HelperCallee { Helper.Kind: HelperKind.ObjectNew },
            "捕获异常并返回空值的导出包装不能当成直接抛出的分配");
        foreach (var unsupported in new TypeRef[] { types.String, types.Int32, types.Delegate, types.Array, new ArrayRef(types.Object, 1),
            new ByRefRef(types.Object), new DefinitionRef(types.CorlibDefinition("System.Collections.Generic.List")!, []) })
            Require(!ObjectAllocation.Supported(types, unsupported), "专用或开放类型不能使用普通对象分配: " + unsupported);
        Synthetic(session);
        Native(session);
        return 0;
    }

    public static int Saved(string path)
    {
        using var assembly = AssemblyDefinition.ReadAssembly(path);
        Action<SR.Assembly> execute = assembly.Name.Name == "NativeAllocationChecks" ? ExecuteCache : a => Execute(a, constructors: false);
        execute(SR.Assembly.Load(File.ReadAllBytes(path))); Source(assembly, execute);
        Console.WriteLine("已保存对象分配程序集的 CIL/C# 往返执行通过");
        return 0;
    }

    private static void Synthetic(RecoverySession session)
    {
        var types = session.Types;
        TypeDef Owner(string name, SR.TypeAttributes attributes = SR.TypeAttributes.Public) => new()
        {
            Index = -1, Assembly = "AllocationChecks.dll", Namespace = "Checks", Name = name, Token = 0,
            Attributes = attributes, IsValueType = false, IsEnum = false, BaseType = types.Object,
        };
        var owner = Owner("Harness"); var payload = Owner("Payload", SR.TypeAttributes.Public | SR.TypeAttributes.BeforeFieldInit);
        var failure = Owner("Failure"); var probe = Owner("Probe"); var plain = Owner("Plain");
        var payloadType = new DefinitionRef(payload, []); var failureType = new DefinitionRef(failure, []);
        var plainType = new DefinitionRef(plain, []);
        MethodRef Method(TypeDef parent, string name, TypeRef result, bool instance = false, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = parent, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | (instance ? 0 : SR.MethodAttributes.Static),
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result,
            Parameters = parameters.Select((p, i) => new ParameterDef("p" + i, p, 0, null, false)).ToArray(),
        }, [], []);
        var constructor = Method(payload, ".ctor", types.Void, true, types.Int32);
        var plainConstructor = Method(plain, ".ctor", types.Void, true, types.Int32); plain.Methods = [plainConstructor.Method];
        payload.Methods = [constructor.Method, Method(payload, ".cctor", types.Void).Method];
        failure.Methods = [Method(failure, ".cctor", types.Void).Method];
        var field = new FieldDef { Index = -1, Owner = payload, Name = "Value", Type = types.Int32, Offset = 16, Attributes = SR.FieldAttributes.Public };
        payload.Fields = [field];
        var plainFieldModel = new FieldDef { Index = -1, Owner = plain, Name = "Value", Type = types.Int32, Offset = 16, Attributes = SR.FieldAttributes.Public };
        plain.Fields = [plainFieldModel];
        var observer = Method(probe, "Observe", types.Void, false, types.Object);
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("AllocationChecks", new Version(1, 0)), "AllocationChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(host);
        var actualPayload = new TypeDefinition("Checks", "Payload", TypeAttributes.Public | TypeAttributes.BeforeFieldInit, module.TypeSystem.Object); module.Types.Add(actualPayload);
        var actualFailure = new TypeDefinition("Checks", "Failure", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(actualFailure);
        var actualPlain = new TypeDefinition("Checks", "Plain", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(actualPlain);
        var plainField = new FieldDefinition("Value", FieldAttributes.Public, module.TypeSystem.Int32); actualPlain.Fields.Add(plainField);
        var actualPlainConstructor = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
        actualPlainConstructor.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32)); actualPlain.Methods.Add(actualPlainConstructor);
        var actualField = new FieldDefinition("Value", FieldAttributes.Public, module.TypeSystem.Int32); actualPayload.Fields.Add(actualField);
        actualPayload.Fields.Add(new FieldDefinition("Reference", FieldAttributes.Public, module.TypeSystem.Object));
        var actualConstructor = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
        actualConstructor.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32)); actualPayload.Methods.Add(actualConstructor);
        var il = actualConstructor.Body.GetILProcessor();
        il.Emit(OpCodes.Ldarg_0); il.Emit(OpCodes.Call, module.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)));
        il.Emit(OpCodes.Ldarg_1); il.Emit(OpCodes.Call, module.ImportReference(typeof(ObjectAllocationCheck).GetMethod(nameof(CheckArgument))));
        il.Emit(OpCodes.Ldarg_0); il.Emit(OpCodes.Ldarg_1); il.Emit(OpCodes.Stfld, actualField); il.Emit(OpCodes.Ret);
        il = actualPlainConstructor.Body.GetILProcessor();
        il.Emit(OpCodes.Ldarg_0); il.Emit(OpCodes.Call, module.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)));
        il.Emit(OpCodes.Ldarg_0); il.Emit(OpCodes.Ldarg_1); il.Emit(OpCodes.Stfld, plainField); il.Emit(OpCodes.Ret);
        foreach (var target in new[] { actualPayload, actualFailure })
        {
            var cctor = new MethodDefinition(".cctor", MethodAttributes.Private | MethodAttributes.Static | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
            target.Methods.Add(cctor); il = cctor.Body.GetILProcessor();
            il.Emit(OpCodes.Ldstr, target == actualPayload ? "init" : "failed-init");
            il.Emit(OpCodes.Call, module.ImportReference(typeof(ObjectAllocationCheck).GetMethod(nameof(Record))));
            if (target == actualFailure) { il.Emit(OpCodes.Newobj, module.ImportReference(typeof(InvalidOperationException).GetConstructor(Type.EmptyTypes))); il.Emit(OpCodes.Throw); }
            else il.Emit(OpCodes.Ret);
        }
        TypeReference Reference(TypeRef type) => type == payloadType ? actualPayload : type == failureType ? actualFailure : type == plainType ? actualPlain
            : type == types.RuntimeTypeHandle ? module.ImportReference(typeof(RuntimeTypeHandle)) : type == types.Type ? module.ImportReference(typeof(Type))
            : type == types.Object ? module.TypeSystem.Object : type == types.Int32 ? module.TypeSystem.Int32 : ManagedTypes.IsVoid(type) ? module.TypeSystem.Void
            : throw new NotSupportedException(type.ToString());
        MethodReference Called(MethodRef method) => method == constructor ? actualConstructor : method == plainConstructor ? actualPlainConstructor : method == observer
            ? module.ImportReference(typeof(ObjectAllocationCheck).GetMethod(nameof(Observe))) : RuntimeMethod(module, method);
        var emitter = new BodyEmitter(types, Reference, f => f.Field == field ? actualField : throw new NotSupportedException(f.ToString()), Called);
        MethodDefinition Emit(ManagedBody body)
        {
            var method = new MethodDefinition(body.Method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(body.Method.Method.ReturnType));
            foreach (var p in body.Method.Method.Parameters) method.Parameters.Add(new ParameterDefinition(Reference(p.Type)));
            host.Methods.Add(method); var problem = emitter.Emit(body, method); Require(problem is null, problem ?? method.Name); return method;
        }
        Emit(new(Method(owner, "Allocate", payloadType), [new(0x1000, [new ManagedReturn(0x1000, new ObjectAllocationValue(payloadType))])]));
        Emit(new(Method(owner, "Failed", failureType), [new(0x1000, [new ManagedReturn(0x1000, new ObjectAllocationValue(failureType))])]));
        var local = new LocalValue(new(Storage.Temp(0), 1), payloadType, 64);
        var unused = Emit(new(Method(owner, "Unused", types.Void), [new(0x1000, [new ManagedAssignment(0x1000, local, new ObjectAllocationValue(payloadType)), new ManagedReturn(0x1010, null)])]));
        Require(unused.Body.Instructions.Any(i => i.OpCode == OpCodes.Call && i.Operand is MethodReference { Name: "GetUninitializedObject" }), "未使用结果也保留分配调用");
        var publish = Emit(new(Method(owner, "Publish", payloadType, false, types.Int32), [new(0x1000,
        [
            new ManagedAssignment(0x1000, local, new ObjectAllocationValue(payloadType)),
            new ManagedStore(0x1004, new FieldValue(local, new(field, payloadType), types.Int32, 32), new ConstantValue(7, types.Int32, 32)),
            new ManagedCall(0x1008, new(observer, null, [local]), null, false),
            new ManagedCall(0x100c, new(constructor, local, [new ArgumentValue(0, "value", types.Int32, 32)]), null, false),
            new ManagedReturn(0x1010, local),
        ])]));
        var plainLocal = new LocalValue(new(Storage.Temp(1), 1), plainType, 64);
        var plainAllocate = new ManagedAssignment(0x1000, plainLocal, new ObjectAllocationValue(plainType));
        var plainCall = new ManagedCall(0x1004, new(plainConstructor, plainLocal, [new ArgumentValue(0, "value", types.Int32, 32)]), null, false);
        var simple = new ManagedBody(Method(owner, "Construct", plainType, false, types.Int32), [new(0x1000, [plainAllocate, plainCall, new ManagedReturn(0x1008, plainLocal)])]);
        var combined = ObjectConstruction.Recover(simple);
        Require(combined.Blocks[0].Statements is [ManagedAssignment { Value: NewObjectValue }, ManagedReturn], "相邻同类型构造合并为 newobj");
        Emit(combined);
        var observed = simple with { Blocks = [new(0x1000, [plainAllocate, new ManagedCall(0x1002, new(observer, null, [plainLocal]), null, false), plainCall, new ManagedReturn(0x1008, plainLocal)])] };
        Require(ObjectConstruction.Recover(observed).Blocks[0].Statements[0] is ManagedAssignment { Value: ObjectAllocationValue }, "不能跨过构造前逃逸调用");
        var readSelf = plainCall with { Invocation = plainCall.Invocation with { Arguments = [new FieldValue(plainLocal, new(plainFieldModel, plainType), types.Int32, 32)] } };
        Require(ObjectConstruction.Recover(simple with { Blocks = [new(0x1000, [plainAllocate, readSelf, new ManagedReturn(0x1008, plainLocal)])] })
            .Blocks[0].Statements[0] is ManagedAssignment { Value: ObjectAllocationValue }, "不能把分配后字段读取提前到 newobj 的参数求值");
        var wrongReceiver = plainCall with { Invocation = plainCall.Invocation with { Receiver = new ArgumentValue(0, "existing", plainType, 64) } };
        Require(ObjectConstruction.Recover(simple with { Blocks = [new(0x1000, [plainAllocate, wrongReceiver, new ManagedReturn(0x1008, plainLocal)])] })
            .Blocks[0].Statements[0] is ManagedAssignment { Value: ObjectAllocationValue }, "不能合并另一个对象的构造调用");
        var tail = ObjectConstruction.Recover(simple with { Method = Method(owner, "Tail", types.Void, false, types.Int32), Blocks = [new(0x1000, [plainAllocate, plainCall with { Tail = true }])] });
        Require(tail.Blocks[0].Statements is [ManagedAssignment { Value: NewObjectValue }, ManagedReturn { Value: null }], "构造尾调用合并后仍保留 void 返回");
        var initialized = simple with { Blocks = [new(0x1000, [new ManagedAssignment(0x1000, local, new ObjectAllocationValue(payloadType)),
            new ManagedCall(0x1004, new(constructor, local, [new ConstantValue(0, types.Int32, 32)]), null, false), new ManagedReturn(0x1008, local)])] };
        Require(ObjectConstruction.Recover(initialized).Blocks[0].Statements[0] is ManagedAssignment { Value: ObjectAllocationValue },
            "有静态构造函数的分配不由当前合并规则改变初始化时机");
        using var stream = new MemoryStream(); assembly.Write(stream);
        Execute(SR.Assembly.Load(stream.ToArray()), constructors: true);
        Console.WriteLine("对象分配 CIL 执行通过：零初始化、独立身份、BeforeFieldInit、初始化失败缓存、构造前观察与逃逸、实例构造失败传播");
        // 分离式实例构造调用尚无通用 C# 语法；此处单独核验无构造分配的源码往返。
        host.Methods.Remove(publish);
        Source(assembly, a => Execute(a, constructors: false));
        Console.WriteLine("清零分配及相邻构造合并的 C# 往返执行通过；分离式实例构造调用仅验证 CIL");
    }

    private static void Source(AssemblyDefinition assembly, Action<SR.Assembly> execute)
    {
        var directory = Path.GetFullPath(Path.Combine("artifacts", "allocation-source-check", Guid.NewGuid().ToString("N")));
        Directory.CreateDirectory(directory); var file = Path.Combine(directory, assembly.Name.Name + ".dll"); assembly.Write(file);
        File.Copy(typeof(ObjectAllocationCheck).Assembly.Location, Path.Combine(directory, "Cpp2CS.Tests.dll"));
        var sources = Decompilation.Decompile(file, Path.GetDirectoryName(typeof(ObjectAllocationCheck).Assembly.Location)!, _ => true, false, recoveringBodies: true);
        foreach (var source in sources) File.WriteAllText(Path.Combine(directory, source.TypeName + ".cs"), source.Source);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator).Append(typeof(ObjectAllocationCheck).Assembly.Location)
            .Distinct().Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("Recompiled" + assembly.Name.Name, sources.Select(s => CSharpSyntaxTree.ParseText(s.Source)), references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        using var output = new MemoryStream(); var result = compilation.Emit(output);
        Require(result.Success, string.Join("\n", result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        execute(SR.Assembly.Load(output.ToArray()));
    }

    private static void Execute(SR.Assembly assembly, bool constructors)
    {
        Events.Clear(); Escaped = null;
        var host = assembly.GetType("Checks.Harness", true)!;
        object? Invoke(string name, params object?[] args) => host.GetMethod(name)!.Invoke(null, args);
        var first = Invoke("Allocate")!; var second = Invoke("Allocate")!;
        Require(!ReferenceEquals(first, second) && first.GetType() == second.GetType(), "每次分配产生同类型的独立对象");
        Require((int)first.GetType().GetField("Value")!.GetValue(first)! == 0 && first.GetType().GetField("Reference")!.GetValue(first) is null,
            "分配跳过实例构造并清零所有字段");
        Invoke("Unused"); Require(Events.SequenceEqual(["init"]), "BeforeFieldInit 类型在分配处初始化且只执行一次");
        for (var i = 0; i < 2; i++)
        {
            var task = Task.Run(() => Invoke("Failed")); Task.WhenAny(task).GetAwaiter().GetResult();
            Require(task.Exception?.InnerException is SR.TargetInvocationException { InnerException: TypeInitializationException { InnerException: InvalidOperationException } },
                "类型初始化失败必须传播");
        }
        Require(Events.Count(e => e == "failed-init") == 1, "类型初始化失败被缓存");
        foreach (var value in new[] { int.MinValue, -1, 0, int.MaxValue })
        {
            var created = Invoke("Construct", value)!;
            Require((int)created.GetType().GetField("Value")!.GetValue(created)! == value, "合并后实例构造保留完整参数值");
        }
        if (!constructors) return;
        Events.Clear(); var result = Invoke("Publish", 9)!;
        Require(ReferenceEquals(Escaped, result) && (int)result.GetType().GetField("Value")!.GetValue(result)! == 9
            && Events.SequenceEqual(["observe:7", "ctor"]), "构造前观察值和构造后对象身份保持");
        Events.Clear(); var failure = Task.Run(() => Invoke("Publish", -1)); Task.WhenAny(failure).GetAwaiter().GetResult();
        Require(failure.Exception?.InnerException is SR.TargetInvocationException { InnerException: InvalidOperationException }
            && Events.SequenceEqual(["observe:7", "ctor"]) && (int)Escaped!.GetType().GetField("Value")!.GetValue(Escaped)! == 7,
            "构造失败保留此前逃逸的对象和副作用，不提前执行构造函数");
    }

    private static MethodReference RuntimeMethod(ModuleDefinition module, MethodRef method) => method.Method.Owner.FullName switch
    {
        "System.Type" when method.Method.Name == "GetTypeFromHandle" => module.ImportReference(typeof(Type).GetMethod("GetTypeFromHandle", [typeof(RuntimeTypeHandle)])),
        "System.Runtime.Serialization.FormatterServices" when method.Method.Name == "GetUninitializedObject" => module.ImportReference(
            Type.GetType("System.Runtime.Serialization.FormatterServices, System.Runtime.Serialization.Formatters", true)!.GetMethod("GetUninitializedObject", [typeof(Type)])),
        "System.Runtime.CompilerServices.RuntimeHelpers" when method.Method.Name == "RunClassConstructor" => module.ImportReference(
            typeof(System.Runtime.CompilerServices.RuntimeHelpers).GetMethod("RunClassConstructor", [typeof(RuntimeTypeHandle)])),
        "System.Object" when method.Method.Name == ".ctor" => module.ImportReference(typeof(object).GetConstructor(Type.EmptyTypes)),
        _ => throw new NotSupportedException(method.ToString()),
    };

    private static void Native(RecoverySession session)
    {
        var types = session.Types;
        var method = session.Model.Code[0x55d31ac].Single().Method;
        Require(method.ToString() == "Sekai.Mysekai.MysekaiLocalCacheData..ctor", "真实构造方法身份");
        var field = method.Method.Owner.Fields.Single(f => !f.IsStatic && f.Offset == 16);
        var dictionaryType = (DefinitionRef)field.Type;
        Require(dictionaryType.Definition.FullName == "System.Collections.Generic.Dictionary" && dictionaryType.Arguments is [DefinitionRef { Definition.IsEnum: true }, var value]
            && value == types.Int32, "真实泛型字典字段");
        var key = dictionaryType.Arguments[0];
        var prepared = session.Analyze(method, method.Method.Address);
        var recovery = BodyRecovery.Recover(session, prepared); Require(recovery.Body is not null, string.Join("; ", recovery.Problems));
        var allocation = recovery.Body!.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Single(a => a.Value is NewObjectValue);
        Require(allocation.Value.Type == dictionaryType, "分配 TypeInfo 与字段的具体泛型类型一致");
        var native = prepared.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single(c => c.Address == 0x55d3208);
        var values = new ValueRecovery(session, prepared);
        Require(values.HelperValue(native with { Arguments = [Expr.C(0, 64)] }, out _) is null, "缺失 TypeInfo 不能猜测对象类型");
        Require(values.HelperValue(native with { Arguments = [new Load(new Load(Expr.C(0xb737490, 64), 64), 64)] }, out _) is null,
            "枚举 TypeInfo 不能冒充普通引用对象");
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeAllocationChecks", new Version(1, 0)), "NativeAllocationChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Cache", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(host);
        var enumType = new TypeDefinition("Checks", "Key", TypeAttributes.Public | TypeAttributes.Sealed, module.ImportReference(typeof(Enum))); module.Types.Add(enumType);
        enumType.Fields.Add(new FieldDefinition("value__", FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName, module.TypeSystem.Int32));
        var dictionary = new GenericInstanceType(module.ImportReference(typeof(Dictionary<,>)));
        dictionary.GenericArguments.Add(enumType); dictionary.GenericArguments.Add(module.TypeSystem.Int32);
        var actualField = new FieldDefinition(field.Name, FieldAttributes.Public, dictionary); host.Fields.Add(actualField);
        TypeReference Reference(TypeRef type) => type == method.DeclaringType ? host : type == dictionaryType ? dictionary : type == key ? enumType
            : type == types.Object ? module.TypeSystem.Object : type == types.Type ? module.ImportReference(typeof(Type))
            : type == types.RuntimeTypeHandle ? module.ImportReference(typeof(RuntimeTypeHandle)) : type == types.Int32 ? module.TypeSystem.Int32
            : ManagedTypes.IsVoid(type) ? module.TypeSystem.Void : throw new NotSupportedException(type.ToString());
        var emitter = new BodyEmitter(types, Reference, f => f.Field == field ? actualField : throw new NotSupportedException(f.ToString()),
            m => m.DeclaringType == dictionaryType && m.Method.Name == ".ctor" && m.Method.Parameters.Count == 0
                ? new MethodReference(".ctor", module.TypeSystem.Void, dictionary) { HasThis = true } : RuntimeMethod(module, m));
        var actual = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void); host.Methods.Add(actual);
        var problem = emitter.Emit(recovery.Body, actual); Require(problem is null, problem ?? method.ToString());
        using var stream = new MemoryStream(); assembly.Write(stream);
        ExecuteCache(SR.Assembly.Load(stream.ToArray())); Source(assembly, ExecuteCache);
        Console.WriteLine("真实 MysekaiLocalCacheData..ctor 0x55d31ac CIL/C# 执行通过：具体枚举字典分配、构造与字段保存；字典映射当前 CLR，未加载 Unity");
    }

    private static void ExecuteCache(SR.Assembly result)
    {
        var runtime = result.GetType("Checks.Cache", true)!;
        var first = Activator.CreateInstance(runtime)!; var second = Activator.CreateInstance(runtime)!;
        // 元数据后备字段名会被 C# 转义；此宿主只映射一个实例字段。
        var storage = runtime.GetFields(SR.BindingFlags.Public | SR.BindingFlags.Instance).Single();
        var firstDictionary = (System.Collections.IDictionary)storage.GetValue(first)!;
        var secondDictionary = (System.Collections.IDictionary)storage.GetValue(second)!;
        Require(firstDictionary.Count == 0 && secondDictionary.Count == 0 && !ReferenceEquals(firstDictionary, secondDictionary), "真实构造体建立互不共享的空字典");
        var runtimeKey = firstDictionary.GetType().GetGenericArguments()[0]; firstDictionary.Add(Enum.ToObject(runtimeKey, 1), 17);
        Require(firstDictionary.Count == 1 && secondDictionary.Count == 0, "实际分配的字典完成构造，可以独立读写");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
