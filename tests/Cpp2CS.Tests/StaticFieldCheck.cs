using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class StaticFieldCheck
{
    public struct Pair { public int A; public int B; }
    public static void Mutate(ref int first, ref int second) { first = unchecked(first + 1); second = unchecked(second * 2); }

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        var counter = session.Model.Code[0x58a58d0].Single().Method.Method.Owner;
        var count = counter.Fields.Single(f => f.IsStatic && f.Type == types.Int32 && f.Offset == 0);
        Require(counter.FullName == "Sekai.Mysekai.GCAllocChecker", "真实计数类型身份");
        var slot = new Variable(Storage.Gpr(8), 1);
        var klass = new Variable(Storage.Gpr(9), 1);
        var storage = new Variable(Storage.Gpr(10), 1);
        Stmt[] Metadata(int storageOffset = 0xb8) =>
        [
            new Define(0x1000, slot, new Load(Expr.C(0xb7449a8, 64), 64)),
            new Define(0x1004, klass, new Load(new Use(slot, 64), 64)),
            new Define(0x1008, storage, new Load(new Binary(BinOp.Add, new Use(klass, 64), Expr.C((ulong)storageOffset, 64), 64), 64)),
        ];
        MethodRef Method(TypeDef owner, string name, TypeRef result, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1,
            Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL,
            ReturnType = result, Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
        }, [], []);
        PreparedMethod Prepare(MethodRef method, params Stmt[] statements) => new(method, session.Abi.ClassifyReturn(method.Method.ReturnType, out _),
            new MachineFunction { Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1100, BoundaryEvidence.SymbolCandidate, "静态字段合成检查"),
                Blocks = [new Block(0x1000) { Statements = [.. statements] }] }, null, []);
        var address = new Use(storage, 64);
        var saved = new Variable(Storage.Gpr(11), 1);
        var prepared = Prepare(Method(counter, "ReadThenWrite", types.Int32, types.Int32), [.. Metadata(),
            new Define(0x100c, saved, new Load(address, 32)),
            new Store(0x1010, address, new Use(new Variable(Storage.Gpr(0), 0), 32)),
            new Return(0x1014) { Value = new Use(saved, 32) }]);
        var values = new ValueRecovery(session, prepared);
        Require(values.Metadata.StaticAddress(address) is { Offset: 0, Type.Definition: var owner } && owner == counter,
            "类型信息、静态存储和字段偏移必须来自同一个真实类型");
        Require(values.Metadata.IsRuntimeReference(storage), "静态存储指针不作为 CLR 局部对象输出");
        Require(values.Location(address, 32, out _) is StaticFieldValue { Field.Field: var located } && located == count, "静态字段按真实布局定位");
        Require(values.Location(address, 16, out _) is null, "部分静态字段读写不能冒充完整字段");
        var reference = values.RecoverAs(address, new ByRefRef(types.Int32), out _);
        Require(reference is AddressValue { Target: StaticFieldValue }, "静态字段地址只在明确的引用类型上下文中恢复");
        var pointerReturn = Prepare(Method(counter, "Escaped", types.Object), [.. Metadata(), new Return(0x100c) { Value = address }]);
        Require(BodyRecovery.Recover(session, pointerReturn).Body is null, "静态存储指针不能作为对象返回");
        var wrongOffset = Prepare(Method(counter, "WrongOffset", types.Int32), [.. Metadata(0xc0), new Return(0x100c) { Value = new Load(address, 32) }]);
        Require(BodyRecovery.Recover(session, wrongOffset).Body is null, "rgctx 偏移不能冒充静态存储");
        var shifted = new Variable(Storage.Gpr(12), 1);
        var merged = new Variable(Storage.Gpr(13), 1);
        var phi = Prepare(Method(counter, "Phi", types.Void), [.. Metadata(),
            new Define(0x100c, shifted, new Binary(BinOp.Add, address, Expr.C(0, 64), 64)), new Phi(0x1010, merged, [storage, shifted])]);
        Require(new MetadataReferences(session.Model, phi.Function).StaticAddress(new Use(merged, 64)) is { Offset: 0 }, "同一静态存储的汇合保持身份");
        phi.Function.Blocks[0].Statements[3] = new Define(0x100c, shifted, new Binary(BinOp.Add, address, Expr.C(4, 64), 64));
        Require(new MetadataReferences(session.Model, phi.Function).StaticAddress(new Use(merged, 64)) is null, "不同静态偏移的汇合不能选择其中一侧");
        Require(session.Model.Fields.Any(f => f.IsThreadStatic && f.CustomAttributes.Any(a => a.Constructor.Owner.FullName == "System.ThreadStaticAttribute")),
            "输入模型从真实特性辨认线程静态字段");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("StaticFieldChecks", new Version(1, 0)), "StaticFieldChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var hosts = new Dictionary<TypeDef, TypeDefinition>();
        var fields = new Dictionary<FieldDef, FieldDefinition>();
        TypeDefinition Host(TypeDef type, string name)
        {
            var host = new TypeDefinition("Checks", name, TypeAttributes.Public | TypeAttributes.BeforeFieldInit, module.TypeSystem.Object);
            module.Types.Add(host); hosts.Add(type, host); return host;
        }
        TypeReference Reference(TypeRef type) => type is DefinitionRef definition && hosts.TryGetValue(definition.Definition, out var host) ? host
            : type is ByRefRef byRef ? new ByReferenceType(Reference(byRef.Element))
            : module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        void Field(FieldDef field, string name)
        {
            var flags = FieldAttributes.Public | FieldAttributes.Static;
            if ((field.Attributes & SR.FieldAttributes.InitOnly) != 0) flags |= FieldAttributes.InitOnly;
            var actual = new FieldDefinition(name, flags, Reference(field.Type));
            hosts[field.Owner].Fields.Add(actual); fields.Add(field, actual);
        }
        Host(counter, "Counter"); Field(count, "Count");
        var plan = session.Model.Code[0x561bda4].Single().Method.Method.Owner;
        Require(plan.FullName == "Sekai.Mysekai.NPCTalkReservationUtility", "真实计划编号类型身份");
        Host(plan, "Plans"); Field(plan.Fields.Single(f => f.IsStatic && f.Type == types.Int64 && f.Offset == 0), "Last");
        var matching = session.Model.Code[0x5b75360].Single().Method.Method.Owner;
        Require(matching.FullName == "Sekai.Mysekai.Multi.MatchingController", "真实引用类型身份");
        Host(matching, "Matching"); Field(matching.Fields.Single(f => f.IsStatic && f.Type == new DefinitionRef(matching, []) && f.Offset == 0), "Instance");
        var mutate = Method(counter, nameof(Mutate), types.Void, new ByRefRef(types.Int32), new ByRefRef(types.Int32));
        var emitter = new BodyEmitter(types, Reference, f => fields[f.Field], m => m == mutate
            ? module.ImportReference(typeof(StaticFieldCheck).GetMethod(nameof(Mutate))) : throw new NotSupportedException(m.ToString()));
        void Emit(ManagedBody body)
        {
            var definition = body.Method.Method;
            var actual = new MethodDefinition(definition.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(definition.ReturnType));
            foreach (var parameter in definition.Parameters) actual.Parameters.Add(new ParameterDefinition(Reference(parameter.Type)));
            hosts[definition.Owner].Methods.Add(actual);
            var problem = emitter.Emit(body, actual); Require(problem is null, problem ?? definition.Name);
        }
        var recovered = BodyRecovery.Recover(session, prepared);
        Require(recovered.Body is not null, string.Join("; ", recovered.Problems)); Emit(recovered.Body!);
        var countValue = new StaticFieldValue(new FieldRef(count, new DefinitionRef(counter, [])), types.Int32, 32);
        Emit(new ManagedBody(Method(counter, "Alias", types.Int32), [new ManagedBlock(0x1000,
            [new ManagedCall(0x1000, new(mutate, null, [reference!, reference!]), null, false), new ManagedReturn(0x1004, countValue)])]));
        foreach (var va in new ulong[] { 0x58a58d0, 0x58a5918, 0x561bda4, 0x5b75360, 0x5b753a8 })
        {
            var source = session.Model.Code[va].Single().Method;
            var result = BodyRecovery.Recover(session, session.Analyze(source, va));
            Require(result.Body is not null, string.Join("; ", result.Problems)); Emit(result.Body!);
        }
        LayoutAndPermissions(types, assembly);
        using var bytes = new MemoryStream(); assembly.Write(bytes);
        Execute(SR.Assembly.Load(bytes.ToArray()));
        var directory = Path.Combine("artifacts", "static-source-check", Guid.NewGuid().ToString("N")); Directory.CreateDirectory(directory);
        var path = Path.Combine(directory, assembly.Name.Name + ".dll"); assembly.Write(path);
        var sources = Decompilation.Decompile(path, Path.GetDirectoryName(typeof(StaticFieldCheck).Assembly.Location)!, _ => true, false, recoveringBodies: true);
        foreach (var source in sources) File.WriteAllText(Path.Combine(directory, source.TypeName + ".cs"), source.Source);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Append(typeof(StaticFieldCheck).Assembly.Location).Distinct().Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("RecompiledStaticFieldChecks", sources.Select(s => CSharpSyntaxTree.ParseText(s.Source)), references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        using var compiled = new MemoryStream(); var emitted = compilation.Emit(compiled);
        Require(emitted.Success, string.Join(Environment.NewLine, emitted.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        Execute(SR.Assembly.Load(compiled.ToArray()));
        Console.WriteLine("静态字段检查通过：布局、元数据指针拒绝、读取顺序、共享引用、只读与权限；5 个真实方法的 CIL/C# 往返执行；未加载 Unity");
        return 0;
    }

    private static void Execute(SR.Assembly assembly)
    {
        var counter = assembly.GetType("Checks.Counter", true)!;
        foreach (var value in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            counter.GetMethod("set_Count")!.Invoke(null, [value]);
            Require((int)counter.GetMethod("get_Count")!.Invoke(null, [])! == value, "真实静态 getter/setter 保留整数位型");
            Require((int)counter.GetMethod("ReadThenWrite")!.Invoke(null, [17])! == value && (int)counter.GetField("Count")!.GetValue(null)! == 17,
                "读取后的静态写入不能改变已经保存的值");
        }
        counter.GetField("Count")!.SetValue(null, 3);
        Require((int)counter.GetMethod("Alias")!.Invoke(null, [])! == 8, "两个引用参数共享同一静态字段");
        var plans = assembly.GetType("Checks.Plans", true)!;
        foreach (var value in new[] { long.MinValue, -1L, 0L, 1L, long.MaxValue })
        {
            plans.GetField("Last")!.SetValue(null, value);
            for (var i = 1; i <= 3; i++) Require((long)plans.GetMethod("IssuePlanId")!.Invoke(null, [])! == unchecked(value + i), "真实方法读取、递增并写回静态编号");
        }
        var matching = assembly.GetType("Checks.Matching", true)!;
        var instance = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(matching);
        foreach (var value in new[] { instance, null })
        {
            matching.GetMethod("set_Instance")!.Invoke(null, [value]);
            Require(ReferenceEquals(matching.GetMethod("get_Instance")!.Invoke(null, []), value), "真实静态引用访问器保持对象身份和空值");
        }
        var storage = assembly.GetType("Checks.Storage", true)!;
        Require((int)storage.GetField("Readonly")!.GetValue(null)! == 29, "本类静态构造函数可以初始化只读静态字段");
        foreach (var bits in new uint[] { 0, 1, 0x80000000, 0x7f800000, 0x7fc01234 })
        {
            var value = BitConverter.Int32BitsToSingle(unchecked((int)bits));
            var result = (float)storage.GetMethod("Float")!.Invoke(null, [value])!;
            Require(unchecked((uint)BitConverter.SingleToInt32Bits(result)) == bits, "静态浮点字段保留位型");
        }
        storage.GetMethod("Nested")!.Invoke(null, [11]);
        Require(((Pair)storage.GetField("Pair")!.GetValue(null)!).B == 11, "嵌套字段写入不修改静态结构体副本");
    }

    private static void LayoutAndPermissions(ManagedTypes types, AssemblyDefinition assembly)
    {
        TypeDef Owner(string name, bool valueType = false) => new() { Index = -1, Assembly = "Checks.dll", Namespace = "Checks", Name = name,
            Token = 0, Attributes = SR.TypeAttributes.Public, IsValueType = valueType, IsEnum = false, Size = valueType ? 8 : 16 };
        var owner = Owner("Storage"); var pairOwner = Owner("Pair", true); var pair = new DefinitionRef(pairOwner, []);
        FieldDef Field(TypeDef type, string name, TypeRef value, int offset, SR.FieldAttributes attributes) => new()
            { Index = -1, Owner = type, Name = name, Type = value, Offset = offset, Attributes = attributes, Token = 0 };
        var a = Field(pairOwner, "A", types.Int32, 0, SR.FieldAttributes.Public);
        var b = Field(pairOwner, "B", types.Int32, 4, SR.FieldAttributes.Public); pairOwner.Fields = [a, b];
        var floating = Field(owner, "FloatValue", types.Single, 0, SR.FieldAttributes.Public | SR.FieldAttributes.Static);
        var readonlyField = Field(owner, "Readonly", types.Int32, 4, SR.FieldAttributes.Public | SR.FieldAttributes.Static | SR.FieldAttributes.InitOnly);
        var composite = Field(owner, "Pair", pair, 8, SR.FieldAttributes.Public | SR.FieldAttributes.Static);
        var thread = Field(owner, "Thread", types.Int32, 16, SR.FieldAttributes.Public | SR.FieldAttributes.Static); thread.IsThreadStatic = true;
        var readonlyPair = Field(owner, "ReadonlyPair", pair, 20, SR.FieldAttributes.Public | SR.FieldAttributes.Static | SR.FieldAttributes.InitOnly);
        var protectedField = Field(owner, "Protected", types.Int32, 28, SR.FieldAttributes.Family | SR.FieldAttributes.Static);
        owner.Fields = [floating, readonlyField, composite, thread, readonlyPair, protectedField];
        var ownerType = new DefinitionRef(owner, []);
        Require(types.StaticFieldPath(ownerType, 12, 4) is { Count: 2 } path && path[0].Field.Field == composite && path[1].Field.Field == b,
            "静态结构体偏移继续按实例字段布局查找");
        Require(types.StaticFieldPath(ownerType, 16, 4) is null && types.StaticFieldPath(ownerType, 0, 2) is null,
            "线程静态和部分字段读取不能套用普通静态存储");
        var derived = Owner("Derived"); derived.BaseType = ownerType;
        Require(ManagedAccess.Field(types, derived, new(protectedField, ownerType), null)
            && !ManagedAccess.Field(types, Owner("Foreign"), new(protectedField, ownerType), null), "protected 静态字段没有实例接收者，但仍限制访问类型");
        Require(types.StaticFieldPath(new DefinitionRef(derived, []), 28, 4) is null, "派生类型的静态存储不包含基类字段");
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Storage", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(host);
        TypeReference Reference(TypeRef type) => type == pair ? module.ImportReference(typeof(Pair))
            : type is ByRefRef reference ? new ByReferenceType(Reference(reference.Element))
            : module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var fields = new Dictionary<FieldDef, FieldReference>();
        foreach (var field in new[] { floating, readonlyField, composite, readonlyPair })
        {
            var actual = new FieldDefinition(field.Name, FieldAttributes.Public | FieldAttributes.Static
                | ((field.Attributes & SR.FieldAttributes.InitOnly) != 0 ? FieldAttributes.InitOnly : 0), Reference(field.Type));
            host.Fields.Add(actual); fields.Add(field, actual);
        }
        fields.Add(b, module.ImportReference(typeof(Pair).GetField(nameof(Pair.B))));
        StaticFieldValue Value(FieldDef field) => new(new(field, ownerType), field.Type, types.Size(field.Type) * 8);
        var emitter = new BodyEmitter(types, Reference, f => fields[f.Field], m => throw new NotSupportedException(m.ToString()));
        void Emit(string name, TypeRef result, ManagedStatement[] statements, bool accepted = true, params TypeRef[] parameters)
        {
            var definition = new MethodDef { Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
                ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result, Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            var actual = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, Reference(result));
            if (name == ".cctor") actual.Attributes = MethodAttributes.Private | MethodAttributes.Static | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName;
            foreach (var parameter in parameters) actual.Parameters.Add(new ParameterDefinition(Reference(parameter)));
            var problem = emitter.Emit(new(new(definition, [], []), [new(0x1000, statements)]), actual);
            Require((problem is null) == accepted, problem ?? "错误静态写入被接受");
            if (accepted) host.Methods.Add(actual);
        }
        Emit(".cctor", types.Void, [new ManagedStore(0x1000, Value(readonlyField), new ConstantValue(29, types.Int32, 32)), new ManagedReturn(0x1004, null)]);
        Emit("BadWrite", types.Void, [new ManagedStore(0x1000, Value(readonlyField), new ConstantValue(1, types.Int32, 32)), new ManagedReturn(0x1004, null)], false);
        Emit("BadAddress", new ByRefRef(types.Int32), [new ManagedReturn(0x1000, new AddressValue(Value(readonlyField), new ByRefRef(types.Int32)))], false);
        var nested = new FieldValue(Value(composite), new(b, pair), types.Int32, 32);
        var readonlyNested = new FieldValue(Value(readonlyPair), new(b, pair), types.Int32, 32);
        Emit("BadNested", types.Void, [new ManagedStore(0x1000, readonlyNested, new ConstantValue(1, types.Int32, 32)), new ManagedReturn(0x1004, null)], false);
        Emit("Nested", types.Void, [new ManagedStore(0x1000, nested, new ArgumentValue(0, "value", types.Int32, 32)), new ManagedReturn(0x1004, null)], true, types.Int32);
        Emit("Float", types.Single, [new ManagedStore(0x1000, Value(floating), new ArgumentValue(0, "value", types.Single, 32)), new ManagedReturn(0x1004, Value(floating))], true, types.Single);
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
