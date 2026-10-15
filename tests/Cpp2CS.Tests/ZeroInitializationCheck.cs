using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class ZeroInitializationCheck
{
    public enum LoadKind { None, Blueprint, Fixture }
    public readonly struct LoadTarget(LoadKind loadType, int id, int colorId)
    {
        public readonly LoadKind LoadType = loadType;
        public readonly int Id = id;
        public readonly int ColorId = colorId;
    }
    public sealed class Preview
    {
        public LoadTarget Current;
        public LoadTarget Next;
        public Renderer? Renderer;
        public int Guard = 12345;
    }
    public sealed class Renderer { public Action OnRelease = null!; public void Release() => OnRelease(); }
    public delegate void ClearReference(ref LoadTarget value);

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        Synthetic(session.Types);
        Native(session);
        return 0;
    }

    private static void Synthetic(ManagedTypes types)
    {
        TypeDef Type(string name, bool value, int size) => new()
        {
            Index = -1, Assembly = "ZeroChecks.dll", Namespace = "Checks", Name = name, Token = 0,
            Attributes = SR.TypeAttributes.Public | (value ? SR.TypeAttributes.SequentialLayout : 0),
            IsValueType = value, IsEnum = false, Size = size, ClassSizeIsDefault = true, BaseType = value ? null : types.Object,
        };
        FieldDef Field(TypeDef owner, string name, TypeRef type, int offset, bool readOnly = true) => new()
        { Index = -1, Owner = owner, Name = name, Type = type, Offset = offset, Attributes = SR.FieldAttributes.Public | (readOnly ? SR.FieldAttributes.InitOnly : 0) };
        var value = Type("LoadTarget", true, 12); var valueType = new DefinitionRef(value, []);
        value.Fields = [Field(value, "LoadType", types.Int32, 0), Field(value, "Id", types.Int32, 4), Field(value, "ColorId", types.Int32, 8)];
        var host = Type("Preview", false, 0); var hostType = new DefinitionRef(host, []);
        host.Fields = [Field(host, "Current", valueType, 16, false), Field(host, "Next", valueType, 28, false)];
        var harness = Type("Harness", false, 0);
        MethodRef Method(string name, TypeRef input, TypeRef result) => new(new MethodDef
        {
            Index = -1, Owner = harness, Name = name, Token = 0, Slot = -1,
            Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL,
            ReturnType = result, Parameters = [new("value", input, 0, null, false)],
        }, [], []);
        FieldValue Member(ManagedValue receiver, FieldDef field) => new(receiver, new(field, new DefinitionRef(field.Owner, [])), field.Type, types.Size(field.Type) * 8);
        ManagedStore Clear(ManagedValue receiver, int field, ulong bits = 0) => new((ulong)(0x1000 + field * 4), Member(receiver, value.Fields[field]), new ConstantValue(bits, types.Int32, 32));
        ManagedBody Body(MethodRef method, params ManagedStatement[] statements) => new(method, [new(0x1000, statements)]);
        var reference = new ArgumentValue(0, "value", new ByRefRef(valueType), 64);
        var clearMethod = Method("Clear", reference.Type, types.Void);
        var ret = new ManagedReturn(0x1020, null);
        void Unchanged(string reason, params ManagedStatement[] statements)
        {
            var body = Body(clearMethod, statements);
            Require(ZeroInitialization.Recover(types, body).Blocks[0].Statements.SequenceEqual(statements), reason);
        }
        Unchanged("部分覆盖不能清零整个值", Clear(reference, 0), Clear(reference, 1), ret);
        Unchanged("重复覆盖不能作为完整范围", Clear(reference, 0), Clear(reference, 1), Clear(reference, 1), Clear(reference, 2), ret);
        Unchanged("非零字段不能并入 default", Clear(reference, 0), Clear(reference, 1, 1), Clear(reference, 2), ret);
        Unchanged("错误字段宽度不能按完整字段处理", Clear(reference, 0) with { Target = Member(reference, value.Fields[0]) with { Width = 16 } }, Clear(reference, 1), Clear(reference, 2), ret);
        var local = new LocalValue(new Variable(Storage.Gpr(8), 1), types.Int32, 32);
        Unchanged("不能跨过读取", Clear(reference, 0), new ManagedAssignment(0x1004, local, Member(reference, value.Fields[0])), Clear(reference, 1), Clear(reference, 2), ret);
        Unchanged("不能跨过调用", Clear(reference, 0), new ManagedCall(0x1004, new(clearMethod, null, [reference]), null, false), Clear(reference, 1), Clear(reference, 2), ret);
        var other = new ArgumentValue(1, "other", reference.Type, 64);
        Unchanged("不同引用可能别名，不能跨过其写入", Clear(reference, 0), Clear(other, 0), Clear(reference, 1), Clear(reference, 2), ret);
        Unchanged("不能跨控制流", Clear(reference, 0), new ManagedJump(0x1004, new(0x2000, [])), Clear(reference, 1), Clear(reference, 2), ret);
        foreach (var variant in new[] { "Padding", "Overlap", "Unknown", "Reference" })
        {
            var invalid = Type(variant, true, 16); var invalidType = new DefinitionRef(invalid, []);
            invalid.Fields = variant switch
            {
                "Padding" => [Field(invalid, "a", types.Int32, 0), Field(invalid, "b", types.Int32, 8)],
                "Overlap" => [Field(invalid, "a", types.Int64, 0), Field(invalid, "b", types.Int64, 4)],
                "Unknown" => [Field(invalid, "a", types.Int64, 0), Field(invalid, "b", types.Int64, -1)],
                _ => [Field(invalid, "a", types.Int64, 0), Field(invalid, "b", types.Object, 8)],
            };
            var arg = new ArgumentValue(0, "value", new ByRefRef(invalidType), 64);
            var stores = invalid.Fields.Select(f => (ManagedStatement)new ManagedStore(0x1000, Member(arg, f), new ConstantValue(0, f.Type, types.Size(f.Type) * 8))).ToArray();
            Unchanged(variant + " 布局不合并", stores);
        }
        var objectArg = new ArgumentValue(0, "value", hostType, 64);
        var readOnlyHost = Type("ReadOnlyHost", false, 0); var readOnlyHostType = new DefinitionRef(readOnlyHost, []);
        readOnlyHost.Fields = [Field(readOnlyHost, "Value", valueType, 16)];
        var readOnlyTarget = Member(new ArgumentValue(0, "value", readOnlyHostType, 64), readOnlyHost.Fields[0]);
        Unchanged("不能在普通方法中写只读根字段", Clear(readOnlyTarget, 0), Clear(readOnlyTarget, 1), Clear(readOnlyTarget, 2), ret);
        var current = Member(objectArg, host.Fields[0]); var next = Member(objectArg, host.Fields[1]);
        var interleaved = Body(Method("Interleaved", hostType, types.Void), Clear(current, 2), Clear(next, 0), Clear(current, 0), Clear(current, 1), Clear(next, 1), Clear(next, 2), ret);
        var byRef = Body(clearMethod, Clear(reference, 2), Clear(reference, 0), Clear(reference, 1), ret);
        var byValue = new ArgumentValue(0, "value", valueType, 96);
        var argument = Body(Method("Argument", valueType, valueType), Clear(byValue, 2), Clear(byValue, 0), Clear(byValue, 1), new ManagedReturn(0x1020, byValue));
        var storage = new LocalValue(new Variable(Storage.Gpr(8), 2), valueType, 96);
        var localBody = Body(Method("Local", valueType, valueType), new ManagedAssignment(0x1000, storage, byValue), Clear(storage, 2), Clear(storage, 0), Clear(storage, 1), new ManagedReturn(0x1020, storage));
        var stack = new StackLocalValue(-16, valueType, 96);
        var stackBody = Body(Method("Stack", valueType, valueType), new ManagedStore(0x1000, stack, byValue), Clear(stack, 2), Clear(stack, 0), Clear(stack, 1), new ManagedReturn(0x1020, stack));
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ZeroChecks", new Version(1, 0)), "ZeroChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var target = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(target);
        TypeReference Reference(TypeRef type) => type is ByRefRef byRefType ? new ByReferenceType(Reference(byRefType.Element))
            : type == valueType ? module.ImportReference(typeof(LoadTarget)) : type == hostType ? module.ImportReference(typeof(Preview))
            : module.ImportReference(System.Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var fields = value.Fields.Concat(host.Fields).ToDictionary(f => f,
            f => module.ImportReference((f.Owner == value ? typeof(LoadTarget) : typeof(Preview)).GetField(f.Name)));
        var emitter = new BodyEmitter(types, Reference, f => fields[f.Field], m => throw new NotSupportedException(m.ToString()));
        foreach (var body in new[] { interleaved, byRef, argument, localBody, stackBody })
        {
            var recovered = ZeroInitialization.Recover(types, body);
            Require(recovered.Blocks[0].Statements.OfType<ManagedStore>().Count(s => s.Value is DefaultValue) == (body == interleaved ? 2 : 1), "仅用整值清零替换完整字段组");
            var mapped = new MethodDefinition(body.Method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(body.Method.Method.ReturnType));
            mapped.Parameters.Add(new ParameterDefinition(Reference(body.Method.Method.Parameters[0].Type))); target.Methods.Add(mapped);
            var problem = emitter.Emit(recovered, mapped); Require(problem is null, problem ?? body.Method.ToString());
        }
        using var stream = new MemoryStream(); assembly.Write(stream); ExecuteSynthetic(SR.Assembly.Load(stream.ToArray()));
        ObjectAllocationCheck.Source(assembly, ExecuteSynthetic, "zero-initialization-source-check");
        Console.WriteLine("整值清零 CIL/C# 通过：交错对象字段、引用、参数、局部及栈存储；不跨读取、调用、别名、控制流，不接受部分、重复、非零或未知布局");
    }

    private static void ExecuteSynthetic(SR.Assembly assembly)
    {
        var host = assembly.GetType("Checks.Harness", true)!;
        var initial = new LoadTarget(LoadKind.Fixture, int.MinValue, int.MaxValue);
        var clear = (ClearReference)host.GetMethod("Clear")!.CreateDelegate(typeof(ClearReference));
        var value = initial; clear(ref value); Empty(value); clear(ref value); Empty(value);
        foreach (var name in new[] { "Argument", "Local", "Stack" })
        {
            var run = (Func<LoadTarget, LoadTarget>)host.GetMethod(name)!.CreateDelegate(typeof(Func<LoadTarget, LoadTarget>));
            Empty(run(initial)); Require(initial.Id == int.MinValue && initial.ColorId == int.MaxValue, "按值传递不修改调用者值");
        }
        var reset = (Action<Preview>)host.GetMethod("Interleaved")!.CreateDelegate(typeof(Action<Preview>));
        var preview = new Preview { Current = initial, Next = initial };
        reset(preview); Empty(preview.Current); Empty(preview.Next); Require(preview.Guard == 12345, "范围外字段不变");
        var failed = Task.Run(() => reset(null!)); Task.WhenAny(failed).GetAwaiter().GetResult();
        Require(failed.Exception?.InnerException is NullReferenceException, "空对象仍抛异常");
    }

    private static void Native(RecoverySession session)
    {
        var methods = new ulong[] { 0x56f956c, 0x56f957c, 0x56ee0e4 }.Select(a => session.Model.Code[a].Single().Method).ToArray();
        Require(methods.Select(m => m.Method.Name).SequenceEqual(["OnEnable", "Initialize", "Dispose"]), "真实方法身份");
        var owner = methods[0].Method.Owner;
        Require(owner.FullName == "Sekai.Mysekai.MysekaiBlueprint3DPreview" && methods.All(m => m.Method.Owner == owner), "真实类型身份");
        var current = owner.Fields.Single(f => f.Name == "_currentLoadTarget"); var next = owner.Fields.Single(f => f.Name == "_nextLoadTarget");
        var renderer = owner.Fields.Single(f => f.Name == "_object3DPreview");
        var load = ((DefinitionRef)current.Type).Definition;
        Require(current.Offset == 0xdc && next.Offset == 0xe8 && session.Types.Size(current.Type) == 12 && next.Type == current.Type
            && load.Fields.Where(f => !f.IsStatic).Select(f => f.Offset).SequenceEqual([0, 4, 8])
            && load.Fields.All(f => (f.Attributes & SR.FieldAttributes.InitOnly) != 0), "原生写入精确覆盖两个 12 字节只读字段结构体");
        var bodies = methods.Select(m => BodyRecovery.Recover(session, session.Analyze(m, m.Method.Address))).ToArray();
        foreach (var recovered in bodies)
        {
            Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
            Require(recovered.Body!.Blocks.SelectMany(b => b.Statements).OfType<ManagedStore>().Count(s => s.Value is DefaultValue) == 2, "真实写入恢复为两个整值初始化");
        }
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeZeroChecks", new Version(1, 0)), "NativeZeroChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var target = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(target);
        TypeReference Reference(TypeRef type) => type == methods[0].DeclaringType ? module.ImportReference(typeof(Preview))
            : type == current.Type ? module.ImportReference(typeof(LoadTarget)) : type == load.Fields[0].Type ? module.ImportReference(typeof(LoadKind))
            : type == renderer.Type ? module.ImportReference(typeof(Renderer))
            : module.ImportReference(System.Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var fields = new Dictionary<FieldDef, FieldReference>
        {
            [current] = module.ImportReference(typeof(Preview).GetField(nameof(Preview.Current))),
            [next] = module.ImportReference(typeof(Preview).GetField(nameof(Preview.Next))),
            [renderer] = module.ImportReference(typeof(Preview).GetField(nameof(Preview.Renderer))),
        };
        foreach (var field in load.Fields) fields.Add(field, module.ImportReference(typeof(LoadTarget).GetField(field.Name)));
        var emitter = new BodyEmitter(session.Types, Reference, f => fields[f.Field], m => m.Method.Name == "Release" && m.DeclaringType == renderer.Type
            ? module.ImportReference(typeof(Renderer).GetMethod(nameof(Renderer.Release))) : throw new NotSupportedException(m.ToString()));
        foreach (var body in bodies.Select(b => b.Body!))
        {
            Require(body.Method.Method.Parameters.Count == 0 && body.Accessors.Count == 0 && body.Constructors.Count == 0, "无隐藏恢复依赖");
            var mapped = new MethodDefinition(body.Method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Void);
            mapped.Parameters.Add(new ParameterDefinition(Reference(body.Method.DeclaringType))); target.Methods.Add(mapped);
            var problem = emitter.Emit(body, mapped); Require(problem is null, problem ?? body.Method.ToString());
        }
        using var stream = new MemoryStream(); assembly.Write(stream); ExecuteNative(SR.Assembly.Load(stream.ToArray()));
        ObjectAllocationCheck.Source(assembly, ExecuteNative, "zero-initialization-source-check");
        Console.WriteLine("真实 MysekaiBlueprint3DPreview.OnEnable / Initialize / Dispose CIL/C# 通过：完整清零、重复调用、Release 观察顺序、调用异常和空对象；宿主替代 Unity 依赖");
    }

    private static void ExecuteNative(SR.Assembly assembly)
    {
        var host = assembly.GetType("Checks.Harness", true)!;
        foreach (var name in new[] { "OnEnable", "Initialize", "Dispose" })
        {
            var run = (Action<Preview>)host.GetMethod(name)!.CreateDelegate(typeof(Action<Preview>));
            var preview = new Preview(); var calls = 0;
            preview.Renderer = new Renderer { OnRelease = () => { Empty(preview.Current); Empty(preview.Next); calls++; } };
            for (var i = 0; i < 2; i++)
            {
                preview.Current = new(LoadKind.Blueprint, -1, int.MinValue); preview.Next = new(LoadKind.Fixture, 9, int.MaxValue);
                run(preview); Empty(preview.Current); Empty(preview.Next); Require(preview.Guard == 12345, "真实方法不改范围外字段");
            }
            Require(calls == (name == "Dispose" ? 2 : 0), "Release 调用次数和位置");
            var failed = Task.Run(() => run(null!)); Task.WhenAny(failed).GetAwaiter().GetResult();
            Require(failed.Exception?.InnerException is NullReferenceException, "空 this 仍抛异常");
            if (name != "Dispose") continue;
            preview.Current = new(LoadKind.Blueprint, 1, 2); preview.Next = new(LoadKind.Fixture, 3, 4); preview.Renderer = null;
            failed = Task.Run(() => run(preview)); Task.WhenAny(failed).GetAwaiter().GetResult();
            Require(failed.Exception?.InnerException is NullReferenceException, "空 Release 接收者异常不被吞掉"); Empty(preview.Current); Empty(preview.Next);
            preview.Current = new(LoadKind.Blueprint, 1, 2); preview.Next = new(LoadKind.Fixture, 3, 4);
            preview.Renderer = new Renderer { OnRelease = () => throw new InvalidOperationException("release") };
            failed = Task.Run(() => run(preview)); Task.WhenAny(failed).GetAwaiter().GetResult();
            Require(failed.Exception?.InnerException is InvalidOperationException, "Release 失败仍保留此前写入"); Empty(preview.Current); Empty(preview.Next);
        }
    }

    private static void Empty(LoadTarget value) => Require(value.LoadType == LoadKind.None && value.Id == 0 && value.ColorId == 0, "结构体完整清零");
    private static void Require(bool condition, string message) { if (!condition) throw new InvalidOperationException(message); }
}
