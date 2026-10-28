using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests.Execution;

internal static class SharedValueEmissionCheck
{
    private delegate string Describe<T>(ref T value);
    public struct MutableValue { public int Value; public override string ToString() => (++Value).ToString(); }

    [Command("shared-value-emission", "泛型拆箱及受约束调用的实际 CIL 与 CLR 行为", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var original = facts.Model; var types = new ManagedTypes(original, facts.Layouts);
        var module = new TypeDef { Index = original.Types.Count, Assembly = "SharedValueCheck.dll", Namespace = "", Name = "<Module>", Token = 0,
            Attributes = SR.TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var owner = new TypeDef { Index = original.Types.Count + 1, Assembly = module.Assembly, Namespace = "Tests", Name = "Values", Token = 0,
            Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.Abstract | SR.TypeAttributes.Sealed, IsValueType = false, IsEnum = false, BaseType = types.Object };
        var parameter = new GenericParameterDef { Name = "T", Position = 0, Attributes = SR.GenericParameterAttributes.None };
        var generic = new GenericParameterRef("T", true, 0) { Parameter = parameter };
        MethodDef Method(string name, int index, TypeRef result, TypeRef argument) => new() { Index = original.Methods.Count + index, Owner = owner, Name = name, Token = 0,
            Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL, Slot = -1,
            GenericParameters = [parameter], ReturnType = result, Parameters = [new("value", argument, 0, null, false)] };
        var cast = Method("Cast", 0, generic, types.Object);
        var describe = Method("Describe", 1, types.String, new ByRefRef(generic));
        owner.Methods = [cast, describe];
        var contract = MethodRef.Open(types.CorlibDefinition("System.Object")!.Methods.Single(m => m.Name == "ToString" && m.Parameters.Count == 0));
        var local = new LocalValue(new(Storage.Temp(0), 1), types.String, 64);
        var receiver = new ArgumentValue(0, new ByRefRef(generic), 64);
        var castBody = new ManagedBody(MethodRef.Open(cast), [new(0, [new ManagedReturn(0, new UnboxValue(new ArgumentValue(0, types.Object, 64), generic, 0))])]);
        var describeBody = new ManagedBody(MethodRef.Open(describe), [new(0, [new ManagedCall(0, new(contract, receiver, [], true) { Constraint = generic }, local, false), new ManagedReturn(4, local)])]);
        var assembly = new AssemblyDef { Name = owner.Assembly, AssemblyName = "SharedValueCheck", Version = new(1, 0), Culture = "", PublicKey = [], Types = [module, owner] };
        var model = new ProgramModel { Image = original.Image, MetadataVersion = original.MetadataVersion, Assemblies = [.. original.Assemblies, assembly],
            Types = [.. original.Types, module, owner], Methods = [.. original.Methods, cast, describe], Fields = original.Fields, RuntimeTypes = original.RuntimeTypes,
            MethodSpecs = original.MethodSpecs, FieldRefs = original.FieldRefs, StringLiterals = original.StringLiterals, Code = original.Code };
        var skeleton = new Skeleton(model); var emitter = new BodyEmitter(skeleton, types); var a = new Assertions();
        var unboxers = facts.Code.Functions.Where(f => f.Size == 196 && SharedRuntimeHelpers.UnboxAny(facts, f.Start)).ToArray();
        var invokers = facts.Code.Functions.Where(f => f.Size == 272 && SharedRuntimeHelpers.ConstrainedInvoke(facts, f.Start)).ToArray();
        a.True(unboxers.Length > 0 && invokers.Length > 0, "运行时模板与内部调用身份完整匹配");
        foreach (var function in unboxers) a.True(!SharedRuntimeHelpers.UnboxAny(facts, function.Start + 4), "不能从拆箱模板中间开始");
        foreach (var function in invokers) a.True(!SharedRuntimeHelpers.ConstrainedInvoke(facts, function.Start + 4), "不能从调用模板中间开始");
        foreach (var (name, kind) in new[] { ("il2cpp_value_box", HelperKind.Box), ("il2cpp_object_unbox", HelperKind.Unbox),
            ("il2cpp_object_get_virtual_method", HelperKind.VirtualMethodLookup), ("il2cpp_runtime_class_init", HelperKind.ClassInit) })
            if (facts.Code.Image.Exports.TryGetValue(name, out var export) && facts.Code.Word(export) is { } jump && A64.IsB(jump))
                a.Equal(kind, facts.Helpers.InternalCall(A64.Imm26Target(jump, export)).Kind, "导出直达实现保留身份");
        a.Equal(0, emitter.Emit([castBody, describeBody]).Count, "共享值写出成功");
        a.True(skeleton.Method(cast).Body.Instructions.Any(i => i.OpCode.Code == Code.Unbox_Any), "按值拆箱使用 unbox.any");
        a.True(skeleton.Method(describe).Body.Instructions.Any(i => i.OpCode.Code == Code.Constrained), "受约束前缀保留");
        var wrong = describeBody with { Blocks = [new(0, [new ManagedCall(0, new(contract, receiver, [], false) { Constraint = generic }, local, false), new ManagedReturn(4, local)])] };
        a.Equal(1, emitter.Emit([wrong]).Count, "不允许 constrained 配合普通 call");
        using var stream = new MemoryStream(); skeleton.Assembly(owner.Assembly).Write(stream);
        var loaded = SR.Assembly.Load(stream.ToArray()).GetType("Tests.Values")!;
        Func<object, T> Cast<T>() => loaded.GetMethod("Cast")!.MakeGenericMethod(typeof(T)).CreateDelegate<Func<object, T>>();
        Describe<T> Text<T>() => loaded.GetMethod("Describe")!.MakeGenericMethod(typeof(T)).CreateDelegate<Describe<T>>();
        a.Equal(42, Cast<int>()(42), "值类型拆箱");
        a.Equal("text", Cast<string>()("text"), "引用类型转换");
        a.True(Cast<string>()(null!) is null, "引用类型 null 保留");
        a.Equal((int?)42, Cast<int?>()(42), "Nullable 有值");
        a.True(Cast<int?>()(null!) is null, "Nullable 无值");
        a.Equal(DayOfWeek.Friday, Cast<DayOfWeek>()(DayOfWeek.Friday), "枚举拆箱");
        void Fails(Action operation, Type expected) => a.Equal(expected,
            Task.Run(operation).ContinueWith(task => task.Exception?.InnerException?.GetType()).GetAwaiter().GetResult(), "CLR 异常类型");
        Fails(() => Cast<int>()(null!), typeof(NullReferenceException));
        Fails(() => Cast<int>()("42"), typeof(InvalidCastException));
        Fails(() => Cast<int?>()(42L), typeof(InvalidCastException));
        var number = 42; a.Equal("42", Text<int>()(ref number), "值类型受约束调用");
        var word = "text"; a.Equal("text", Text<string>()(ref word), "引用类型虚调用");
        int? nullable = null; a.Equal("", Text<int?>()(ref nullable), "Nullable 无值 ToString");
        nullable = 42; a.Equal("42", Text<int?>()(ref nullable), "Nullable 有值 ToString");
        var mutable = new MutableValue { Value = 5 };
        a.Equal("6", Text<MutableValue>()(ref mutable), "结构体 override 调用");
        a.Equal(6, mutable.Value, "受约束调用修改原结构体而非装箱副本");
        Fails(() => { string missing = null!; Text<string>()(ref missing); }, typeof(NullReferenceException));
        return a.Finish("shared-value-emission");
    }
}
