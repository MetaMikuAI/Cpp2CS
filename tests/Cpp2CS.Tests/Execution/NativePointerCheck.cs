using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using SR = System.Reflection;

namespace Cpp2CS.Tests.Execution;

internal static class NativePointerCheck
{
    private unsafe delegate nint ReadPointer(char* value);
    private unsafe delegate char* ReturnPointer(nint value);

    [Command("native-pointer", "真实 CLR 核对指针传递、原生整数转换及零值", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static unsafe int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var original = facts.Model;
        var types = new ManagedTypes(original, facts.Layouts);
        var pointer = new PointerRef(types.Corlib("System.Char"));
        var moduleType = new TypeDef { Index = original.Types.Count, Assembly = "PointerCheck.dll", Namespace = "", Name = "<Module>", Token = 0,
            Attributes = SR.TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var owner = new TypeDef { Index = original.Types.Count + 1, Assembly = "PointerCheck.dll", Namespace = "Tests", Name = "Pointers", Token = 0,
            Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.Abstract | SR.TypeAttributes.Sealed, IsValueType = false, IsEnum = false, BaseType = types.Object };
        var methods = new List<MethodDef>();
        var bodies = new List<ManagedBody>();
        void Add(string name, TypeRef result, TypeRef? parameter, ManagedValue value)
        {
            var method = new MethodDef { Index = original.Methods.Count + methods.Count, Owner = owner, Name = name, Token = 0,
                Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL, Slot = -1,
                ReturnType = result, Parameters = parameter is null ? [] : [new("value", parameter, 0, null, false)] };
            methods.Add(method);
            bodies.Add(new(new(method, [], []), [new(0, [new ManagedReturn(0, value)])]));
        }
        Add("Read", types.IntPtr, pointer, new ConversionValue(ConvKind.Bitcast, new ArgumentValue(0, pointer, 64), types.IntPtr, 64));
        Add("Return", pointer, types.IntPtr, new ConversionValue(ConvKind.Bitcast, new ArgumentValue(0, types.IntPtr, 64), pointer, 64));
        Add("Copy", types.IntPtr, types.IntPtr, new ArgumentValue(0, types.IntPtr, 64));
        Add("Zero", types.IntPtr, null, new ConstantValue(0, types.IntPtr, 64));
        owner.Methods = methods;
        var assembly = new AssemblyDef { Name = owner.Assembly, AssemblyName = "PointerCheck", Version = new(1, 0), Culture = "", PublicKey = [], Types = [moduleType, owner] };
        var model = new ProgramModel { Image = original.Image, MetadataVersion = original.MetadataVersion,
            Assemblies = [.. original.Assemblies, assembly], Types = [.. original.Types, moduleType, owner], Methods = [.. original.Methods, .. methods],
            Fields = original.Fields, RuntimeTypes = original.RuntimeTypes, MethodSpecs = original.MethodSpecs, FieldRefs = original.FieldRefs,
            StringLiterals = original.StringLiterals, Code = original.Code };
        var skeleton = new Skeleton(model);
        var emitter = new BodyEmitter(skeleton, types);
        var a = new Assertions();
        a.Equal(0, emitter.Emit(bodies).Count, "指针值通过实际写出管线");
        var invalid = bodies[3] with { Blocks = [new(0, [new ManagedReturn(0, new ConstantValue(1234, types.IntPtr, 64))])] };
        a.Equal(1, emitter.Emit([invalid]).Count, "不把原生数值地址常量冒充可移植指针");
        a.True(!ManagedTypes.IsNativePointer(new ByRefRef(types.Int32)), "托管引用地址不参与非托管转换");
        a.True(!ManagedTypes.IsNativePointer(types.UInt64), "普通64位整数不自动获得指针身份");
        using var stream = new MemoryStream();
        skeleton.Assembly(owner.Assembly).Write(stream);
        var loaded = SR.Assembly.Load(stream.ToArray()).GetType("Tests.Pointers")!;
        var read = loaded.GetMethod("Read")!.CreateDelegate<ReadPointer>();
        var returned = loaded.GetMethod("Return")!.CreateDelegate<ReturnPointer>();
        var copy = loaded.GetMethod("Copy")!.CreateDelegate<Func<nint, nint>>();
        var zero = loaded.GetMethod("Zero")!.CreateDelegate<Func<nint>>();
        foreach (var bits in new ulong[] { 0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000, ulong.MaxValue })
        {
            var value = unchecked((nint)bits);
            a.Equal(value, read((char*)value), "指针转原生整数保留全部位");
            a.Equal(value, (nint)returned(value), "原生整数转指针保留全部位");
            a.Equal(value, copy(value), "参数返回原样传递");
        }
        a.Equal((nint)0, zero(), "零指针常量使用原生整数求值栈");
        return a.Finish("native-pointer");
    }
}
