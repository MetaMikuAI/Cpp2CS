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

    private static unsafe ulong PinnedReference(byte[] data, long offset, Action collect)
    {
        fixed (byte* start = data)
        {
            collect();
            return *(ulong*)(start + offset);
        }
    }

    [Command("native-pointer", "真实 CLR 核对指针、数组固定及压缩 GC 后的非对齐访问", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
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
        MethodDef Add(string name, TypeRef result, TypeRef? parameter, ManagedValue value)
        {
            var method = new MethodDef { Index = original.Methods.Count + methods.Count, Owner = owner, Name = name, Token = 0,
                Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL, Slot = -1,
                ReturnType = result, Parameters = parameter is null ? [] : [new("value", parameter, 0, null, false)] };
            methods.Add(method);
            bodies.Add(new(new(method, [], []), [new(0, [new ManagedReturn(0, value)])]));
            return method;
        }
        Add("Read", types.IntPtr, pointer, new ConversionValue(ConvKind.Bitcast, new ArgumentValue(0, pointer, 64), types.IntPtr, 64));
        Add("Return", pointer, types.IntPtr, new ConversionValue(ConvKind.Bitcast, new ArgumentValue(0, types.IntPtr, 64), pointer, 64));
        Add("Copy", types.IntPtr, types.IntPtr, new ArgumentValue(0, types.IntPtr, 64));
        Add("Zero", types.IntPtr, null, new ConstantValue(0, types.IntPtr, 64));
        var array = new ArrayRef(types.Byte, 1) { IsVector = true };
        var input = new ArgumentValue(0, array, 64);
        Add("PinnedZero", types.IntPtr, array, new ConversionValue(ConvKind.Bitcast, new PinnedArrayValue(input, array), types.IntPtr, 64));
        var pinnedMethod = Add("PinnedBits", types.UInt64, array, new ConstantValue(0, types.UInt64, 64));
        var action = types.Corlib("System.Action");
        var invoke = types.CorlibMethod("System.Action", "Invoke")!;
        pinnedMethod.Parameters = [new("array", array, 0, null, false), new("offset", types.Int64, 0, null, false), new("collect", action, 0, null, false)];
        var start = new LocalValue(new Variable(Storage.Gpr(0), 1), new PointerRef(types.Byte), 64);
        var location = new IndirectValue(new PointerOffsetValue(start, new ArgumentValue(1, types.Int64, 64)), types.UInt64, 64);
        const ulong mask = 0x123456789abcdef0;
        bodies[^1] = new(new(pinnedMethod, [], []), [new(0,
        [
            new ManagedAssignment(0, start, new PinnedArrayValue(input, array)),
            new ManagedCall(0, new(invoke, new ArgumentValue(2, action, 64), [], true), null, false),
            new ManagedStore(0, location, new BinaryValue(BinOp.Xor, location, new ConstantValue(mask, types.UInt64, 64), types.UInt64, 64)),
            new ManagedReturn(0, location),
        ])]);
        owner.Methods = methods;
        var assembly = new AssemblyDef { Name = owner.Assembly, AssemblyName = "PointerCheck", Version = new(1, 0), Culture = "", PublicKey = [], Types = [moduleType, owner] };
        var model = new ProgramModel { Image = original.Image, MetadataVersion = original.MetadataVersion,
            Assemblies = [.. original.Assemblies, assembly], Types = [.. original.Types, moduleType, owner], Methods = [.. original.Methods, .. methods],
            Fields = original.Fields, RuntimeTypes = original.RuntimeTypes, MethodSpecs = original.MethodSpecs, FieldRefs = original.FieldRefs,
            StringLiterals = original.StringLiterals, Code = original.Code };
        var skeleton = new Skeleton(model);
        var emitter = new FullBodyEmitter(skeleton, types);
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
        var pinnedZero = loaded.GetMethod("PinnedZero")!.CreateDelegate<Func<byte[]?, nint>>();
        var pinnedBits = loaded.GetMethod("PinnedBits")!.CreateDelegate<Func<byte[], long, Action, ulong>>();
        foreach (var bits in new ulong[] { 0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000, ulong.MaxValue })
        {
            var value = unchecked((nint)bits);
            a.Equal(value, read((char*)value), "指针转原生整数保留全部位");
            a.Equal(value, (nint)returned(value), "原生整数转指针保留全部位");
            a.Equal(value, copy(value), "参数返回原样传递");
        }
        a.Equal((nint)0, zero(), "零指针常量使用原生整数求值栈");
        a.Equal((nint)0, pinnedZero(null), "固定 null 数组得到零指针");
        a.Equal((nint)0, pinnedZero([]), "固定空数组得到零指针");
        foreach (var offset in new[] { 0, 1, 7 })
        {
            var buffer = Enumerable.Range(0, 32).Select(i => (byte)i).ToArray();
            var expected = buffer.ToArray();
            var changed = BitConverter.ToUInt64(buffer, offset) ^ mask;
            a.Equal(BitConverter.ToUInt64(buffer, offset), PinnedReference(buffer, offset, () => GC.Collect(2, GCCollectionMode.Forced, true, true)), "C# 编译器固定数组参考");
            BitConverter.GetBytes(changed).CopyTo(expected, offset);
            a.Equal(changed, pinnedBits(buffer, offset, () => GC.Collect(2, GCCollectionMode.Forced, true, true)), "压缩 GC 后按字节偏移读写完整64位");
            a.True(buffer.SequenceEqual(expected), "固定指针写入不改变相邻字节");
        }
        return a.Finish("native-pointer");
    }
}
