using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests.Execution;

internal static class BitReinterpretCheck
{
    [Command("bit-reinterpret", "浮点位重解释的实际写出、CLR 位型和拒绝边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var original = facts.Model;
        var types = new ManagedTypes(original, facts.Layouts);
        var moduleType = new TypeDef { Index = original.Types.Count, Assembly = "BitReinterpretCheck.dll", Namespace = "", Name = "<Module>", Token = 0,
            Attributes = SR.TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var owner = new TypeDef { Index = original.Types.Count + 1, Assembly = moduleType.Assembly, Namespace = "Tests", Name = "Bits", Token = 0,
            Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.Abstract | SR.TypeAttributes.Sealed, IsValueType = false, IsEnum = false, BaseType = types.Object };
        var methods = new List<MethodDef>();
        var bodies = new List<ManagedBody>();
        void Add(string name, TypeRef from, TypeRef to)
        {
            var method = new MethodDef { Index = original.Methods.Count + methods.Count, Owner = owner, Name = name, Token = 0,
                Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL, Slot = -1,
                ReturnType = to, Parameters = [new("value", from, 0, null, false)] };
            methods.Add(method);
            var value = new ConversionValue(ConvKind.Bitcast, new ArgumentValue(0, from, types.Bits(from)), to, types.Bits(to));
            bodies.Add(new(new(method, [], []), [new(0, [new ManagedReturn(0, value)])]));
        }
        Add("Float", types.UInt32, types.Single);
        Add("Word", types.Single, types.UInt32);
        Add("Double", types.UInt64, types.Double);
        Add("Long", types.Double, types.UInt64);
        owner.Methods = methods;
        var assembly = new AssemblyDef { Name = owner.Assembly, AssemblyName = "BitReinterpretCheck", Version = new(1, 0), Culture = "", PublicKey = [], Types = [moduleType, owner] };
        var model = new ProgramModel { Image = original.Image, MetadataVersion = original.MetadataVersion,
            Assemblies = [.. original.Assemblies, assembly], Types = [.. original.Types, moduleType, owner], Methods = [.. original.Methods, .. methods],
            Fields = original.Fields, RuntimeTypes = original.RuntimeTypes, MethodSpecs = original.MethodSpecs, FieldRefs = original.FieldRefs,
            StringLiterals = original.StringLiterals, Code = original.Code };
        var skeleton = new Skeleton(model);
        var emitter = new BodyEmitter(skeleton, types);
        var a = new Assertions();
        a.Equal(0, emitter.Emit(bodies).Count, "四种同宽浮点位重解释通过写出检查");
        foreach (var method in methods)
        {
            var instructions = skeleton.Method(method).Body.Instructions;
            a.True(instructions.Count(i => i.OpCode.Code == Code.Call && i.Operand is Mono.Cecil.MethodReference { DeclaringType.FullName: "System.BitConverter" }) == 1,
                "写出对应的 BCL 按位转换");
            a.True(instructions.All(i => i.OpCode.Code is not (Code.Ldloca or Code.Ldloca_S or Code.Ldobj)), "不使用不同类型的托管地址读取");
        }
        var invalid = bodies[0] with { Blocks = [new(0, [new ManagedReturn(0,
            new ConversionValue(ConvKind.Bitcast, new ArgumentValue(0, types.UInt32, 32), types.Double, 64))])] };
        a.Equal(1, emitter.Emit([invalid]).Count, "不同位宽不冒充按位转换");
        using var stream = new MemoryStream();
        skeleton.Assembly(owner.Assembly).Write(stream);
        var loaded = SR.Assembly.Load(stream.ToArray()).GetType("Tests.Bits")!;
        var floating = loaded.GetMethod("Float")!.CreateDelegate<Func<uint, float>>();
        var word = loaded.GetMethod("Word")!.CreateDelegate<Func<float, uint>>();
        var doubling = loaded.GetMethod("Double")!.CreateDelegate<Func<ulong, double>>();
        var wide = loaded.GetMethod("Long")!.CreateDelegate<Func<double, ulong>>();
        ulong[] samples = [0, 1, ulong.MaxValue, 0x80000000, 0x7f800000, 0xff800000, 0x7fc01234, 0x7f800001,
            0x8000000000000000, 0x7ff0000000000000, 0xfff0000000000000, 0x7ff8123456789abc, 0x7ff0000000000001];
        var random = new Random(71);
        foreach (var bits in samples.Concat(Enumerable.Range(0, 128).Select(_ => unchecked((ulong)random.NextInt64()))))
        {
            a.Equal((uint)bits, BitConverter.SingleToUInt32Bits(floating((uint)bits)), "整数到 float 保留完整位型");
            a.Equal((uint)bits, word(BitConverter.UInt32BitsToSingle((uint)bits)), "float 到整数保留完整位型");
            a.Equal(bits, BitConverter.DoubleToUInt64Bits(doubling(bits)), "整数到 double 保留完整位型");
            a.Equal(bits, wide(BitConverter.UInt64BitsToDouble(bits)), "double 到整数保留完整位型");
        }
        return a.Finish("bit-reinterpret");
    }
}
