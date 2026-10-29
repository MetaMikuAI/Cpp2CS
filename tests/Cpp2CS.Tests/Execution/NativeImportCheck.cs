using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil;
using System.Runtime.InteropServices;
using SR = System.Reflection;

namespace Cpp2CS.Tests.Execution;

internal static class NativeImportCheck
{
    [Command("native-import", "原生导入签名、写盘及 CLR 单精度调用检查", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var skeleton = new Skeleton(facts.Model);
        using var module = ModuleDefinition.CreateModule("NativeImportCheck", ModuleKind.Dll);
        var owner = new TypeDef { Index = -1, Assembly = module.Name, Namespace = "Tests", Name = "Imports", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodDef { Index = -1, Owner = owner, Name = "sinf", Token = 0, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.PreserveSig, Slot = -1, ReturnType = types.Single,
            Parameters = [new("value", types.Single, 0, null, false)], NativeImport = new("libm.so", "sinf") };
        var reference = new MethodRef(method, [], []);
        var declaration = (MethodDefinition)skeleton.Reference(module, reference, null, null);
        var a = new Assertions();
        a.True(declaration.IsPInvokeImpl && !declaration.HasBody && declaration.IsPreserveSig && declaration.PInvokeInfo.IsCallConvCdecl
            && declaration.PInvokeInfo.IsNoMangle, "真实 extern C ABI 声明");
        a.True(ReferenceEquals(declaration, skeleton.Reference(module, reference, null, null)), "重复调用共用导入声明");
        a.Equal("System.Single", declaration.ReturnType.FullName, "返回值保留 float");
        a.Equal("System.Single", declaration.Parameters.Single().ParameterType.FullName, "实参保留 float");
        var caller = new MethodDefinition("Call", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Single);
        caller.Parameters.Add(new("value", 0, module.TypeSystem.Single));
        declaration.DeclaringType.Methods.Add(caller);
        var il = caller.Body.GetILProcessor();
        il.Emit(Mono.Cecil.Cil.OpCodes.Ldarg_0); il.Emit(Mono.Cecil.Cil.OpCodes.Call, declaration); il.Emit(Mono.Cecil.Cil.OpCodes.Ret);
        var fingerprint = CilBodyFingerprint.Describe(caller);
        declaration.PInvokeInfo.EntryPoint = "cosf";
        a.True(!fingerprint.SequenceEqual(CilBodyFingerprint.Describe(caller)), "调用身份包含导入符号");
        declaration.PInvokeInfo.EntryPoint = "sinf";
        var remainder = new MethodDef { Index = -1, Owner = owner, Name = "fmodf", Token = 0, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.PreserveSig, Slot = -1, ReturnType = types.Single,
            Parameters = [new("value", types.Single, 0, null, false), new("divisor", types.Single, 0, null, false)], NativeImport = new("libm.so", "fmodf") };
        var remainderDeclaration = (MethodDefinition)skeleton.Reference(module, new MethodRef(remainder, [], []), null, null);
        a.True(remainderDeclaration.Parameters is [{ ParameterType.FullName: "System.Single" }, { ParameterType.FullName: "System.Single" }]
            && remainderDeclaration.PInvokeInfo.IsCallConvCdecl && remainderDeclaration.PInvokeInfo.EntryPoint == "fmodf", "双实参单精度 C ABI 声明");
        MethodDefinition Declare(string name, TypeRef scalar, string[] parameters)
        {
            var imported = new MethodDef { Index = -1, Owner = owner, Name = name, Token = 0,
                Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.PreserveSig,
                Slot = -1, ReturnType = scalar, Parameters = parameters.Select(p => new ParameterDef(p, scalar, 0, null, false)).ToArray(),
                NativeImport = new("libm.so", name) };
            return (MethodDefinition)skeleton.Reference(module, new MethodRef(imported, [], []), null, null);
        }
        var powerDeclaration = Declare("powf", types.Single, ["value", "power"]);
        var acosDeclaration = Declare("acos", types.Double, ["value"]);
        Declare("tanf", types.Single, ["value"]);
        Declare("atan2f", types.Single, ["y", "x"]);
        Declare("atan2", types.Double, ["y", "x"]);
        a.True(powerDeclaration.Parameters.Count == 2 && powerDeclaration.ReturnType.FullName == "System.Single"
            && acosDeclaration.Parameters.Single().ParameterType.FullName == "System.Double" && acosDeclaration.ReturnType.FullName == "System.Double",
            "powf 保留单精度，acos 保留双精度");
        using var stream = new MemoryStream();
        module.Write(stream);
        stream.Position = 0;
        using var saved = ModuleDefinition.ReadModule(stream);
        var savedType = saved.Types.Single(t => t.Name == "NativeImports");
        var savedMethod = savedType.Methods.Single(m => m.Name == "sinf");
        a.True(fingerprint.SequenceEqual(CilBodyFingerprint.Describe(savedType.Methods.Single(m => m.Name == "Call"))), "导入调用身份写盘不变");
        a.Equal("libm.so", savedMethod.PInvokeInfo.Module.Name, "写盘保留库名");
        a.Equal("sinf", savedMethod.PInvokeInfo.EntryPoint, "写盘保留符号");
        var loaded = SR.Assembly.Load(stream.ToArray());
        NativeLibrary.SetDllImportResolver(loaded, (library, _, _) => library == "libm.so" ? NativeMathLibrary.Library : IntPtr.Zero);
        var invoke = loaded.GetType("Cpp2CS.NativeImports")!.GetMethod("sinf")!.CreateDelegate<Func<float, float>>();
        var remainderInvoke = loaded.GetType("Cpp2CS.NativeImports")!.GetMethod("fmodf")!.CreateDelegate<Func<float, float, float>>();
        var powerInvoke = loaded.GetType("Cpp2CS.NativeImports")!.GetMethod("powf")!.CreateDelegate<Func<float, float, float>>();
        var acosInvoke = loaded.GetType("Cpp2CS.NativeImports")!.GetMethod("acos")!.CreateDelegate<Func<double, double>>();
        var tanInvoke = loaded.GetType("Cpp2CS.NativeImports")!.GetMethod("tanf")!.CreateDelegate<Func<float, float>>();
        var atanSingleInvoke = loaded.GetType("Cpp2CS.NativeImports")!.GetMethod("atan2f")!.CreateDelegate<Func<float, float, float>>();
        var atanDoubleInvoke = loaded.GetType("Cpp2CS.NativeImports")!.GetMethod("atan2")!.CreateDelegate<Func<double, double, double>>();
        uint[] samples = [0, 0x80000000, 1, 0x80000001, 0x007fffff, 0x00800000, 0x3f800000, 0xbf800000,
            0x40490fdb, 0x7f7fffff, 0xff7fffff, 0x7f800000, 0xff800000, 0x7fc12345];
        foreach (var bits in samples)
        {
            var value = BitConverter.UInt32BitsToSingle(bits);
            a.Equal(BitConverter.SingleToUInt32Bits(NativeMathLibrary.Sinf(value)), BitConverter.SingleToUInt32Bits(invoke(value)), $"CLR 调用位型 {bits:x8}");
            a.Equal(BitConverter.SingleToUInt32Bits(NativeMathLibrary.Tanf(value)), BitConverter.SingleToUInt32Bits(tanInvoke(value)), "正切 CLR 调用位型");
            foreach (var divisorBits in samples)
            {
                var divisor = BitConverter.UInt32BitsToSingle(divisorBits);
                a.Equal(BitConverter.SingleToUInt32Bits(NativeMathLibrary.Fmodf(value, divisor)),
                    BitConverter.SingleToUInt32Bits(remainderInvoke(value, divisor)), $"双实参 CLR 调用位型 {bits:x8}, {divisorBits:x8}");
                a.Equal(BitConverter.SingleToUInt32Bits(NativeMathLibrary.Powf(value, divisor)),
                    BitConverter.SingleToUInt32Bits(powerInvoke(value, divisor)), $"幂运算 CLR 调用位型 {bits:x8}, {divisorBits:x8}");
                a.Equal(BitConverter.SingleToUInt32Bits(NativeMathLibrary.Atan2f(value, divisor)),
                    BitConverter.SingleToUInt32Bits(atanSingleInvoke(value, divisor)), "单精度反正切保留实参顺序及符号");
            }
        }
        foreach (var bits in new ulong[] { 0, 0x8000000000000000, 1, 0x3fe0000000000000, 0x3ff0000000000000,
            0xbff0000000000000, 0x4000000000000000, 0x7ff0000000000000, 0x7ff8000000000123 })
        {
            var value = BitConverter.UInt64BitsToDouble(bits);
            a.Equal(BitConverter.DoubleToUInt64Bits(NativeMathLibrary.Acos(value)), BitConverter.DoubleToUInt64Bits(acosInvoke(value)),
                "反余弦 CLR 调用保留双精度与边界位型");
            foreach (var x in new[] { -1.0, -0.0, 0.0, 1.0, double.PositiveInfinity, double.NaN })
                a.Equal(BitConverter.DoubleToUInt64Bits(NativeMathLibrary.Atan2(value, x)), BitConverter.DoubleToUInt64Bits(atanDoubleInvoke(value, x)),
                    "双精度反正切保留实参顺序及有符号零");
        }
        return a.Finish("native-import");
    }
}
