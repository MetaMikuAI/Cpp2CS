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
        uint[] samples = [0, 0x80000000, 1, 0x80000001, 0x007fffff, 0x00800000, 0x3f800000, 0xbf800000,
            0x40490fdb, 0x7f7fffff, 0xff7fffff, 0x7f800000, 0xff800000, 0x7fc12345];
        foreach (var bits in samples)
        {
            var value = BitConverter.UInt32BitsToSingle(bits);
            a.Equal(BitConverter.SingleToUInt32Bits(NativeMathLibrary.Sinf(value)), BitConverter.SingleToUInt32Bits(invoke(value)), $"CLR 调用位型 {bits:x8}");
        }
        return a.Finish("native-import");
    }
}
