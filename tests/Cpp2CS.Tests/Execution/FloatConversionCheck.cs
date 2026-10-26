using Cpp2CS.Ir;
using Cpp2CS.Output;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static class FloatConversionCheck
{
    [Command("float-conversions", "浮点转整数的 CLR/ARM64 边界与随机对照", Gate = Gate.Unit)]
    public static int Run()
    {
        using var module = ModuleDefinition.CreateModule("ConversionCheck", ModuleKind.Dll);
        var owner = new TypeDefinition("Tests", "Conversions", TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed, module.TypeSystem.Object);
        module.Types.Add(owner);
        foreach (var from in new[] { 32, 64 })
            foreach (var width in new[] { 32, 64 })
                foreach (var signed in new[] { false, true })
                {
                    var method = new MethodDefinition($"Convert{from}_{width}_{signed}", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.UInt64);
                    owner.Methods.Add(method);
                    var floating = from == 32 ? module.TypeSystem.Single : module.TypeSystem.Double;
                    method.Parameters.Add(new("bits", ParameterAttributes.None, from == 32 ? module.TypeSystem.UInt32 : module.TypeSystem.UInt64));
                    var il = method.Body.GetILProcessor();
                    il.Emit(OpCodes.Ldarga, method.Parameters[0]); il.Emit(OpCodes.Ldobj, floating);
                    NativeArithmetic.FloatToInteger(il, from, width, signed);
                    if (width == 32) il.Emit(OpCodes.Conv_U8);
                    il.Emit(OpCodes.Ret);
                }
        using var stream = new MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray()).GetType("Tests.Conversions")!;
        using var arm = new Unicorn();
        arm.Map(0x1000, 0x1000);
        var a = new Assertions();
        ulong pc = 0x1000;
        foreach (var from in new[] { 32, 64 })
            foreach (var width in new[] { 32, 64 })
                foreach (var signed in new[] { false, true })
                {
                    var method = loaded.GetMethod($"Convert{from}_{width}_{signed}")!;
                    Func<ulong, ulong> invoke;
                    if (from == 32)
                    {
                        var function = method.CreateDelegate<Func<uint, ulong>>();
                        invoke = bits => function((uint)bits);
                    }
                    else invoke = method.CreateDelegate<Func<ulong, ulong>>();
                    var instruction = 0x1e380000u | (from == 64 ? 1u << 22 : 0) | (width == 64 ? 1u << 31 : 0) | (signed ? 0 : 1u << 16);
                    pc += 4;
                    arm.Write(pc, BitConverter.GetBytes(instruction));
                    var upper = Math.Pow(2, signed ? width - 1 : width);
                    var values = new[] { 0d, -0d, 0.9, -0.9, 1.9, -1.9, 1000d, -1000d, double.PositiveInfinity, double.NegativeInfinity, double.NaN,
                        upper, -upper, Math.BitDecrement(upper), Math.BitIncrement(upper), Math.BitDecrement(-upper), Math.BitIncrement(-upper) };
                    var bits = values.Select(v => from == 32 ? BitConverter.SingleToUInt32Bits((float)v) : BitConverter.DoubleToUInt64Bits(v)).ToList();
                    if (from == 32) bits.AddRange([BitConverter.SingleToUInt32Bits(float.BitDecrement((float)upper)),
                        BitConverter.SingleToUInt32Bits(float.BitIncrement((float)upper)), BitConverter.SingleToUInt32Bits(float.BitDecrement((float)-upper)),
                        BitConverter.SingleToUInt32Bits(float.BitIncrement((float)-upper)), 0x7f800001, 0xff800001]);
                    else bits.AddRange([0x7ff0000000000001, 0xfff0000000000001]);
                    var random = new Random(41);
                    bits.AddRange(Enumerable.Range(0, 128).Select(_ => BitConverter.ToUInt64(RandomBytes(random)) & Expr.Mask(from)));
                    foreach (var input in bits.Distinct())
                    {
                        arm.SetReg(from == 32 ? Unicorn.S(0) : Unicorn.D(0), input);
                        var error = arm.Start(pc, 1);
                        if (error != 0) throw new InvalidOperationException(Unicorn.Error(error));
                        a.Equal(arm.Reg(Unicorn.X(0)) & Expr.Mask(width), invoke(input), $"{from}→{width} signed={signed} 0x{input:x}");
                    }
                }
        return a.Finish("float-conversions");
    }

    private static byte[] RandomBytes(Random random)
    {
        var bytes = new byte[8];
        random.NextBytes(bytes);
        return bytes;
    }
}
