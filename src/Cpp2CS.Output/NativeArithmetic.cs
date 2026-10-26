using Cpp2CS.Ir;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>ARM64 标量运算的 CIL 展开。输入各求值一次；采用 FPCR 默认模式（AH/DN/FZ 为 0）。</summary>
public static class NativeArithmetic
{
    /// <summary>FCVTZS/FCVTZU：NaN 为零，越界饱和；只对有效范围内的值使用 CIL 转换。</summary>
    public static void FloatToInteger(ILProcessor il, int from, int width, bool signed, Func<string, TypeReference>? corlib = null)
    {
        if (from is not (32 or 64) || width is not (32 or 64)) throw new ArgumentOutOfRangeException(nameof(width));
        var module = il.Body.Method.Module;
        var floating = corlib?.Invoke(from == 32 ? "System.Single" : "System.Double")
            ?? (from == 32 ? module.TypeSystem.Single : module.TypeSystem.Double);
        var input = new VariableDefinition(floating);
        il.Body.Variables.Add(input);
        void Bits(ulong value)
        {
            if (width == 32) il.Emit(OpCodes.Ldc_I4, unchecked((int)value));
            else il.Emit(OpCodes.Ldc_I8, unchecked((long)value));
        }
        void Bound(double value)
        {
            if (from == 32) il.Emit(OpCodes.Ldc_R4, (float)value);
            else il.Emit(OpCodes.Ldc_R8, value);
        }
        var number = Instruction.Create(OpCodes.Nop);
        var belowUpper = Instruction.Create(OpCodes.Nop);
        var convert = Instruction.Create(OpCodes.Nop);
        var done = Instruction.Create(OpCodes.Nop);
        il.Emit(OpCodes.Stloc, input);
        il.Emit(OpCodes.Ldloc, input); il.Emit(OpCodes.Ldloc, input); il.Emit(OpCodes.Ceq); il.Emit(OpCodes.Brtrue, number);
        Bits(0); il.Emit(OpCodes.Br, done); il.Append(number);
        var upper = Math.Pow(2, signed ? width - 1 : width);
        il.Emit(OpCodes.Ldloc, input); Bound(upper); il.Emit(OpCodes.Clt); il.Emit(OpCodes.Brtrue, belowUpper);
        Bits(signed ? (1UL << (width - 1)) - 1 : width == 64 ? ulong.MaxValue : uint.MaxValue);
        il.Emit(OpCodes.Br, done); il.Append(belowUpper);
        il.Emit(OpCodes.Ldloc, input); Bound(signed ? -upper : 0); il.Emit(OpCodes.Cgt); il.Emit(OpCodes.Brtrue, convert);
        Bits(signed ? 1UL << (width - 1) : 0); il.Emit(OpCodes.Br, done); il.Append(convert);
        il.Emit(OpCodes.Ldloc, input);
        il.Emit((width, signed) switch { (32, true) => OpCodes.Conv_I4, (32, false) => OpCodes.Conv_U4,
            (64, true) => OpCodes.Conv_I8, _ => OpCodes.Conv_U8 });
        il.Append(done);
    }

    public static void Emit(ILProcessor il, BinOp operation, int width, Func<string, TypeReference>? corlib = null,
        Func<string, MethodReference>? bitConverter = null)
    {
        if (width is not (32 or 64)) throw new ArgumentOutOfRangeException(nameof(width));
        var module = il.Body.Method.Module;
        var integer = corlib?.Invoke(width == 32 ? "System.UInt32" : "System.UInt64") ?? (width == 32 ? module.TypeSystem.UInt32 : module.TypeSystem.UInt64);
        var floating = corlib?.Invoke(width == 32 ? "System.Single" : "System.Double") ?? (width == 32 ? module.TypeSystem.Single : module.TypeSystem.Double);
        VariableDefinition Local(TypeReference type)
        {
            var local = new VariableDefinition(type);
            il.Body.Variables.Add(local);
            return local;
        }
        void Bits(ulong value)
        {
            if (width == 32) il.Emit(OpCodes.Ldc_I4, unchecked((int)value));
            else il.Emit(OpCodes.Ldc_I8, unchecked((long)value));
        }
        var done = Instruction.Create(OpCodes.Nop);
        if (operation is BinOp.SDiv or BinOp.UDiv)
        {
            var type = operation == BinOp.SDiv ? corlib?.Invoke(width == 32 ? "System.Int32" : "System.Int64") ?? (width == 32 ? module.TypeSystem.Int32 : module.TypeSystem.Int64) : integer;
            var left = Local(type); var right = Local(type);
            il.Emit(OpCodes.Stloc, right); il.Emit(OpCodes.Stloc, left);
            var nonzero = Instruction.Create(OpCodes.Nop);
            il.Emit(OpCodes.Ldloc, right); il.Emit(OpCodes.Brtrue, nonzero);
            Bits(0); il.Emit(OpCodes.Br, done); il.Append(nonzero);
            if (operation == BinOp.SDiv)
            {
                var divide = Instruction.Create(OpCodes.Nop);
                il.Emit(OpCodes.Ldloc, right); Bits(ulong.MaxValue); il.Emit(OpCodes.Ceq); il.Emit(OpCodes.Brfalse, divide);
                // ARM64 的最小整数 / -1 回绕；CIL div 会抛出，因此使用不检查溢出的 neg。
                il.Emit(OpCodes.Ldloc, left); il.Emit(OpCodes.Neg); il.Emit(OpCodes.Br, done); il.Append(divide);
            }
            il.Emit(OpCodes.Ldloc, left); il.Emit(OpCodes.Ldloc, right);
            il.Emit(operation == BinOp.SDiv ? OpCodes.Div : OpCodes.Div_Un);
            il.Append(done);
            return;
        }
        if (operation is not (BinOp.FMin or BinOp.FMax)) throw new ArgumentOutOfRangeException(nameof(operation));
        var x = Local(floating); var y = Local(floating);
        var xb = Local(integer); var yb = Local(integer);
        MethodReference ConvertBits(bool toInteger)
        {
            var name = (width, toInteger) switch { (32, true) => "SingleToInt32Bits", (64, true) => "DoubleToInt64Bits", (32, false) => "Int32BitsToSingle", _ => "Int64BitsToDouble" };
            if (bitConverter is not null) return bitConverter(name);
            var signed = width == 32 ? module.TypeSystem.Int32 : module.TypeSystem.Int64;
            var reference = new MethodReference(name, toInteger ? signed : floating, new TypeReference("System", "BitConverter", module, module.TypeSystem.CoreLibrary));
            reference.Parameters.Add(new ParameterDefinition(toInteger ? floating : signed));
            return reference;
        }
        il.Emit(OpCodes.Stloc, y); il.Emit(OpCodes.Stloc, x);
        il.Emit(OpCodes.Ldloc, x); il.Emit(OpCodes.Call, ConvertBits(true)); il.Emit(OpCodes.Stloc, xb);
        il.Emit(OpCodes.Ldloc, y); il.Emit(OpCodes.Call, ConvertBits(true)); il.Emit(OpCodes.Stloc, yb);
        var unequal = Instruction.Create(OpCodes.Nop);
        il.Emit(OpCodes.Ldloc, x); il.Emit(OpCodes.Ldloc, y); il.Emit(OpCodes.Ceq); il.Emit(OpCodes.Brfalse, unequal);
        // 相等的有限数位型相同；对 ±0，min 取符号位 OR，max 取 AND。
        il.Emit(OpCodes.Ldloc, xb); il.Emit(OpCodes.Ldloc, yb);
        il.Emit(operation == BinOp.FMin ? OpCodes.Or : OpCodes.And);
        Result(); il.Emit(OpCodes.Br, done); il.Append(unequal);
        var absolute = width == 32 ? 0x7fffffffUL : 0x7fffffffffffffffUL;
        var infinity = width == 32 ? 0x7f800000UL : 0x7ff0000000000000UL;
        var quiet = width == 32 ? 0x00400000UL : 0x0008000000000000UL;
        // Arm FPProcessNaNs：先左 sNaN，再右 sNaN，再左 qNaN，最后右 qNaN，保留载荷并置 quiet 位。
        foreach (var signaling in new[] { true, false })
            foreach (var bits in new[] { xb, yb })
            {
                var next = Instruction.Create(OpCodes.Nop);
                il.Emit(OpCodes.Ldloc, bits); Bits(absolute); il.Emit(OpCodes.And); Bits(infinity); il.Emit(OpCodes.Cgt_Un); il.Emit(OpCodes.Brfalse, next);
                if (signaling) { il.Emit(OpCodes.Ldloc, bits); Bits(quiet); il.Emit(OpCodes.And); il.Emit(OpCodes.Brtrue, next); }
                il.Emit(OpCodes.Ldloc, bits); Bits(quiet); il.Emit(OpCodes.Or); Result(); il.Emit(OpCodes.Br, done); il.Append(next);
            }
        var second = Instruction.Create(OpCodes.Nop);
        il.Emit(OpCodes.Ldloc, x); il.Emit(OpCodes.Ldloc, y);
        il.Emit(operation == BinOp.FMin ? OpCodes.Clt : OpCodes.Cgt); il.Emit(OpCodes.Brfalse, second);
        il.Emit(OpCodes.Ldloc, x); il.Emit(OpCodes.Br, done); il.Append(second); il.Emit(OpCodes.Ldloc, y); il.Append(done);
        void Result() => il.Emit(OpCodes.Call, ConvertBits(false));
    }
}
