using Cpp2CS.Ir;
using Cpp2CS.Arm64;
using Cpp2CS.Output;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static class NativeArithmeticCheck
{
    [Command("native-arithmetic", "真实 CLR 执行生成的数值 CIL，与独立 ARM64 指令逐位对照", Gate = Gate.Unit)]
    public static int Run()
    {
        var assertions = new Assertions();
        using var arm = new Unicorn();
        arm.Map(0x1000, 0x1000);
        using var module = ModuleDefinition.CreateModule("ArithmeticCheck", ModuleKind.Dll);
        var owner = new TypeDefinition("Tests", "Arithmetic", TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed, module.TypeSystem.Object);
        module.Types.Add(owner);
        static ulong?[] Constants(BinOp op) => op is BinOp.SDiv or BinOp.UDiv ? [null, 0, ulong.MaxValue, 7] : [null];
        static string Name(BinOp op, int width, ulong? constant) => $"{op}{width}_{constant?.ToString() ?? "dynamic"}";
        foreach (var width in new[] { 32, 64 })
            foreach (var op in new[] { BinOp.FMin, BinOp.FMax, BinOp.FMinNumber, BinOp.FMaxNumber, BinOp.SDiv, BinOp.UDiv })
            foreach (var constant in Constants(op))
            {
                var integer = width == 32 ? module.TypeSystem.UInt32 : module.TypeSystem.UInt64;
                var floating = width == 32 ? module.TypeSystem.Single : module.TypeSystem.Double;
                var method = new MethodDefinition(Name(op, width, constant), MethodAttributes.Public | MethodAttributes.Static, integer);
                owner.Methods.Add(method);
                method.Parameters.Add(new("left", ParameterAttributes.None, integer));
                method.Parameters.Add(new("right", ParameterAttributes.None, integer));
                var il = method.Body.GetILProcessor();
                foreach (var parameter in method.Parameters)
                {
                    if (op is BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber) { il.Emit(OpCodes.Ldarga, parameter); il.Emit(OpCodes.Ldobj, floating); }
                    else if (parameter.Index == 1 && constant is { } value)
                    {
                        if (width == 32) il.Emit(OpCodes.Ldc_I4, unchecked((int)value));
                        else il.Emit(OpCodes.Ldc_I8, unchecked((long)value));
                    }
                    else il.Emit(OpCodes.Ldarg, parameter);
                }
                NativeArithmetic.Emit(il, op, width, rightConstant: constant);
                if (constant == 7) assertions.True(!method.Body.Instructions.Any(i => i.OpCode.FlowControl == FlowControl.Cond_Branch),
                    "安全常量除数直接写出 div，不引入保护分支");
                if (op is BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber)
                {
                    var result = new VariableDefinition(floating); method.Body.Variables.Add(result);
                    il.Emit(OpCodes.Stloc, result); il.Emit(OpCodes.Ldloca, result); il.Emit(OpCodes.Ldobj, integer);
                }
                il.Emit(OpCodes.Ret);
            }
        using var stream = new MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray()).GetType("Tests.Arithmetic")!;
        ulong pc = 0x1000;
        foreach (var width in new[] { 32, 64 })
            foreach (var op in new[] { BinOp.FMin, BinOp.FMax, BinOp.FMinNumber, BinOp.FMaxNumber, BinOp.SDiv, BinOp.UDiv })
            foreach (var constant in Constants(op))
            {
                var method = loaded.GetMethod(Name(op, width, constant))!;
                Func<ulong, ulong, ulong> invoke;
                if (width == 32)
                {
                    var function = method.CreateDelegate<Func<uint, uint, uint>>();
                    invoke = (x, y) => function((uint)x, (uint)y);
                }
                else invoke = method.CreateDelegate<Func<ulong, ulong, ulong>>();
                var fp = op is BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber;
                uint word = op switch { BinOp.FMin => 0x1e215800, BinOp.FMax => 0x1e214800,
                    BinOp.FMinNumber => 0x1e217800, BinOp.FMaxNumber => 0x1e216800, BinOp.SDiv => 0x1ac10c00, _ => 0x1ac10800 };
                if (width == 64) word |= fp ? 1u << 22 : 1u << 31;
                pc += 4;
                arm.Write(pc, BitConverter.GetBytes(word));
                var lifted = new List<Stmt>();
                Arm64Lifter.Lift(pc, word, lifted);
                var inputs = width == 32
                    ? new ulong[] { 0, 1, 0xffffffff, 0x80000000, 0x7fffffff, 3, 7, 0xfffffff9, 0x3f800000, 0xbf800000, 0x7f800000, 0xff800000, 0x7fc01234, 0xffc05678, 0x7f801234, 0xff805678, 0x00800000, 0x007fffff }
                    : new ulong[] { 0, 1, ulong.MaxValue, 0x8000000000000000, 0x7fffffffffffffff, 3, 7, 0xfffffffffffffff9, 0x3ff0000000000000, 0xbff0000000000000, 0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000012345678, 0xfff8000056781234, 0x7ff0000012345678, 0xfff0000056781234, 0x0010000000000000, 0x000fffffffffffff };
                var random = new Random(20261024);
                var pairs = inputs.SelectMany(x => inputs.Select(y => (x, y: constant ?? y)).Distinct()).Concat(Enumerable.Range(0, 512).Select(_ =>
                    ((ulong)random.NextInt64() & Expr.Mask(width), (constant ?? (ulong)random.NextInt64()) & Expr.Mask(width))));
                foreach (var (x, y) in pairs)
                {
                    var first = fp ? width == 32 ? Unicorn.S(0) : Unicorn.D(0) : Unicorn.X(0);
                    var second = fp ? width == 32 ? Unicorn.S(1) : Unicorn.D(1) : Unicorn.X(1);
                    arm.SetReg(first, x); arm.SetReg(second, y);
                    var error = arm.Start(pc, 1);
                    if (error != 0) throw new InvalidOperationException(Unicorn.Error(error));
                    assertions.Equal(arm.Reg(first) & Expr.Mask(width), invoke(x, y), $"{op}{width} 0x{x:x}, 0x{y:x}");
                    var evaluator = new Evaluator();
                    var destination = fp ? Storage.Vec(0) : Storage.Gpr(0);
                    evaluator.Registers[destination] = x;
                    evaluator.Registers[fp ? Storage.Vec(1) : Storage.Gpr(1)] = y;
                    evaluator.Run(lifted, pc, pc + 4);
                    assertions.True(evaluator.Failure is null, "原指令提升结果可求值");
                    assertions.Equal((UInt128)(arm.Reg(first) & Expr.Mask(width)), evaluator.Get(destination), $"提升 {op}{width} 0x{x:x}, 0x{y:x}");
                }
            }
        return assertions.Finish("native-arithmetic");
    }
}
