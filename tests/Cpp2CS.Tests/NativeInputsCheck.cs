using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;

namespace Cpp2CS.Tests;

internal static class NativeInputsCheck
{
    [Command("native-inputs", "原生入口参数读取的直接、汇合、调用与未知边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var register = Storage.Gpr(2);
        var input = new Variable(register, 0);
        var local = new Variable(register, 1);
        var block = new Block(0x1000);
        var function = new MachineFunction { Entry = 0x1000, Range = new(0x1000, 0x1100, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block] };
        var lifted = new LiftedFunction(function, []);
        block.Statements = [new Define(0x1000, local, Expr.C(0, 64)), new Return(0x1004) { Value = new Use(local, 64) }];
        a.True(NativeInputs.Reads(lifted) is { } absent && !absent.Contains(register), "读取覆盖后的寄存器不读取入口参数");
        block.Statements = [new Define(0x1000, local, new Load(new Use(input, 64), 64)), new Return(0x1004)];
        a.True(NativeInputs.Reads(lifted)!.Contains(register), "结果未使用的原生加载也读取参数");
        block.Statements = [new Phi(0x1000, local, [input, new(register, 2)]), new Return(0x1004)];
        a.True(NativeInputs.Reads(lifted)!.Contains(register), "任一分支传入参数均算使用");
        block.Statements = [new Call(0x1000, CallKind.Direct, Expr.C(0x2000, 64)) { Arguments = [new Use(input, 64)] }, new Return(0x1004)];
        a.True(NativeInputs.Reads(lifted)!.Contains(register), "转传给其他调用的参数仍算使用");
        block.Statements = [new Return(0x1000) { Value = new Use(input, 64) }];
        a.True(NativeInputs.Reads(lifted)!.Contains(register), "返回参数仍算使用");
        block.Statements = [new Opaque(0x1000, "unknown")];
        a.True(NativeInputs.Reads(lifted) is null, "未知指令不能证明未用");
        block.Statements = [new Return(0x1000)];
        a.True(NativeInputs.Reads(lifted with { Errors = ["incomplete"] }) is null, "提升失败不能证明未用");
        function.Problems.Add("incomplete control flow");
        a.True(NativeInputs.Reads(lifted) is null, "不完整控制流不能证明未用");
        function.Problems.Clear();
        function.UnresolvedIndirectJumps = 1;
        a.True(NativeInputs.Reads(lifted) is null, "未解析跳转不能证明未用");
        var receiver = new Use(new Variable(Storage.Gpr(1), 0), 64);
        var target = new Load(new Binary(BinOp.Add, new Load(receiver, 64), Expr.C((ulong)RuntimeLayout.VtableMethodPointer(2), 64), 64), 64);
        var tail = new Call(0x1000, CallKind.TailIndirect, target) { Arguments = [receiver] };
        block.Statements = [tail];
        a.True(NativeInputs.Reads(lifted) is { } virtualReads && virtualReads.Contains(receiver.Variable.Storage) && !virtualReads.Contains(register),
            "同一接收者的 vtable 尾调用保留输入读取证明");
        block.Statements = [tail with { Arguments = [new Use(input, 64)] }];
        a.True(NativeInputs.Reads(lifted) is null, "vtable 对象与接收者不一致仍拒绝证明");
        block.Statements = [tail with { Target = new Load(receiver, 64) }];
        a.True(NativeInputs.Reads(lifted) is null, "任意指针尾跳转不能视为 vtable 调用");
        return a.Finish("native-inputs");
    }

    [Command("native-parameters", "打印指定原生方法的参数使用证据", Arguments = "<binary> <metadata> <入口地址…>")]
    public static int Inspect(string binary, string metadata, string[] entries)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var lifter = new FunctionLifter(facts);
        var abi = new ManagedAbi(facts.Layouts);
        foreach (var entry in entries.Select(s => System.Convert.ToUInt64(s, 16)))
        {
            var method = facts.EntriesAt(entry).Select(e => e.Method).OfType<Cpp2CS.Model.MethodRef>().First();
            var signature = abi.Classify(method, out _)!;
            Expr? result = signature.Return is not { } value ? null
                : new Intrinsic("return", value.Pieces.Select(p => (Expr)new Read(p.Register, p.Width)).ToArray(), 64);
            var reads = NativeInputs.Reads(lifter.Lift(entry, result, simplify: false));
            for (var i = 0; i < signature.Parameters.Length; i++)
                Console.WriteLine($"0x{entry:x}\t{method}\t{method.Method.Parameters[i].Name}\t{(reads is null ? "unknown" : signature.Parameters[i].Pieces.Any(p => reads.Contains(p.Register)) ? "read" : "unused")}\t{string.Join(',', signature.Parameters[i].Pieces.Select(p => p.Register))}");
        }
        return 0;
    }
}
