using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;

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
        var provenTail = ((Call)block.Statements[0]) with { Arguments = [new Use(input, 64)] };
        block.Statements = [provenTail];
        a.True(NativeInputs.Reads(lifted, knownTail: c => ReferenceEquals(c, provenTail)) is { } provenReads
            && provenReads.Contains(receiver.Variable.Storage) && provenReads.Contains(register), "外部完整尾调用证据仍保留目标和实参依赖");
        a.True(NativeInputs.Reads(lifted, knownTail: _ => false) is null, "未获证据的尾调用仍拒绝未使用证明");
        function.UnresolvedIndirectJumps++;
        a.True(NativeInputs.Reads(lifted, knownTail: _ => true) is null, "证明一个尾调用不能覆盖额外未解析跳转");
        function.UnresolvedIndirectJumps = 1;
        Expr Field(Expr root, ulong offset) => new Load(new Binary(BinOp.Add, root, Expr.C(offset, 64), 64), 64);
        var delegateTail = tail with { Target = Field(receiver, 0x18), Arguments = [Field(receiver, 0x40), Field(receiver, 0x28), new Use(input, 64)] };
        block.Statements = [delegateTail];
        a.True(NativeInputs.Reads(lifted) is { } delegateReads && delegateReads.Contains(register) && delegateReads.Contains(receiver.Variable.Storage), "委托布局证明尾调用时仍保留全部参数依赖");
        block.Statements = [delegateTail with { Arguments = [Field(receiver, 0x40), Field(new Use(input, 64), 0x28)] }];
        a.True(NativeInputs.Reads(lifted) is null, "不同对象的方法身份不能证明委托尾调用");
        block.Statements = [delegateTail with { Arguments = [Field(receiver, 0x40), Expr.C(0, 64)] }];
        a.True(NativeInputs.Reads(lifted) is null, "缺失方法身份仍保留未知尾跳转");
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
