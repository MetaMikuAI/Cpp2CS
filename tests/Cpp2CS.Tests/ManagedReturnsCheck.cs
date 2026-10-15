using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Ssa;

namespace Cpp2CS.Tests;

/// <summary>返回位置参与活跃性和 SSA 的检查；覆盖窄值、聚合及入口返回缓冲区。</summary>
internal static class ManagedReturnsCheck
{
    public static int Run()
    {
        var convention = new CallingConvention
        {
            StackPointer = Storage.Gpr(31), IntegerArguments = [Storage.Gpr(0)], FloatArguments = [],
            IntegerResults = [Storage.Gpr(0), Storage.Gpr(1)], FloatResults = [],
            IndirectResult = Storage.Gpr(8), Clobbered = [Storage.Gpr(0), Storage.Gpr(1), Storage.Gpr(8)],
        };
        var type = new PrimitiveRef("nint");
        MachineFunction Lower(AbiValue? result, params Stmt[] statements)
        {
            var function = new MachineFunction
            {
                Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1100, BoundaryEvidence.SymbolCandidate, "合成检查"),
                Blocks = [new Block(0x1000) { Statements = [.. statements, new Return(0x1080)] }],
            };
            ManagedReturns.Bind(function, result);
            var errors = Lowering.Registers(function, convention, new ConservativeCallModel(convention), null);
            Require(errors.Count == 0, string.Join("; ", errors));
            return function;
        }
        Return Returned(MachineFunction function) => (Return)function.Blocks[0].Statements[^1];

        var narrow = Lower(new AbiValue(type, Passing.Registers, [new AbiPiece(Storage.Gpr(0), 8, 0)]),
            new Assign(0x1000, Storage.Gpr(0), Expr.C(0x1234, 64)));
        Require(Returned(narrow).Value is Const { Width: 8, Value: 0x34 }, "窄整数不读取寄存器高位");

        var aggregate = Lower(new AbiValue(type, Passing.Registers,
            [new AbiPiece(Storage.Gpr(0), 64, 0), new AbiPiece(Storage.Gpr(1), 32, 8)]),
            new Assign(0x1000, Storage.Gpr(0), Expr.C(11, 64)),
            new Assign(0x1004, Storage.Gpr(1), Expr.C(22, 64)));
        Require(Returned(aggregate).Pieces is
            [{ Offset: 0, Value: Const { Value: 11, Width: 64 } }, { Offset: 8, Value: Const { Value: 22, Width: 32 } }],
            "双寄存器返回保留两个分量及偏移");

        var hfa = Lower(new AbiValue(type, Passing.Registers,
            Enumerable.Range(0, 4).Select(i => new AbiPiece(Storage.Vec(i), 64, i * 8)).ToArray()),
            Enumerable.Range(0, 4).Select(i => (Stmt)new Assign((ulong)(0x1000 + i * 4), Storage.Vec(i), Expr.C((ulong)(i + 1), 64))).ToArray());
        Require(Returned(hfa).Pieces.Length == 4 && Returned(hfa).Pieces.Select(p => ((Const)p.Value).Value).SequenceEqual([1UL, 2UL, 3UL, 4UL]),
            "四个 double 的聚合返回不丢失 v1-v3");

        var indirect = Lower(new AbiValue(type, Passing.Indirect, [new AbiPiece(Storage.Gpr(8), 64, 0)]),
            new Assign(0x1000, Storage.Gpr(19), new Read(Storage.Gpr(8), 64)),
            new Call(0x1004, CallKind.Direct, Expr.C(0x2000, 64)),
            new Store(0x1008, new Read(Storage.Gpr(19), 64), Expr.C(42, 64)));
        Require(Returned(indirect).Buffer is Use { Variable.Version: 0 } buffer && buffer.Variable.Storage == Storage.Gpr(8),
            "返回缓冲区来自入口 x8，不读取调用后的 x8");
        Require(indirect.Blocks[0].Statements.OfType<Store>().Single().Target == Returned(indirect).Buffer,
            "缓冲区写入与返回位置保持相同来源");

        var empty = Lower(null, new Assign(0x1000, Storage.Gpr(0), Expr.C(42, 64)));
        Require(empty.Blocks[0].Statements.Count == 1 && !ExprMap.Operands(Returned(empty)).Any(), "void 不制造返回寄存器依赖");
        Console.WriteLine("方法返回布局与 SSA 检查通过");
        return 0;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
