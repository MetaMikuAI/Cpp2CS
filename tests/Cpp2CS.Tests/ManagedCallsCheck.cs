using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Runtime;
using Cpp2CS.Ssa;

namespace Cpp2CS.Tests;

/// <summary>验证签名参与 SSA 后的调用输入、返回值及破坏集合。</summary>
internal static class ManagedCallsCheck
{
    private sealed class UnusedAbi : IManagedAbi
    {
        public AbiSignature? Classify(MethodRef method, out string? problem) => throw new InvalidOperationException("此测试不包含托管目标");
        public AbiValue? ClassifyReturn(TypeRef type, out string? problem) => throw new InvalidOperationException("此测试不分类返回值");
    }

    private sealed class FixedAbi(AbiSignature? signature) : IManagedAbi
    {
        public AbiValue? ClassifyReturn(TypeRef type, out string? problem)
        {
            problem = signature is null ? "未知布局" : null;
            return signature?.Return;
        }
        public AbiSignature? Classify(MethodRef method, out string? problem)
        {
            problem = signature is null ? "未知布局" : null;
            return signature;
        }
    }

    public static int Run()
    {
        var convention = new CallingConvention
        {
            StackPointer = Storage.Gpr(31),
            IntegerArguments = Enumerable.Range(0, 8).Select(Storage.Gpr).ToArray(),
            FloatArguments = Enumerable.Range(0, 8).Select(Storage.Vec).ToArray(),
            IntegerResults = [Storage.Gpr(0), Storage.Gpr(1)],
            FloatResults = Enumerable.Range(0, 4).Select(Storage.Vec).ToArray(),
            IndirectResult = Storage.Gpr(8),
            Clobbered = [Storage.Gpr(0), Storage.Gpr(1), Storage.Vec(0)],
        };
        var calls = new ManagedCallModel(call => call.Target is Const { Value: 0x2000 }
            ? new HelperCallee(new Helper(HelperKind.NullCheck, "测试"))
            : call.Target is Const { Value: 0x3000 }
                ? new HelperCallee(new Helper(HelperKind.CxaEndCatch, "测试")) : new UnknownCallee(), new UnusedAbi(), convention);
        var direct = new Call(0x1004, CallKind.Direct, Expr.C(0x2000, 64));
        var block = new Block(0x1000)
        {
            Statements = [new Assign(0x1000, Storage.Gpr(0), Expr.C(42, 64)), direct, new Return(0x1008)],
        };
        var function = new MachineFunction
        {
            Entry = 0x1000,
            Range = new FunctionRange(0x1000, 0x100c, BoundaryEvidence.SymbolCandidate, "合成检查"),
            Blocks = [block],
        };
        var errors = Lowering.Registers(function, convention, calls, new Read(Storage.Gpr(0), 64));
        Require(errors.Count == 0, string.Join("; ", errors));
        var lowered = block.Statements.OfType<Call>().Single();
        Require(lowered.Arguments is [Const { Value: 42 }], "已知调用只读取实际参数");
        Require(lowered.Results.SequenceEqual([Storage.Gpr(0)]) && lowered.Defines.Length == 1, "只定义实际返回寄存器");
        Require(block.Statements[^1] is Return { Value: Use u } && u.Variable == lowered.Defines[0], "返回值引用调用结果");

        block.Statements = [new Assign(0x1000, Storage.Gpr(0), Expr.C(42, 64)), direct with { Target = Expr.C(0x3000, 64) }, new Return(0x1008)];
        errors = Lowering.Registers(function, convention, calls, new Read(Storage.Gpr(0), 64));
        Require(errors.Count == 0, string.Join("; ", errors));
        Require(block.Statements.OfType<Call>().Single() is { Arguments.Length: 0, Defines.Length: 0 }, "无参 void 调用不产生参数和结果");
        Require(block.Statements[^1] is Return { Value: Unknown }, "void 调用仍破坏易失寄存器，不保留旧值");
        Require(calls.Results(direct with { Kind = CallKind.Tail }).Count == 0, "尾调用不在当前函数定义返回寄存器");
        var indirect = direct with { Kind = CallKind.Indirect, Target = new Read(Storage.Gpr(9), 64) };
        Require(calls.Reads(indirect).Count == 17 && calls.Results(indirect).Count == 6, "未知间接调用保留全部约定寄存器");
        Require(calls.Reads(direct with { Target = Expr.C(0x4000, 64) }).Count == 17, "未知直接调用保持保守约定");
        var classPassThrough = new ManagedCallModel(_ => new HelperCallee(new Helper(HelperKind.ClassInit, "返回类型指针的测试包装") { ReturnedArgument = 0 }),
            new UnusedAbi(), convention);
        Require(classPassThrough.Reads(direct).SequenceEqual([Storage.Gpr(0)]) && classPassThrough.Results(direct).SequenceEqual([Storage.Gpr(0)]),
            "返回类型指针的类初始化包装仍产生 x0 结果");
        var owner = new TypeDef
        {
            Index = 0, Assembly = "Test.dll", Namespace = "Test", Name = "Owner", Token = 0,
            Attributes = System.Reflection.TypeAttributes.Public, IsValueType = false, IsEnum = false,
        };
        var method = new MethodDef
        {
            Index = 0, Owner = owner, Name = "Method", Token = 0, Slot = -1,
            Attributes = System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static,
            ImplAttributes = System.Reflection.MethodImplAttributes.IL,
        };
        var callee = new ManagedCallee([new CodeOwner(new MethodRef(method, [], []), false)], null);
        var type = new PrimitiveRef("nint");
        var signature = new AbiSignature(null,
            [new AbiValue(type, Passing.Registers, [new AbiPiece(Storage.Gpr(0), 64, 0)])],
            new AbiPiece(Storage.Gpr(1), 64, 0),
            new AbiValue(type, Passing.Registers, [new AbiPiece(Storage.Vec(0), 32, 0), new AbiPiece(Storage.Vec(1), 32, 4)]));
        var managed = new ManagedCallModel(_ => callee, new FixedAbi(signature), convention);
        Require(managed.Reads(direct).SequenceEqual([Storage.Gpr(0), Storage.Gpr(1)]), "保留 MethodInfo 参数");
        Require(managed.Results(direct).SequenceEqual([Storage.Vec(0), Storage.Vec(1)]), "保留全部聚合返回寄存器");
        signature = signature with { Return = new AbiValue(type, Passing.Indirect, [new AbiPiece(Storage.Gpr(8), 64, 0)]) };
        managed = new ManagedCallModel(_ => callee, new FixedAbi(signature), convention);
        Require(managed.Reads(direct).Contains(Storage.Gpr(8)) && managed.Results(direct).Count == 0, "间接返回缓冲区作为输入");
        signature = signature with { Parameters = [new AbiValue(type, Passing.Stack, [])] };
        managed = new ManagedCallModel(_ => callee, new FixedAbi(signature), convention);
        Require(managed.Reads(direct).Count == 17 && managed.Results(direct).Count == 6, "未支持栈传参不能丢弃保守输入输出");
        managed = new ManagedCallModel(_ => callee, new FixedAbi(null), convention);
        Require(managed.Reads(direct).Count == 17, "未知布局保留保守输入");
        Console.WriteLine("调用签名与 SSA 数据流检查通过");
        return 0;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
