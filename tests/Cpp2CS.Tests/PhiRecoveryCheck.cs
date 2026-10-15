using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

/// <summary>从机器 SSA 恢复并执行分支和循环；未知来源必须沿依赖撤销，不能通过类型约束伪造恢复。</summary>
internal static class PhiRecoveryCheck
{
    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("PhiChecks", new Version(1, 0)), "PhiChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var harness = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(harness);
        var owner = new TypeDef { Index = -1, Assembly = "Checks.dll", Namespace = "Checks", Name = "Harness", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        TypeReference Reference(TypeRef type) => module.ImportReference(Type.GetType("System." +
            (type == types.String ? "String" : type == types.Object ? "Object" : ManagedTypes.PrimitiveName(type)), throwOnError: true)!);
        var emitter = new BodyEmitter(types, Reference, f => throw new NotSupportedException(f.ToString()), m => throw new NotSupportedException(m.ToString()));

        ValueRecovery Check(string name, TypeRef result, TypeRef[] parameters, Block[] blocks, bool accepted = true)
        {
            var definition = new MethodDef { Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1,
                Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL,
                ReturnType = result, Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, SR.ParameterAttributes.None, null, false)).ToArray() };
            var method = new MethodRef(definition, [], []);
            foreach (var block in blocks)
            {
                ulong[] targets = block.Statements.Last() switch { Branch b => [b.Target, b.Fallthrough], Jump j => [j.Target], _ => [] };
                foreach (var target in targets)
                {
                    var next = blocks.Single(b => b.Start == target);
                    block.Successors.Add(next); next.Predecessors.Add(block);
                }
            }
            var function = new MachineFunction { Entry = blocks[0].Start,
                Range = new FunctionRange(0x1000, 0x5000, BoundaryEvidence.SymbolCandidate, "汇合执行检查"), Blocks = [.. blocks] };
            var prepared = new PreparedMethod(method, session.Abi.ClassifyReturn(result, out _), function, null, []);
            var recovered = BodyRecovery.Recover(session, prepared);
            Require((recovered.Body is not null) == accepted, name + ": " + string.Join("; ", recovered.Problems));
            if (recovered.Body is { } body)
            {
                var actual = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, Reference(result));
                foreach (var parameter in parameters) actual.Parameters.Add(new ParameterDefinition(Reference(parameter)));
                harness.Methods.Add(actual);
                Require(emitter.Emit(body, actual) is null, name + " 的 CIL 输出");
            }
            return new(session, prepared);
        }

        Variable V(int index, int version = 1) => new(Storage.Gpr(index), version);
        Use A(int index, int width = 32) => new(V(index, 0), width);
        var left = V(8); var right = V(9); var merged = V(10);
        Block[] Diamond(Expr condition, Expr yes, Expr no, int width) =>
        [
            new(0x1000) { Statements = [new Branch(0x1000, condition, 0x2000, 0x3000)] },
            new(0x2000) { Statements = [new Define(0x2000, left, yes), new Jump(0x2004, 0x4000)] },
            new(0x3000) { Statements = [new Define(0x3000, right, no), new Jump(0x3004, 0x4000)] },
            new(0x4000) { Statements = [new Phi(0x4000, merged, [left, right]), new Return(0x4004) { Value = new Use(merged, width) }] },
        ];
        Expr When(int index) => new Compare(Cond.Ne, A(index), Expr.C(0, 32));
        Check("SignedMerge", types.Int32, [types.Int32, types.Int32, types.Int32],
            Diamond(When(2), A(0), new Binary(BinOp.Add, A(1), Expr.C(0, 32), 32), 32));
        Check("WidenMerge", types.UInt64, [types.UInt64, types.Int32],
            Diamond(When(1), Expr.C(uint.MaxValue, 32), A(0, 64), 64));
        Check("ZeroHigh", types.UInt64, [types.Int32], Diamond(When(0), Expr.C(uint.MaxValue, 32), Expr.C(0, 32), 64));
        var undefinedHigh = Diamond(When(1), A(0), Expr.C(0, 32), 64);
        undefinedHigh[3].Statements[0] = new Phi(0x4000, merged, [V(0, 0), right]);
        Check("UndefinedHigh", types.UInt64, [types.Int32, types.Int32], undefinedHigh, false);
        var floatLeft = new Use(new Variable(Storage.Vec(0), 0), 32);
        var floatRight = new Use(new Variable(Storage.Vec(1), 0), 32);
        Check("FloatMerge", types.Single, [types.Single, types.Single, types.Int32], Diamond(When(0), floatLeft, floatRight, 32));
        Check("NullMerge", types.String, [types.String, types.Int32], Diamond(When(1), A(0, 64), Expr.C(0, 64), 64));
        Check("BaseMerge", types.Object, [types.String, types.Object, types.Int32], Diamond(When(2), A(0, 64), A(1, 64), 64));
        Check("InvalidReference", types.String, [types.String, types.Int32], Diamond(When(1), A(0, 64), Expr.C(1, 64), 64), false);
        Check("UnknownReference", types.String, [types.String, types.Int32], Diamond(When(1), A(0, 64), new Unknown("未知来源", 64), 64), false);
        var callTarget = session.Model.Code.First(pair => pair.Value.Count == 1 && pair.Value[0].Method.Method is { IsStatic: true, Parameters.Count: 0 } m
            && m.ReturnType == types.Int32 && m.GenericParameters.Count == 0 && m.Owner.GenericParameters.Count == 0);
        var callResult = V(0);
        var undefinedReturn = Diamond(When(0), new Use(callResult, 32), Expr.C(0, 32), 64);
        undefinedReturn[0].Statements.Insert(0, new Call(0x1000, CallKind.Direct, Expr.C(callTarget.Key, 64))
            { Results = [Storage.Gpr(0)], Defines = [callResult] });
        undefinedReturn[3].Statements[0] = new Phi(0x4000, merged, [callResult, right]);
        Check("UndefinedReturnHigh", types.UInt64, [types.Int32], undefinedReturn, false);

        var count = V(11); var total = V(12); var nextCount = V(13); var nextTotal = V(14);
        Block[] SumLoop(Expr increment) =>
        [
            new(0x1000) { Statements = [new Jump(0x1000, 0x2000)] },
            new(0x2000) { Statements = [new Phi(0x2000, count, [V(0, 0), nextCount]), new Phi(0x2000, total, [V(1, 0), nextTotal]),
                new Branch(0x2000, new Compare(Cond.Ne, new Use(count, 32), Expr.C(0, 32)), 0x3000, 0x4000)] },
            new(0x3000) { Statements = [new Define(0x3000, nextTotal, increment),
                new Define(0x3004, nextCount, new Binary(BinOp.Sub, new Use(count, 32), Expr.C(1, 32), 32)), new Jump(0x3008, 0x2000)] },
            new(0x4000) { Statements = [new Return(0x4000) { Value = new Use(total, 32) }] },
        ];
        Check("SumLoop", types.Int32, [types.UInt32, types.Int32],
            SumLoop(new Binary(BinOp.Add, new Use(total, 32), new Use(count, 32), 32)));
        var invalid = Check("InvalidLoop", types.Int32, [types.UInt32, types.Int32],
            SumLoop(new Binary(BinOp.Add, new Use(total, 32), new Unknown("未知回边", 32), 32)), false);
        Require(!invalid.Locals.ContainsKey(total) && !invalid.Locals.ContainsKey(nextTotal), "撤销无效回边及其依赖的 φ");

        var x = V(15); var y = V(16); var initialX = V(17); var initialY = V(18);
        Check("SwapLoop", types.UInt32, [types.UInt32],
        [
            new(0x1000) { Statements = [new Define(0x1000, initialX, Expr.C(1, 32)), new Define(0x1004, initialY, Expr.C(2, 32)), new Jump(0x1008, 0x2000)] },
            new(0x2000) { Statements = [new Phi(0x2000, x, [initialX, y]), new Phi(0x2000, y, [initialY, x]),
                new Phi(0x2000, count, [V(0, 0), nextCount]), new Branch(0x2000, new Compare(Cond.Ne, new Use(count, 32), Expr.C(0, 32)), 0x3000, 0x4000)] },
            new(0x3000) { Statements = [new Define(0x3000, nextCount, new Binary(BinOp.Sub, new Use(count, 32), Expr.C(1, 32), 32)), new Jump(0x3004, 0x2000)] },
            new(0x4000) { Statements = [new Return(0x4000) { Value = new Binary(BinOp.Add,
                new Binary(BinOp.Mul, new Use(x, 32), Expr.C(10, 32), 32), new Use(y, 32), 32) }] },
        ]);
        var unseeded = Check("Unseeded", types.UInt32, [],
        [
            new(0x1000) { Statements = [new Jump(0x1000, 0x2000)] },
            new(0x2000) { Statements = [new Phi(0x2000, x, [y]), new Phi(0x2000, y, [x]), new Return(0x2004) { Value = new Use(x, 32) }] },
        ], false);
        Require(!unseeded.Locals.ContainsKey(x) && !unseeded.Locals.ContainsKey(y), "没有外部来源的环不能产生类型证据");

        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
        object? Run(string name, params object?[] args) => runtime.GetMethod(name)!.Invoke(null, args);
        foreach (var input in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            Require((int)Run("SignedMerge", input, ~input, 1)! == input, "有符号汇合 true");
            Require((int)Run("SignedMerge", input, ~input, 0)! == ~input, "有符号汇合 false");
            for (uint n = 0; n < 32; n++)
                Require((int)Run("SumLoop", n, input)! == unchecked(input + (int)(n * (n + 1) / 2)), "循环归纳值与溢出");
        }
        foreach (var input in new[] { 0UL, (ulong)uint.MaxValue, 0x1_0000_0000UL, ulong.MaxValue })
        {
            Require((ulong)Run("WidenMerge", input, 1)! == uint.MaxValue, "窄定义的高位清零");
            Require((ulong)Run("WidenMerge", input, 0)! == input, "宽来源的高位保留");
        }
        Require((ulong)Run("ZeroHigh", 1)! == uint.MaxValue && (ulong)Run("ZeroHigh", 0)! == 0, "φ 的所有来源都清零高位");
        foreach (var bits in new[] { 0, int.MinValue, 0x3f800000, 0x7fc01234, unchecked((int)0xffc01234) })
        {
            var value = BitConverter.Int32BitsToSingle(bits);
            Require(BitConverter.SingleToInt32Bits((float)Run("FloatMerge", value, 1f, 1)!) == bits, "浮点 φ 保留 NaN 和负零位型");
            Require((float)Run("FloatMerge", value, 1f, 0)! == 1f, "浮点 φ 另一分支");
        }
        var text = new string('a', 3);
        Require(ReferenceEquals(Run("NullMerge", text, 1), text) && Run("NullMerge", text, 0) is null, "引用与已知零合并");
        var other = new object();
        Require(ReferenceEquals(Run("BaseMerge", text, other, 1), text) && ReferenceEquals(Run("BaseMerge", text, other, 0), other), "引用合并到公共基类");
        for (uint n = 0; n < 10; n++) Require((uint)Run("SwapLoop", n)! == (n % 2 == 0 ? 12U : 21U), "互相引用的 φ 环保持并行赋值");
        Console.WriteLine("φ 恢复及 CIL 执行通过：整数/浮点分支、循环归纳值、交换环、空引用、高位边界和无效来源撤销");
        PhiNativeCheck.Run(session);
        return 0;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
