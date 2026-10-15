using System.Reflection;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

/// <summary>借用真实类型定义构造小型 SSA，检查字段映射和读取时机，不作为真实方法行为证明。</summary>
internal static class ValueRecoveryCheck
{
    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        var field = session.Model.Fields.First(f => !f.IsStatic && !f.Owner.IsValueType
            && f.Owner.GenericParameters.Count == 0 && f.Offset >= 16 && f.Type == types.Int32);
        var definition = new MethodDef
        {
            Index = -1, Owner = field.Owner, Name = "SyntheticValueCheck", Token = 0, Slot = -1,
            Attributes = MethodAttributes.Public, ImplAttributes = MethodImplAttributes.IL,
            ReturnType = types.Int32,
            Parameters = [new ParameterDef("value", types.Int32, ParameterAttributes.None, null, false)],
        };
        var method = new MethodRef(definition, [], []);
        var self = new Use(new Variable(Storage.Gpr(0), 0), 64);
        var location = new Binary(BinOp.Add, self, Expr.C((ulong)field.Offset, 64), 64);
        var load = new Load(location, 32);
        var saved = new Variable(Storage.Gpr(2), 1);
        var function = new MachineFunction
        {
            Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1010, BoundaryEvidence.SymbolCandidate, "合成检查"),
            Blocks = [new Block(0x1000) { Statements =
            [
                new Define(0x1000, saved, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, load, 64)),
                new Store(0x1004, location, Expr.C(9, 32)),
                new Return(0x1008) { Value = new Use(saved, 32) },
            ] }],
        };
        var prepared = new PreparedMethod(method, session.Abi.ClassifyReturn(types.Int32, out _), function, null, []);
        var recovery = new ValueRecovery(session, prepared);
        Require(recovery.Recover(load, out _) is FieldValue f && f.Field.Field == field, "字段地址必须匹配真实元数据中的字段");
        Require(recovery.Recover(new Use(saved, 32), out _) is ConversionValue { Operand: LocalValue }, "写入后的返回必须引用此前保存的局部值，不能重新读字段");
        Require(recovery.Recover(new Use(new Variable(Storage.Gpr(1), 0), 32), out _) is ArgumentValue { Index: 0 }, "参数寄存器恢复为逻辑参数");
        Require(recovery.Recover(new Use(new Variable(Storage.Gpr(1), 0), 64), out _) is null, "窄参数的高位不可凭空扩展");
        Require(recovery.Recover(new Load(location, 16), out _) is null, "部分字段读取不能冒充整个字段");
        Require(recovery.Recover(new Compare(Cond.Eq, self, Expr.C(0, 64)), out _) is ComparisonValue { Right: ConstantValue { Bits: 0 } n }
            && n.Type == method.DeclaringType, "对象判空的零必须具有对象类型");
        Require(recovery.Recover(new Unknown("检查", 32), out _) is null, "未知值不能生成常量");

        var target = session.Model.Code.First(pair => pair.Value.Count == 1 && pair.Value[0].Method.Method is { IsStatic: true, Parameters.Count: 0 } m
            && m.ReturnType == types.Int32 && m.GenericParameters.Count == 0 && m.Owner.GenericParameters.Count == 0);
        var call = new Call(0x100c, CallKind.Direct, Expr.C(target.Key, 64))
        {
            Sources = [Storage.Gpr(0)], Arguments = [new Unknown("隐藏 MethodInfo", 64)],
        };
        Require(recovery.Invocation(call, out _) is { Receiver: null, Arguments.Count: 0 }, "托管调用不应输出隐藏 MethodInfo 参数");
        Console.WriteLine("托管表达式检查通过：字段定位、读取顺序、参数位宽、判空和隐藏参数");
        return 0;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
