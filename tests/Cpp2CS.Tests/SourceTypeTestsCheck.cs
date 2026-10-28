using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceTypeTestsCheck
{
    [Command("source-type-tests", "引用上行类型检查、捕获异常类型与布尔扩展边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var method = new MethodRef(new MethodDef { Index = -1, Owner = types.Object.Definition, Name = "Read", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = types.Object }, [], []);
        ManagedValue Rewritten(ManagedValue value) => SourceRewriter.Rewrite(new(method,
            [new(0, [new ManagedReturn(0, value)])]), types).Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value!;
        var a = new Assertions();
        var targetType = new TypeDef { Index = -2, Assembly = "Tests.dll", Namespace = "Tests", Name = "Record", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var reference = new DefinitionRef(targetType, []);
        var instance = new ArgumentValue(0, reference, 64);
        var field = new FieldRef(new FieldDef { Index = -2, Owner = targetType, Name = "value", Type = types.Int32,
            Attributes = FieldAttributes.Public, Offset = 16 }, reference);
        var inspect = new MethodRef(new MethodDef { Index = -2, Owner = targetType, Name = "Inspect", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = types.Int32 }, [], []);
        var nullError = types.CorlibMethod("System.NullReferenceException", ".ctor")!;
        foreach (var checkedReceiver in new[] { false, true })
        {
            var statements = new List<ManagedStatement>();
            if (checkedReceiver) statements.Add(new ManagedCheck(1, new ComparisonValue(Cond.Eq, instance,
                new ConstantValue(0, reference, 64), types.Boolean), nullError));
            statements.Add(new ManagedCall(2, new(inspect, instance, [], false), null, false));
            statements.Add(new ManagedJump(3, new(3, [])));
            var input = new ManagedBody(method, [new(0, [new ManagedJump(0, new(1, []))]), new(1, statements),
                new(2, [new ManagedRethrow(2)]), new(3, [new ManagedReturn(3, new FieldValue(instance, field, types.Int32, 32))])])
                { Regions = [new([1], 2, [2], null, ManagedRegionKind.Catch)] };
            var output = SourceRewriter.Rewrite(input, types);
            a.Equal(checkedReceiver, output.Regions[0].Try.Contains(3UL), "在删除显式判空前使用其字段访问证据");
            a.True(!output.Blocks.SelectMany(b => b.Statements).OfType<ManagedCheck>().Any(), "调用前的冗余判空仍可删除");
        }
        foreach (var from in new TypeRef[] { types.String, new ArrayRef(types.String, 1), types.Corlib("System.InvalidOperationException") })
        {
            var value = new ArgumentValue(0, from, 64);
            a.Equal<ManagedValue>(value, Rewritten(new IsInstValue(value, types.Object)), "引用上行保留原值，包含 null");
        }
        var obj = new ArgumentValue(0, types.Object, 64);
        var downcast = new IsInstValue(obj, types.String);
        a.Equal<ManagedValue>(downcast, Rewritten(downcast), "向下转换仍需运行时类型检查");
        var boxed = new IsInstValue(obj, types.Int32, types.Object);
        a.Equal<ManagedValue>(boxed, Rewritten(boxed), "装箱类型检查不按引用上行处理");
        var array = new ArgumentValue(0, new ArrayRef(types.String, 1), 64);
        a.Equal<ManagedValue>(array, Rewritten(new IsInstValue(array, new ArrayRef(types.Object, 1))), "引用数组协变保留原值");
        var values = new IsInstValue(new ArgumentValue(0, new ArrayRef(types.Int32, 1), 64), new ArrayRef(types.Object, 1));
        a.Equal<ManagedValue>(values, Rewritten(values), "值类型数组不能通过装箱变成 object 数组");

        var caught = new LocalValue(new(Storage.Temp(0), 1), types.Object, 64);
        var exception = types.Corlib("System.Exception");
        var cancellation = types.Corlib("System.OperationCanceledException");
        ManagedBody Catch(TypeRef tested, TypeRef? catchType = null, bool replace = false) => new(method,
            [new(0, [new ManagedReturn(0, null)]), new(1, [
                .. (replace ? new ManagedStatement[] { new ManagedAssignment(1, caught, new ConstantValue(0, types.Object, 64)) } : []),
                new ManagedReturn(2, new ComparisonValue(Cond.Ne, new IsInstValue(caught, tested), new ConstantValue(0, tested, 64), types.Boolean))])])
            { Regions = [new([0], 1, [1], caught, ManagedRegionKind.Catch) { CatchType = catchType }] };
        ManagedValue CatchResult(ManagedBody body) => ((ManagedReturn)SourceCaughtExceptions.Rewrite(body, types).Blocks[1].Statements.Last()).Value!;
        a.True(CatchResult(Catch(exception)) is ConstantValue { Bits: 1 }, "默认 catch 对象必为非空 Exception");
        a.True(CatchResult(Catch(types.Object, cancellation)) is ConstantValue { Bits: 1 }, "特定 catch 类型向基类上行成立");
        a.True(CatchResult(Catch(cancellation)) is ComparisonValue, "普通 Exception 不保证为取消异常");
        a.True(CatchResult(Catch(exception, replace: true)) is ComparisonValue, "捕获对象被重写后不沿用入口事实");

        var boolean = new ArgumentValue(0, types.Boolean, 8);
        var widened = new ConversionValue(ConvKind.ZeroExtend, boolean, types.UInt64, 64);
        var narrowed = new ConversionValue(ConvKind.Truncate, widened, types.UInt32, 32);
        a.True(Rewritten(narrowed) is ConversionValue { Kind: ConvKind.ZeroExtend, Width: 32, Operand: var operand } && operand == boolean,
            "8→64→32 保留一次扩展");
        var mask = new BinaryValue(BinOp.And, narrowed, new ConstantValue(1, types.UInt32, 32), types.UInt32, 32);
        a.Equal<ManagedValue>(boolean, Rewritten(new ComparisonValue(Cond.Ne, mask, new ConstantValue(0, types.UInt32, 32), types.Boolean)), "布尔扩展、掩码及零比较折回原判断");
        var signed = narrowed with { Operand = widened with { Kind = ConvKind.SignExtend } };
        a.Equal<ManagedValue>(signed, Rewritten(signed), "不混用有符号扩展规则");
        var flag = new LocalValue(new(Storage.Temp(2), 1), types.UInt64, 64);
        var flagUse = new ComparisonValue(Cond.Ne, mask with { Left = narrowed with { Operand = flag } }, new ConstantValue(0, types.UInt32, 32), types.Boolean);
        var flags = new ManagedBody(method, [new(0, [new ManagedAssignment(0, flag, widened),
            new ManagedReturn(1, new BooleanValue(true, flagUse, flagUse, types.Boolean))])]);
        var restored = SourceRewriter.Rewrite(flags, types);
        a.True(!restored.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
            .OfType<LocalValue>().Any(v => v.Type.Equals(types.UInt64)), "多次使用的布尔标志不再保留 ulong 局部");
        var mixed = flags with { Blocks = [new(0, [new ManagedAssignment(0, flag, widened), new ManagedReturn(1,
            new BinaryValue(BinOp.Add, flag, narrowed with { Operand = flag }, types.UInt64, 64))])] };
        a.True(SourceRewriter.Rewrite(mixed, types).Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
            .Any(s => s.Target == flag), "同一表达式同时读取完整值与截断值时保留宽局部");
        foreach (var mode in new[] { "nonnull", "null", "alias", "reset", "join", "addressed" })
        {
            var alias = new LocalValue(new(Storage.Temp(3), 1), types.Object, 64);
            var zero = new ConstantValue(0, types.Object, 64);
            ManagedValue input = mode == "alias" ? alias : obj;
            var guarded = new ManagedBody(method, [
                new(0, [.. (mode == "addressed" ? new ManagedStatement[] { new ManagedCall(0, new(method, null, [new AddressValue(obj)], false), null, false) } : []),
                    new ManagedBranch(0, new ComparisonValue(mode == "null" ? Cond.Eq : Cond.Ne, obj, zero, types.Boolean), new(1, []), new(mode == "join" ? 1UL : 2UL, []))]),
                new(1, [.. (mode == "alias" ? new ManagedStatement[] { new ManagedAssignment(1, alias, obj) } : []),
                    .. (mode == "reset" ? new ManagedStatement[] { new ManagedStore(1, obj, zero) } : []),
                    new ManagedBranch(2, new ComparisonValue(Cond.Eq, input, zero, types.Boolean), new(2, []), new(3, []))]),
                new(2, [new ManagedReturn(3, null)]), new(3, [new ManagedReturn(4, null)])]);
            var rewritten = SourceNonNullReceivers.FoldBranches(guarded).Blocks[1].Statements.Last();
            if (mode is "join" or "addressed") a.True(rewritten is ManagedBranch, $"{mode} 不沿用单边事实");
            else a.True(rewritten is ManagedJump jump && jump.Edge.Target == (mode is "null" or "reset" ? 2UL : 3UL), $"{mode} 按当前引用事实选择分支");
        }
        return a.Finish("source-type-tests");
    }
}
