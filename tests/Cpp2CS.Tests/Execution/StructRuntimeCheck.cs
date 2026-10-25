using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>规范驱动的合成用例；不恢复、不读取任何被测方法的机器指令。</summary>
internal static partial class StructRuntimeCheck
{
    [Command("struct-runtime", "结构体 L5 独立边界检查", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var index = new WorldIndex(facts, types);
        var world = new World(index, 17, new Hints([], []), null);
        var a = new Assertions();
        using (var native = new NativeMachine(facts)) native.CheckStructTransfers(world, a);
        var task = new DefinitionRef(facts.Model.Types.Single(t => t.FullName == "Cysharp.Threading.Tasks.UniTask" && t.GenericParameters.Count == 0), []);
        var storage = world.ValueStorage(task, "padding-test");
        var leaves = index.StructAbi.Classifier.Leaves(task);
        a.True(leaves.Any(l => l.Offset == 8 && l.Size == 2), "独立布局含 UniTask.token 短叶子");
        a.True(world.Observable(storage + 9) && !world.Observable(storage + 10), "只排除 UniTask 的填充，保留 token 第二字节");
        var bytes = world.ValueBytes(task, "argument");
        var changed = bytes.ToArray(); changed[10] ^= 0xff;
        a.True(index.StructAbi.Observable(task, bytes).SequenceEqual(index.StructAbi.Observable(task, changed)), "填充变化不改变托管值");
        changed[8] ^= 1;
        a.True(!index.StructAbi.Observable(task, bytes).SequenceEqual(index.StructAbi.Observable(task, changed)), "叶子位段变化必须可观察");
        CheckFrames(world, task, a);
        CheckWriteBack(world, a);

        var skeleton = new Skeleton(facts.Model);
        var interpreter = new CilInterpreter(new CecilModel(facts.Model, skeleton), index);
        CheckBoxing(world, skeleton, interpreter, a);
        // 只借现成的元数据签名；方法体完全由下列 ECMA 指令组成，未使用该方法的恢复结果。
        foreach (var type in new TypeRef[] { task, new DefinitionRef(facts.Model.Types.Single(t => t.FullName == "UnityEngine.Vector3"), []) })
        {
            var method = facts.Model.Methods.First(m => m.Owner.GenericParameters.Count == 0 && m.GenericParameters.Count == 0 && m.ReturnType.Equals(type));
            var tested = new MethodRef(method, [], []);
            var definition = skeleton.Method(method);
            definition.Body = new MethodBody(definition) { InitLocals = true };
            var t = skeleton.Reference(definition.Module, type, definition.DeclaringType, definition);
            var local = new VariableDefinition(t);
            var copy = new VariableDefinition(t);
            definition.Body.Variables.Add(local); definition.Body.Variables.Add(copy);
            var il = definition.Body.GetILProcessor();
            il.Emit(OpCodes.Ldloca, local); il.Emit(OpCodes.Initobj, t);
            il.Emit(OpCodes.Ldloc, local); il.Emit(OpCodes.Stloc, copy);
            il.Emit(OpCodes.Ldloca, copy); il.Emit(OpCodes.Ldloc, local); il.Emit(OpCodes.Stobj, t);
            il.Emit(OpCodes.Ldloca, copy); il.Emit(OpCodes.Ldobj, t); il.Emit(OpCodes.Ret);
            var arguments = StructAbi.ArgumentTypes(tested).Select(p => interpreter.FromBytes(p, new byte[world.StorageSize(p)])).ToArray();
            var side = interpreter.Run(world, definition, tested, arguments);
            var expected = "return " + string.Join(", ", index.StructAbi.Classifier.Leaves(type).Select(_ => "0x0"));
            a.Equal(expected, side.Result, $"{type} 的 initobj/ldloca/ldobj/stobj 值复制");
        }
        return a.Finish("F3 独立值类型运行时检查");
    }

    private static void CheckWriteBack(World world, Assertions a)
    {
        var model = world.Index.Facts.Model;
        var constructors = model.Methods.Count(m => m.Name == ".ctor" && m.Owner.IsValueType);
        var outStructs = model.Methods.SelectMany(m => m.Parameters)
            .Count(p => (p.Attributes & System.Reflection.ParameterAttributes.Out) != 0
                && p.Type is ByRefRef b && Aapcs64Classifier.IsStruct(b.Element));
        Console.WriteLine($"  全元数据值类型构造器 {constructors}，显式 out 结构体参数 {outStructs}（只按签名计数）");
        var vector = new DefinitionRef(model.Types.Single(t => t.FullName == "UnityEngine.Vector2"), []);
        var constructor = new MethodRef(vector.Definition.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 2), [], []);
        var left = new CilSide(world); var right = new CilSide(world);
        var x = World.StackBase + 0x1000; var y = World.StackBase + 0x90000;
        left.Write(x, new byte[world.StorageSize(vector)]);
        right.Write(y, Enumerable.Repeat((byte)0xa5, world.StorageSize(vector)).ToArray());
        byte[][] Args(ulong p) => [StructAbi.Bytes(p, 8), new byte[4], new byte[4]];
        world.Index.StructAbi.WriteBack(left, constructor, 3, Args(x));
        world.Index.StructAbi.WriteBack(right, constructor, 3, Args(y));
        var expected = world.CallWriteBytes(3, 0, vector);
        var actual = new byte[expected.Length]; left.Read(x, actual);
        a.True(actual.SequenceEqual(expected), "构造器 this 后值由独立签名规则合成");
        right.Read(y, actual);
        a.True(actual.SequenceEqual(expected), "后值与物理地址和先前内容无关");
        var getter = new MethodRef(vector.Definition.Methods.Single(m => m.Name == "get_sqrMagnitude"), [], []);
        world.Index.StructAbi.WriteBack(left, getter, 4, [StructAbi.Bytes(x, 8)]);
        left.Read(x, actual);
        a.True(actual.SequenceEqual(expected), "普通值类型 this 不被误判为写回参数");
        var task = new DefinitionRef(model.Types.Single(t => t.FullName == "Cysharp.Threading.Tasks.UniTask" && t.GenericParameters.Count == 0), []);
        var first = world.CallWriteBytes(4, 0, task);
        a.True(ReferenceEquals(first, world.CallWriteBytes(4, 0, task)), "含引用叶子的后值在两侧共用一次分配");
    }

    private static void CheckFrames(World world, TypeRef task, Assertions a)
    {
        var left = new CilSide(world); var right = new CilSide(world);
        var x = World.StackBase + 0x200; var y = World.StackBase + 0x80000;
        var bytes = world.ValueBytes(task, "local-ref");
        left.Write(x, bytes); right.Write(y, bytes);
        ulong[] Observe(Side side, params ulong[] addresses) => world.Index.StructAbi.ObservableArguments(side,
            addresses.Select(_ => (TypeRef)new ByRefRef(task)).ToArray(), addresses.Select(p => StructAbi.Bytes(p, 8)).ToArray());
        a.True(Observe(left, x).SequenceEqual(Observe(right, y)), "局部物理地址独立，全部叶子相同");
        right.WriteValue(y + 8, StructAbi.Bits(bytes.AsSpan(8, 2)) ^ 1, 2);
        a.True(!Observe(left, x).SequenceEqual(Observe(right, y)), "局部 ref 叶子变异可见");
        right.Write(y, bytes); right.Write(y + 0x100, bytes);
        a.True(!Observe(left, x, x).SequenceEqual(Observe(right, y, y + 0x100)), "相同内容的异址不能冒充同址别名");
        a.True(Observe(left, x, x).SequenceEqual(Observe(right, y, y)), "同址别名与物理地址无关");
        left.Write(x + 8, bytes); right.Write(y + 8, bytes);
        a.True(Observe(left, x, x + 8).SequenceEqual(Observe(right, y, y + 8)), "部分重叠保留相对偏移");
        a.True(!Observe(left, x, x + 8).SequenceEqual(Observe(right, y, y + 0x100)), "部分重叠不能变成互不重叠");
    }
}

internal sealed partial class NativeMachine
{
    internal void CheckStructTransfers(World world, Assertions a)
    {
        side = new NativeSide(world, uc);
        uc.SetReg(Unicorn.RegSp, World.StackBase + 0x80000);
        var integer = new Aapcs64Classifier.Shape(Aapcs64Classifier.Kind.Aggregate, 16, 8);
        var packed = Aapcs64Classifier.Allocate(integer, new());
        var bytes = Enumerable.Range(1, 16).Select(i => (byte)i).ToArray();
        PutLocation(packed, bytes);
        a.Equal(0x0807060504030201UL, uc.Reg(Unicorn.X(0)), "小端第一片 x0");
        a.Equal(0x100f0e0d0c0b0a09UL, uc.Reg(Unicorn.X(1)), "小端第二片 x1");
        foreach (var width in new[] { 32, 64 })
        {
            var hfa = new Aapcs64Classifier.Shape(Aapcs64Classifier.Kind.Aggregate, 3 * width / 8, width / 8, width, [0, width / 8, 2 * width / 8]);
            var location = Aapcs64Classifier.Result(hfa)!;
            var value = Enumerable.Range(1, hfa.Size).Select(i => (byte)i).ToArray();
            PutLocation(location, value);
            for (var i = 0; i < 3; i++) a.Equal(StructAbi.Bits(value.AsSpan(i * width / 8, width / 8)), uc.Reg(Unicorn.D(i)), $"{width} 位 HFA v{i}");
        }
        var large = new Aapcs64Classifier.Shape(Aapcs64Classifier.Kind.Aggregate, 24, 8);
        var data = Enumerable.Range(1, 24).Select(i => (byte)i).ToArray();
        uc.Write(ReturnBuffer, data);
        foreach (var cursor in new[] { new Aapcs64Classifier.Cursor(), new Aapcs64Classifier.Cursor { Gpr = 8, Stack = 16 } })
        {
            var location = Aapcs64Classifier.Allocate(large, cursor);
            PutLocation(location, StructAbi.Bytes(ReturnBuffer, 8), pointer: true);
            a.True(ReadLocation(location).SequenceEqual(data), $"大结构副本指针 {location}");
        }
        uc.SetReg(Unicorn.X(8), ReturnBuffer);
        a.True(ReadLocation(Aapcs64Classifier.Result(large)!).SequenceEqual(data), "x8 结果缓冲区");
    }
}
