using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>ECMA-335 III.4.18；手写 CIL 与 CLR 委托绑定，不读取业务方法的机器码或恢复结果。</summary>
internal static class VirtualDelegateCheck
{
    [Command("virtual-delegate", "虚方法指针的独立分派与判空检查", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var a = new Assertions();
        var dynamic = new System.Reflection.Emit.DynamicMethod("Bind", typeof(Func<string>), [typeof(object)]);
        var clr = dynamic.GetILGenerator();
        clr.Emit(System.Reflection.Emit.OpCodes.Ldarg_0);
        clr.Emit(System.Reflection.Emit.OpCodes.Dup);
        clr.Emit(System.Reflection.Emit.OpCodes.Ldvirtftn, typeof(object).GetMethod("ToString")!);
        clr.Emit(System.Reflection.Emit.OpCodes.Newobj, typeof(Func<string>).GetConstructor([typeof(object), typeof(IntPtr)])!);
        clr.Emit(System.Reflection.Emit.OpCodes.Ret);
        var bind = dynamic.CreateDelegate<Func<object, Func<string>>>();
        foreach (var target in new object[] { new object(), "derived" })
        {
            var callback = bind(target);
            a.True(ReferenceEquals(target, callback.Target), "CLR 保留绑定对象");
            a.Equal(target.GetType(), callback.Method.DeclaringType, "CLR 按实际类型绑定重写方法");
            a.Equal(target.ToString(), callback(), "CLR 执行正确回调");
        }

        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var index = new WorldIndex(facts, types);
        var skeleton = new Skeleton(facts.Model);
        var interpreter = new CilInterpreter(new CecilModel(facts.Model, skeleton), index);
        var targetMethod = new MethodRef(types.Corlib("System.Object").Definition.Methods.Single(m => m.Name == "ToString" && m.Parameters.Count == 0), [], []);
        var definition = skeleton.Method(targetMethod.Method);
        definition.Body = new MethodBody(definition);
        var il = definition.Body.GetILProcessor();
        var derived = il.Create(OpCodes.Ldstr, "override");
        il.Emit(OpCodes.Ldarg_0);
        il.Emit(OpCodes.Ldvirtftn, definition);
        il.Emit(OpCodes.Ldftn, definition);
        il.Emit(OpCodes.Ceq);
        il.Emit(OpCodes.Brfalse, derived);
        il.Emit(OpCodes.Ldstr, "base");
        il.Emit(OpCodes.Ret);
        il.Append(derived);
        il.Emit(OpCodes.Ret);
        foreach (var kind in new[] { "base", "override", "null" })
        {
            var world = new World(index, 17, new Hints([], []), null);
            var receiver = kind == "base" ? world.Instance(types.Corlib("System.Object"), "receiver", 0)
                : kind == "override" ? world.String("derived") : 0;
            var expected = kind == "null" ? "" : $"return 0x{world.String(kind):x}";
            var side = interpreter.Run(world, definition, targetMethod, [StackValue.O(receiver)]);
            if (kind == "null") a.True(side.Result?.StartsWith("throw @", StringComparison.Ordinal) == true
                && side.Events.Last().Text.StartsWith("throw System.NullReferenceException @", StringComparison.Ordinal), "ldvirtftn 在取方法指针时判空");
            else a.Equal(expected, side.Result, $"ldvirtftn 的 {kind} 选择不同于直接 ldftn");
        }
        return a.Finish("virtual-delegate");
    }
}
