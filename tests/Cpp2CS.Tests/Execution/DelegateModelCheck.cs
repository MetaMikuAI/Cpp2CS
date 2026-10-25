using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>直接对运行时生成的 Invoke 做差分，手写 CIL 不经过 L2/L3/L4，防止恢复规则与对照器互相印证。</summary>
internal static class DelegateModelCheck
{
    [Command("delegate-model", "独立 Invoke 原生实现与手写 CIL 对照", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var index = new WorldIndex(facts, types);
        var skeleton = new Skeleton(facts.Model);
        var interpreter = new CilInterpreter(new CecilModel(facts.Model, skeleton), index);
        using var native = new NativeMachine(facts);
        var assertions = new Assertions();
        var methods = facts.Model.Methods.Where(m => m.Name == "Invoke" && m.Address != 0 && m.Owner.GenericParameters.Count == 0)
            .Select(m => new MethodRef(m, [], [])).Where(DelegateModel.IsInvoke)
            .Where(m => index.Abi.Classify(m, out _) is { } signature
                && signature.Arguments.All(a => a.Passing == Passing.Registers && a.Pieces.Length == 1 && types.Kind(a.Type) is not (TypeKind.Struct or TypeKind.Pointer or null))
                && (signature.Return is null || signature.Return is { Passing: Passing.Registers, Pieces.Length: 1 } r && types.Kind(r.Type) is not (TypeKind.Struct or TypeKind.Pointer or null)))
            .GroupBy(DelegateModel.Signature).Select(g => g.First()).Take(8).ToArray();
        assertions.Equal(8, methods.Length, "独立 Invoke 签名样例数");
        foreach (var method in methods)
        {
            var signature = index.StructAbi.Signature(method);
            var argumentTypes = StructAbi.ArgumentTypes(method);
            var definition = skeleton.Method(method.Method);
            definition.Body = new MethodBody(definition);
            var il = definition.Body.GetILProcessor();
            il.Emit(OpCodes.Ldarg_0);
            foreach (var parameter in definition.Parameters) il.Emit(OpCodes.Ldarg, parameter);
            il.Emit(OpCodes.Callvirt, definition);
            il.Emit(OpCodes.Ret);
            for (var seed = 0; seed < 8; seed++)
            {
                var world = new World(index, seed, new Hints([], []), method.DeclaringType);
                var bits = argumentTypes.Select((type, i) => StructAbi.Bytes(i == 0 ? world.Instance((DefinitionRef)method.DeclaringType, "delegate", 0) : world.Value(type, $"arg{i}", 0), world.StorageSize(type))).ToArray();
                var values = argumentTypes.Select((type, i) => interpreter.FromBytes(type, bits[i])).ToArray();
                var cil = interpreter.Run(world, definition, method, values);
                var machine = native.Run(world, method, signature, bits, cil.Callees);
                assertions.Equal<string?>(null, Trace.Difference(world, machine, cil), $"0x{method.Method.Address:x} {method} seed={seed}");
            }
        }
        return assertions.Finish("delegate-model");
    }
}
