using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>先普查全程序 Invoke 签名；随后以手写 CIL 对照运行时 Invoke，不读取业务方法的恢复结果。</summary>
internal static class DelegateStructCheck
{
    [Command("delegate-struct", "全程序委托结构体签名与独立 Invoke 对照", Arguments = "<binary> <metadata> <输出目录> [--census-only]", Gate = Gate.ImageOutput)]
    private static int CommandLine(string binary, string metadata, string output, string[] options) => options switch
    {
        [] => Run(binary, metadata, output, false),
        ["--census-only"] => Run(binary, metadata, output, true),
        _ => Commands.Usage(),
    };

    public static int Run(string binary, string metadata, string output, bool censusOnly)
    {
        var facts = FactsBuilder.Build(binary, metadata, Console.Error.WriteLine);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var index = new WorldIndex(facts, types);
        var methods = facts.Registrations.Entries.Select(e => e.Method).OfType<MethodRef>().Distinct()
            .Where(DelegateModel.IsInvoke).ToArray();
        var rows = new List<string> { "method\tcategory\tparameters\treturn" };
        var candidates = new List<MethodRef>();
        var counts = new Dictionary<string, int>();
        foreach (var method in methods)
        {
            string category, parameters = "", result = "";
            try
            {
                var signature = index.StructAbi.Signature(method);
                var hasStruct = StructAbi.ArgumentTypes(method).Append(method.Method.ReturnType.Substitute(method.TypeArguments, method.MethodArguments))
                    .Any(t => types.Kind(t) == TypeKind.Struct);
                var supported = signature.Parameters.All(p => !p.Indirect && p.StackOffset is null)
                    && signature.MethodInfo.StackOffset is null
                    && (signature.Return is null || signature.Return is { Indirect: false, StackOffset: null, Pieces.Length: 1 }
                        && types.Kind(method.Method.ReturnType.Substitute(method.TypeArguments, method.MethodArguments)) != TypeKind.Struct);
                category = hasStruct ? supported ? "结构体寄存器参数" : "结构体其他ABI" : "标量";
                parameters = string.Join(";", signature.Parameters.Select(p => p.ToString()));
                result = signature.Return?.ToString() ?? "void";
                if (hasStruct && supported && method.TypeArguments.Count == 0 && method.Method.Owner.GenericParameters.Count == 0
                    && method.Method.Address != 0) candidates.Add(method);
            }
            catch (Unsupported e) { category = "残余"; parameters = e.Message; }
            counts[category] = counts.GetValueOrDefault(category) + 1;
            rows.Add($"{method}\t{category}\t{parameters}\t{result}");
        }
        Directory.CreateDirectory(output);
        File.WriteAllLines(Path.Combine(output, "delegate-signatures.tsv"), rows);
        Console.WriteLine($"全程序 Invoke 签名 {methods.Length}；" + string.Join("；", counts.OrderBy(p => p.Key).Select(p => $"{p.Key} {p.Value}")));
        var samples = candidates.GroupBy(DelegateModel.Signature).Select(g => g.First()).OrderBy(m => m.Method.Address).Take(8).ToArray();
        File.WriteAllLines(Path.Combine(output, "samples.tsv"), samples.Select(m => $"0x{m.Method.Address:x}\t{m}"));
        foreach (var method in samples) Console.WriteLine($"样例 0x{method.Method.Address:x} {method}");
        if (censusOnly) return 0;
        var assertions = new Assertions();
        assertions.Equal(8, samples.Length, "结构体 Invoke 独立签名样例数");
        var skeleton = new Skeleton(facts.Model);
        var interpreter = new CilInterpreter(new CecilModel(facts.Model, skeleton), index);
        using var native = new NativeMachine(facts);
        foreach (var method in samples)
        {
            var definition = skeleton.Method(method.Method);
            definition.Body = new MethodBody(definition);
            var il = definition.Body.GetILProcessor();
            il.Emit(OpCodes.Ldarg_0);
            foreach (var parameter in definition.Parameters) il.Emit(OpCodes.Ldarg, parameter);
            il.Emit(OpCodes.Callvirt, definition);
            il.Emit(OpCodes.Ret);
            var argumentTypes = StructAbi.ArgumentTypes(method);
            for (var seed = 0; seed < 32; seed++)
            {
                var world = new World(index, seed, new Hints([], []), method.DeclaringType);
                var bytes = argumentTypes.Select((type, i) => i == 0
                    ? StructAbi.Bytes(world.Instance((DefinitionRef)method.DeclaringType, "delegate", 0), 8)
                    : world.ValueBytes(type, $"arg{i}")).ToArray();
                var values = argumentTypes.Select((type, i) => interpreter.FromBytes(type, bytes[i])).ToArray();
                var cil = interpreter.Run(world, definition, method, values);
                var machine = native.Run(world, method, index.StructAbi.Signature(method), bytes, cil.Callees);
                assertions.Equal<string?>(null, Trace.Difference(world, machine, cil), $"0x{method.Method.Address:x} {method} seed={seed}");
                // 同一真实 Invoke 的原生输入不变，仅扰动 CIL 的一个结构体叶子；必须被事件比较检出。
                var changed = bytes.Select(b => b.ToArray()).ToArray();
                var parameter = Array.FindIndex(argumentTypes, t => types.Kind(t) == TypeKind.Struct);
                var leaf = index.StructAbi.Classifier.Leaves(argumentTypes[parameter]).First();
                changed[parameter][leaf.Offset] ^= 1;
                var changedValues = argumentTypes.Select((type, i) => interpreter.FromBytes(type, changed[i])).ToArray();
                var different = interpreter.Run(world, definition, method, changedValues);
                assertions.True(Trace.Difference(world, machine, different) is not null, "委托结构体叶子位变化必须检出");
            }
        }
        return assertions.Finish("delegate-struct");
    }
}
