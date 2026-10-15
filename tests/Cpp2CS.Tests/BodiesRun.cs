using System.Diagnostics;
using System.Text.Json;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;

namespace Cpp2CS.Tests;

/// <summary>全量恢复并写出可支持的方法体；清单逐项区分恢复失败与 CIL 输出，不把依赖骨架计为恢复。</summary>
internal static class BodiesRun
{
    public static int Run(string binary, string metadata, string directory, string? selector)
    {
        var model = ModelCheck.Load(binary, metadata);
        var session = new RecoverySession(model);
        var skeleton = new Skeleton(model);
        var namespaces = selector?.Split(',') ?? ["Sekai.Mysekai", "Sekai.Api"];
        var cases = Corpus.Cases(model, namespaces);
        var definitions = model.Methods.Where(m => Corpus.InNamespaces(m.Owner, namespaces)).ToArray();
        var represented = cases.Select(c => c.Method.Method).ToHashSet();
        var missing = definitions.Where(m => !m.IsAbstract && !represented.Contains(m)).ToArray();
        Directory.CreateDirectory(directory);
        File.WriteAllLines(Path.Combine(directory, "missing-methods.jsonl"), missing.Select(m => JsonSerializer.Serialize(new
            { methodIndex = m.Index, method = m.ToString(), reason = "元数据有方法定义，但没有代码 case" })));
        Console.WriteLine($"方法定义 {definitions.Length}  抽象 {definitions.Count(m => m.IsAbstract)}  无代码 {missing.Length}");
        using var report = new StreamWriter(Path.Combine(directory, "manifest.jsonl"));
        var reasons = new Dictionary<string, int>();
        var emitted = new HashSet<int>();
        var accessorDependencies = new HashSet<int>();
        var constructorDependencies = new HashSet<int>();
        var constructorCases = 0;
        int accessorCases = 0, accessorUses = 0;
        int recoveredCount = 0, emittedCases = 0;
        var watch = Stopwatch.StartNew();
        foreach (var (address, method) in cases)
        {
            BodyRecoveryResult result;
            string? outputProblem = null;
            if (session.Functions.At(address) is not { } range || range.Start != address)
                result = new(null, [new(address, "没有函数边界")]);
            else result = BodyRecovery.Recover(session, session.Analyze(method, address, range));
            if (result.Body is { } body)
            {
                recoveredCount++;
                outputProblem = BodyEmitter.Emit(skeleton, session.Types, body);
                if (outputProblem is null)
                {
                    emitted.Add(method.Method.Index); emittedCases++;
                    if (body.Accessors.Count > 0) accessorCases++;
                    accessorUses += body.Accessors.Count;
                    accessorDependencies.UnionWith(body.Accessors.Select(a => a.Proof.Method.Method.Index));
                    if (body.Constructors.Count > 0) constructorCases++;
                    constructorDependencies.UnionWith(body.Constructors.Select(c => c.Body.Method.Method.Index));
                }
            }
            foreach (var reason in result.Problems.Select(p => p.Reason).Append(outputProblem).Where(p => p is not null))
            {
                var category = reason!.Split(' ', ':')[0];
                reasons[category] = reasons.GetValueOrDefault(category) + 1;
            }
            report.WriteLine(JsonSerializer.Serialize(new
            {
                address = $"0x{address:x}", methodIndex = method.Method.Index, method = method.ToString(),
                assembly = method.Method.Owner.Assembly,
                managedBody = result.Body is not null, cilEmitted = result.Body is not null && outputProblem is null,
                calls = result.Body is { } calledBody ? Calls(calledBody)
                    .Select(c => new { methodIndex = c.Method.Method.Index, method = c.Method.ToString(), tail = c.Tail }) : null,
                allocations = result.Body?.Blocks.SelectMany(b => b.Statements).Select(s => (s.Address, Value: s switch
                    { ManagedAssignment a => a.Value, ManagedReturn r => r.Value, _ => null }))
                    .Where(a => a.Value is ObjectAllocationValue or NewObjectValue)
                    .Select(a => new { address = $"0x{a.Address:x}", type = a.Value!.Type.ToString(), constructor = (a.Value as NewObjectValue)?.Constructor.ToString() }),
                accessors = result.Body?.Accessors.Select(a => new
                {
                    address = $"0x{a.Address:x}", accessorAddress = $"0x{a.Proof.Address:x}", methodIndex = a.Proof.Method.Method.Index,
                    method = a.Proof.Method.ToString(), field = a.Proof.Field.ToString(), setter = a.Proof.IsSetter,
                }),
                constructors = result.Body?.Constructors.Select(c => new
                {
                    address = $"0x{c.Address:x}", methodIndex = c.Body.Method.Method.Index, method = c.Body.Method.ToString(),
                }),
                problems = result.Problems.Select(p => new { address = $"0x{p.Address:x}", reason = p.Reason }), outputProblem,
            }));
        }
        report.Flush();
        Console.WriteLine($"case {cases.Count}  托管方法体 {recoveredCount}  CIL 输出 {emittedCases}  方法定义 {emitted.Count}  用时 {watch.ElapsedMilliseconds} ms");
        Console.WriteLine($"内联访问器 case {accessorCases}  替换位置 {accessorUses}  依赖方法 {accessorDependencies.Count}");
        Console.WriteLine($"构造恢复 case {constructorCases}  依赖方法 {constructorDependencies.Count}");
        foreach (var (reason, count) in reasons.OrderByDescending(p => p.Value).Take(20)) Console.WriteLine($"  {count,8} {reason}");
        var assemblies = Path.Combine(directory, "assemblies");
        skeleton.Write(assemblies);
        // 使用写出后的 token 回读实际方法体，避免仅以恢复计数声称已生成。
        var written = emitted.Union(accessorDependencies).Union(constructorDependencies).ToArray();
        foreach (var group in written.Select(index => skeleton.Method(model.Methods[index])).GroupBy(m => m.Module.Name))
        {
            using var saved = Mono.Cecil.AssemblyDefinition.ReadAssembly(Path.Combine(assemblies, group.Key));
            foreach (var original in group)
            {
                var loaded = (Mono.Cecil.MethodDefinition)saved.MainModule.LookupToken(original.MetadataToken);
                if (!loaded.HasBody || !loaded.Body.Instructions.Select(i => i.OpCode.Code).SequenceEqual(original.Body.Instructions.Select(i => i.OpCode.Code)))
                    throw new InvalidOperationException($"写出的方法体与内存不符: {loaded}");
            }
        }
        Console.WriteLine($"CIL 回读 {written.Length} 个方法定义通过（含恢复依赖）");
        var sourceDirectory = Path.Combine(directory, "src");
        Directory.CreateDirectory(sourceDirectory);
        var invalid = Path.GetInvalidFileNameChars();
        var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        var sourceCount = 0;
        foreach (var imageName in cases.Select(c => c.Method.Method.Owner.Assembly).Distinct())
        {
            var sources = Decompilation.Decompile(Path.Combine(assemblies, imageName), assemblies,
                t => namespaces.Any(ns => t.Namespace == ns || t.Namespace.StartsWith(ns + ".", StringComparison.Ordinal)), false, recoveringBodies: true);
            foreach (var source in sources)
            {
                var name = new string((imageName + "_" + source.TypeName!).Select(c => invalid.Contains(c) ? '_' : c).ToArray());
                if (!names.Add(name)) throw new InvalidOperationException($"源码文件名冲突: {name}");
                File.WriteAllText(Path.Combine(sourceDirectory, name + ".cs"), source.Source);
            }
            sourceCount += sources.Count;
        }
        Console.WriteLine($"C# 输出 {sourceCount} 个类型文件；未恢复成员仍为骨架，真实恢复范围以 manifest.jsonl 为准");
        File.WriteAllText(Path.Combine(directory, "summary.json"), JsonSerializer.Serialize(new
        {
            binarySha256 = model.Image.Sha256, namespaces, definitions = definitions.Length, missingCode = missing.Length,
            cases = cases.Count, managedBodies = recoveredCount, cilEmittedCases = emittedCases, emittedDefinitions = emitted.Count,
            accessorCases, accessorUses, accessorDependencies = accessorDependencies.Count,
            extraAccessorDefinitions = accessorDependencies.Except(emitted).Count(),
            constructorCases, constructorDependencies = constructorDependencies.Count,
            extraConstructorDefinitions = constructorDependencies.Except(emitted).Count(),
            readBackDefinitions = written.Length, sourceFiles = sourceCount, gameRuntimeVerified = false,
        }, new JsonSerializerOptions { WriteIndented = true }));
        return cases.Count > 0 && emittedCases == cases.Count && missing.Length == 0 ? 0 : 1;
    }

    private static IEnumerable<(MethodRef Method, bool Tail)> Calls(ManagedBody body)
    {
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is ManagedCall call) yield return (call.Invocation.Method, call.Tail);
            else if (statement is ManagedAssignment { Value: NewObjectValue created }) yield return (created.Constructor, false);
        }
    }
}
