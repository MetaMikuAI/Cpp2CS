using System.Globalization;
using MethodImplAttributes = System.Reflection.MethodImplAttributes;
using Mono.Cecil;
using Cpp2CS.Tests.Metrics;
using Mono.Cecil.Cil;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Pipeline;
using Cpp2CS.Native;
using Cpp2CS.Model;
using Cpp2CS.Managed;
using Cpp2CS.Recovery.MethodCopies;
using Cpp2CS.Kernel.State;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using System.Text.RegularExpressions;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Elf;

namespace Cpp2CS.Tests;

internal static class MethodCopiesCorpusChecks
{
    public const string Command = "method-copies-corpus";
    internal static ulong Address(JsonElement value) => ulong.Parse(value.GetString()!.Replace("0x", "", StringComparison.Ordinal), NumberStyles.HexNumber, CultureInfo.InvariantCulture);
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth))
        { Console.WriteLine("跳过方法副本核对：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var checks = new Assertions();
        var image = ElfImage.Load(Path.Combine(corpus, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.so"));
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var (model, registration) = ModelBuilder.Load(image, Path.Combine(corpus, "artifacts/il2cppOutput/data/Metadata/global-metadata.dat"), spec);
        var (map, problems) = RegistrationReader.Read(image, model, spec, registration.CodeRegistration, registration.MetadataRegistration);
        checks.True(problems.Count == 0, "代码地图完整");
        var facts = new GlobalFacts(image, model, map, spec, "arm64");
        var runtime = facts.RuntimeFunctions;
        var wrappers = InternalCallAssembly.Get(facts).Facts;
        bool Eligible(ulong address) => facts.Image.IsExecutable(address) && !map.ByAddress.ContainsKey(address)
            && !runtime.Entries.ContainsKey(address) && !wrappers.Direct.ContainsKey(address) && !wrappers.AmbiguousEntries.Contains(address);
        var uses = new Dictionary<ulong, HashSet<ulong>>();
        foreach (var entry in map.Entries.Where(e => e.Method?.Method.DeclaresCilBody == true && e.Kind is EntryKind.Method or EntryKind.GenericMethod).Select(e => e.Address).Distinct())
            foreach (var range in facts.FunctionsByStart[entry])
                foreach (var site in Arm64DirectCalls.InRange(image, range).Where(site => Eligible(site.Target)))
                {
                    if (!uses.TryGetValue(site.Target, out var callers)) uses.Add(site.Target, callers = []);
                    callers.Add(entry);
                }
        // 真值只用于结果核对，不进入产品识别输入。
        using var functions = InputCorpusChecks.Json(truth, "functions.arm64-v8a.json");
        var symbols = functions.RootElement.EnumerateArray().Where(f => f.GetProperty("defined").GetBoolean())
            .GroupBy(f => Address(f.GetProperty("address"))).ToDictionary(g => g.Key,
                g => g.Select(f => f.GetProperty("demangled_name").GetString() ?? f.GetProperty("name").GetString()!).ToArray());
        string Category(ulong target)
        {
            var names = symbols.GetValueOrDefault(target) ?? [];
            if (names.Any(n => n.Contains("_gshared_inline", StringComparison.Ordinal))) return "泛型共享副本";
            if (names.Any(n => n.Contains("_inline", StringComparison.Ordinal))) return "内联副本";
            if (names.Any(n => n.Contains(".cold", StringComparison.Ordinal) || n.Contains(".part.", StringComparison.Ordinal)
                || n.Contains("OUTLINED_FUNCTION", StringComparison.Ordinal) || n == "__clang_call_terminate" || n.StartsWith("__CortexA53843419_", StringComparison.Ordinal))) return "编译链接辅助片段";
            if (names.Any(n => n.Contains("il2cpp::", StringComparison.Ordinal) || n.Contains("il2cpp_codegen_", StringComparison.Ordinal)
                || n.StartsWith("il2cpp_", StringComparison.Ordinal) || n.StartsWith("Il2Cpp", StringComparison.Ordinal)
                || n.StartsWith("mono_", StringComparison.Ordinal) || n.StartsWith("SystemNative_", StringComparison.Ordinal)
                || n.StartsWith("SetGenericValueImpl(", StringComparison.Ordinal) || n.StartsWith("MethodIsStatic(", StringComparison.Ordinal)
                || n.StartsWith("UnBoxNullable_internal(", StringComparison.Ordinal))) return "目录外运行时";
            return "其他";
        }
        int Callers(IEnumerable<ulong> addresses) => addresses.Distinct().SelectMany(a => map.At(a))
            .Where(e => e.Method?.Method.DeclaresCilBody == true && e.Kind is EntryKind.Method or EntryKind.GenericMethod).Select(e => e.Method!.Method).Distinct().Count();
        foreach (var group in uses.GroupBy(p => Category(p.Key)).OrderBy(g => g.Key))
            Console.WriteLine($"未注册普查 | {group.Key} | 目标={group.Count()} | 调用方法={Callers(group.SelectMany(p => p.Value))} | 调用入口={group.SelectMany(p => p.Value).Distinct().Count()} | 目标调用方法对={group.Sum(p => Callers(p.Value))}");
        Console.WriteLine($"未注册总计 | 目标={uses.Count} | 调用方法={Callers(uses.Values.SelectMany(x => x))} | 调用入口={uses.Values.SelectMany(x => x).Distinct().Count()} | 目标调用方法对={uses.Sum(p => Callers(p.Value))}");
        var result = facts.MethodCopies;
        checks.True(ReferenceEquals(result, facts.MethodCopies), "每次运行只建立一次副本事实");
        checks.True(result.Callers.Count == uses.Count && result.Callers.All(p => uses.TryGetValue(p.Key, out var expected)
            && expected.SetEquals(p.Value)), "产品候选范围与独立普查完全一致");
        var inline = uses.Keys.Where(a => Category(a) is "内联副本" or "泛型共享副本").ToArray();
        static string[] Bases(IEnumerable<string> names) => names.Select(n => Regex.Match(n,
            @"([A-Za-z0-9_]+_m[0-9A-Fa-f]{40}(?:_gshared)?)")).Where(m => m.Success).Select(m => m.Value).Distinct().ToArray();
        // 哈希区分 C++ 泛型实例；身份真值经生成映射核对 MethodDef，规范实例可以使用不同哈希。
        using var mappings = InputCorpusChecks.Json(truth, "mappings.json");
        var bySymbol = mappings.RootElement.EnumerateArray().Where(m => m.TryGetProperty("metadata_method_id", out var id) && id.ValueKind == JsonValueKind.String
                && m.TryGetProperty("cpp_name", out var name) && name.ValueKind == JsonValueKind.String)
            .SelectMany(m => Bases([m.GetProperty("cpp_name").GetString()!]).Select(name => (Name: name, Id: m.GetProperty("metadata_method_id").GetString()!)))
            .GroupBy(p => p.Name).ToDictionary(g => g.Key, g => g.Select(p => p.Id).ToHashSet());
        var expectedDefinitions = symbols.ToDictionary(p => p.Key, p => Bases(p.Value).SelectMany(name => bySymbol.GetValueOrDefault(name) ?? []).ToHashSet());
        checks.True(inline.All(a => expectedDefinitions[a].Count > 0), "全部被调用内联副本均有生成映射给出的定义真值");
        var modelById = model.Methods.ToDictionary(RecoverySession.Identity);
        var registered = map.Entries.Where(e => e.Method is not null).Select(e => RecoverySession.Identity(e.Method!.Method)).ToHashSet();
        // 全部 _inline 符号核实候选规则，包含未被托管入口直接调用的副本。
        var inlineSymbols = symbols.Values.SelectMany(n => n).Where(n => n.Contains("_inline", StringComparison.Ordinal))
            .Select(n => (Name: n, Base: Bases([n]).FirstOrDefault())).Where(p => p.Base is not null).ToArray();
        var matchedSymbols = inlineSymbols.Where(s => bySymbol.TryGetValue(s.Base!, out var ids) && ids.Any(registered.Contains)).ToArray();
        var definitions = matchedSymbols.SelectMany(s => bySymbol[s.Base!]).Where(modelById.ContainsKey).Select(id => modelById[id]).ToHashSet();
        var aggressive = model.Methods.Where(m => (m.ImplAttributes & MethodImplAttributes.AggressiveInlining) != 0).ToArray();
        Console.WriteLine($"候选规则 | inline符号={inlineSymbols.Length} | 对应注册={matchedSymbols.Length} | 注册定义={definitions.Count} | 带特性={definitions.Count(MethodCopyAssembly.Aggressive)} | 带特性全部定义={aggressive.Length} | 有inline={aggressive.Count(definitions.Contains)}");
        foreach (var m in definitions.Where(m => !MethodCopyAssembly.Aggressive(m))) Console.WriteLine($"候选规则反例 | {RecoverySession.Identity(m)} | {m} | {m.ImplAttributes}");
        foreach (var m in aggressive.Where(m => !definitions.Contains(m))) Console.WriteLine($"候选规则反向反例 | {RecoverySession.Identity(m)} | {m}");
        using var methodTruth = InputCorpusChecks.Json(truth, "methods.json");
        var rows = methodTruth.RootElement.EnumerateArray().ToDictionary(m => m.GetProperty("id").GetString()!);
        int accessors = 0;
        using var resolver = new DefaultAssemblyResolver(); resolver.AddSearchDirectory(Path.Combine(corpus, "artifacts", "ManagedStripped"));
        foreach (var group in definitions.Where(m => !MethodCopyAssembly.Aggressive(m)).GroupBy(m => m.Owner.Assembly))
        {
            using var module = ModuleDefinition.ReadModule(Path.Combine(corpus, "artifacts", "ManagedStripped", group.Key), new ReaderParameters { AssemblyResolver = resolver });
            foreach (var method in group)
            {
                var reference = IlCompareCommand.ReferenceMethod(module, rows[RecoverySession.Identity(method)]);
                var code = reference.Body.Instructions.Where(i => i.OpCode.Code != Code.Nop).Select(i => i.OpCode.Code).ToArray();
                bool simple = code is [Code.Ldarg_0, Code.Ldfld, Code.Ret] or [Code.Ldsfld, Code.Ret]
                    or [Code.Ldarg_0, Code.Ldarg_1, Code.Stfld, Code.Ret] or [Code.Ldarg_0, Code.Stsfld, Code.Ret];
                checks.True(simple, $"无强制内联特性的符号 {RecoverySession.Identity(method)} 是单字段读取或写入：{string.Join(',', code)}");
                if (simple) accessors++;
            }
        }
        Console.WriteLine($"候选实际规则 | 强制内联={definitions.Count(MethodCopyAssembly.Aggressive)} | 单字段访问器={accessors} | 总定义={definitions.Count}");
        checks.True(definitions.All(MethodCopyAssembly.EligibleCandidate), "全部内联符号对应的注册定义满足候选签名上界");
        foreach (var address in result.Callers.Keys.Order()) result.Facts.At(address);
        int errors = 0, unique = 0, ambiguous = 0;
        foreach (var (entry, candidates) in result.Facts.Entries)
        {
            var expected = expectedDefinitions.GetValueOrDefault(entry) ?? [];
            var matching = candidates.Where(c => expected.Contains(RecoverySession.Identity(c.Entry.Method!.Method))).ToArray();
            if (inline.Contains(entry))
            {
                checks.True(matching.Length > 0, $"副本 0x{entry:x} 的候选集含真值定义");
                if (matching.Length == 0) errors++;
            }
            // 唯一全局身份直接核对；歧义集合的实际采纳在调用点逐个核对。
            if (candidates.Select(c => c.Entry.Method).Distinct().Count() == 1)
            {
                bool valid = inline.Contains(entry) && matching.Length == candidates.Length;
                if (!valid) errors++;
                checks.True(valid, $"副本 0x{entry:x} 的唯一定义身份与生成映射真值一致");
                unique++;
            }
            else ambiguous++;
            Console.WriteLine($"副本 | 0x{entry:x} | 候选={candidates.Length} | 定义={string.Join(',', candidates.Select(c => RecoverySession.Identity(c.Entry.Method!.Method)).Distinct())} | {string.Join(" / ", symbols.GetValueOrDefault(entry) ?? [])}");
        }
        Console.WriteLine($"事实计算完成 | 秒={result.Seconds:F3} | 候选上限={MethodCopySurvey.CandidateLimit} | 命中上限={result.CappedTargets}");
        var audit = AuditAdoptions(facts, result, symbols, expectedDefinitions, checks);
        errors += audit.Errors;
        Console.WriteLine($"调用点身份 | 采纳={audit.Adopted} | 未消歧={audit.Unresolved} | 不能提升调用方={audit.Unliftable} | 错误={audit.Errors}");
        var recognized = result.Facts.Entries.Keys.Where(inline.Contains).ToArray();
        foreach (var category in new[] { "内联副本", "泛型共享副本" })
        {
            var all = inline.Where(a => Category(a) == category).ToArray(); var found = all.Where(result.Facts.Entries.ContainsKey).ToArray();
            Console.WriteLine($"覆盖 | {category} | 副本={found.Length}/{all.Length} | 调用方法对={found.Sum(a => Callers(uses[a]))}/{all.Sum(a => Callers(uses[a]))}");
        }
        foreach (var group in inline.Where(result.Missing.ContainsKey).GroupBy(a => result.Missing[a].Code + "/" + (result.Missing[a].Cause?.Code ?? "无下级原因")).OrderBy(g => g.Key))
            Console.WriteLine($"未认出 | {group.Key} | 副本={group.Count()} | 调用方法对={group.Sum(a => Callers(uses[a]))}");
        Console.WriteLine($"副本核对 | 已认={recognized.Length}/{inline.Length} | 唯一={unique} | 歧义集合={ambiguous} | 错误={errors} | 提升目标={result.LiftedTargets} | 提升参考={result.LiftedRegistered} | 事实用时={result.Seconds:F3}s | 分项={JsonSerializer.Serialize(result.Timings)}");
        checks.True(recognized.Length > 0, "至少一个实际副本取得托管体同构身份凭据");
        checks.True(errors == 0, "副本身份核对错误数为零");
        Console.WriteLine($"候选预算 | 上限={MethodCopySurvey.CandidateLimit} | 命中上限={result.CappedTargets} | 最大候选={result.CandidateCounts.Values.DefaultIfEmpty().Max()}");
        checks.True(result.Seconds <= 15, "全局副本事实用时不超过十五秒");
        var output = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", "method-copies-corpus.local.json");
        File.WriteAllText(output, JsonSerializer.Serialize(uses.OrderBy(p => p.Key).Select(p => new
        { Entry = p.Key, Category = Category(p.Key), Names = symbols.GetValueOrDefault(p.Key) ?? [], Callers = p.Value.Order().ToArray(), CallerMethods = p.Value.SelectMany(a => map.At(a)).Where(e => e.Method is not null).Select(e => RecoverySession.Identity(e.Method!.Method)).Distinct().Order().ToArray(),
            Candidates = result.Facts.Entries.GetValueOrDefault(p.Key).IsDefault ? null : result.Facts.Entries[p.Key].Select(c => new { c.RegisteredEntry, Method = RecoverySession.Identity(c.Entry.Method!.Method) }).ToArray(),
            CandidateCount = result.CandidateCounts.GetValueOrDefault(p.Key), Missing = result.Missing.GetValueOrDefault(p.Key) }), new JsonSerializerOptions { WriteIndented = true }));
        checks.True(uses.Count > 0, "普查覆盖非空");
        return checks.Finish("方法副本语料核对");
    }
    private static void ExplainMissing(GlobalFacts facts, MethodCopySurvey result, Dictionary<ulong, string[]> symbols,
        Dictionary<ulong, HashSet<string>> expectedDefinitions, FrontendStage frontend)
    {
        var recovery = new IntegerRecoveryStage(frontend);
        var diagnostics = new List<(ulong Address, string Method, Cpp2CS.Native.Terms.Reason Reason)>();
        StageResult<ManagedBody> Recover(CodeEntry entry)
        {
            var context = new MethodContext(entry.Method!.Method, entry, facts);
            return frontend.Run(entry, context) switch
            {
                Completed<NativeFunction> function => recovery.Run(function.Value, context),
                Missing<NativeFunction> missing => new Missing<ManagedBody>(missing.Hole),
                _ => throw new InvalidOperationException("未知前端结果"),
            };
        }
        foreach (var address in result.Missing.Keys.Order())
        {
            var names = symbols.GetValueOrDefault(address) ?? [];
            if (!names.Any(n => n.Contains("_inline", StringComparison.Ordinal))) continue;
            var expected = expectedDefinitions[address];
            var references = facts.CodeMap.Entries.Where(e => e.Method is not null
                && expected.Contains(RecoverySession.Identity(e.Method.Method)))
                .GroupBy(e => e.Method!.Method).Select(g => RecoverySession.SelectEntry(g.Key, g));
            foreach (var entry in references)
            {
                Console.WriteLine($"真值恢复开始 | 0x{address:x} | {RecoverySession.Identity(entry.Method!.Method)}");
                Cpp2CS.Native.Terms.Reason why;
                if (GenericWitness.IsGeneric(entry.Method!.Method) && (entry.Kind != EntryKind.GenericMethod || !GenericWitness.IsCanonical(entry.Method)))
                    why = new("method-copy.witness", "真值定义没有规范引用实例，不能用其他实例代替。");
                else
                {
                    var copy = Recover(entry with { Address = address });
                    var registered = Recover(entry);
                    if (copy is Missing<ManagedBody> copyHole) why = new("method-copy.copy-hole", copyHole.Hole.Reason.Message, copyHole.Hole.Reason);
                    else if (registered is Missing<ManagedBody> referenceHole) why = new("method-copy.registered-hole", referenceHole.Hole.Reason.Message, referenceHole.Hole.Reason);
                    else why = ManagedBodyIsomorphism.Compare(((Completed<ManagedBody>)copy).Value, ((Completed<ManagedBody>)registered).Value).Difference
                        ?? new("method-copy.discovery", "真值两体同构，但索引或候选预算没有纳入。");
                }
                Console.WriteLine($"真值恢复完成 | 0x{address:x} | {why.Code}/{why.Cause?.Code}");
                diagnostics.Add((address, RecoverySession.Identity(entry.Method.Method), why));
            }
        }
        foreach (var group in diagnostics.GroupBy(d => d.Reason.Code + "/" + d.Reason.Cause?.Code).OrderBy(g => g.Key))
            Console.WriteLine($"真值未认出 | {group.Key} | 副本={group.Select(d => d.Address).Distinct().Count()}");
        File.WriteAllText(Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", "method-copies-missing.local.json"),
            JsonSerializer.Serialize(diagnostics.Select(d => new { d.Address, d.Method, d.Reason }), new JsonSerializerOptions { WriteIndented = true }));
    }

    private static (int Errors, int Adopted, int Unresolved, int Unliftable) AuditAdoptions(GlobalFacts facts, MethodCopySurvey result,
        Dictionary<ulong, string[]> symbols, Dictionary<ulong, HashSet<string>> expectedDefinitions, Assertions checks)
    {
        var pointer = facts.Image.PointerWidth;
        var layouts = new FieldLayouts(facts.Spec, pointer, pointer);
        var binder = new MethodBinder(new(layouts, pointer * 8), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(facts.Spec.Layout.UnityVersion, facts.Spec.Layout.Triple, facts.Spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingCodeMap(facts.CodeMap, result.Facts), new RuntimeFunctionMap(facts.RuntimeFunctions), catalog, InternalCallAssembly.Get(facts).Facts);
        var flow = NoReturnCorpusChecks.Analyze(facts.Image);
        var instructions = new Arm64InstructionSet(facts.Image);
        var frontend = new FrontendStage([new FrontendProvider("arm64", _ => new(instructions, Arm64Registers.Convention, flow))]);
        ExplainMissing(facts, result, symbols, expectedDefinitions, frontend);
        int errors = 0, adopted = 0, unresolved = 0, unliftable = 0;
        foreach (var address in result.Facts.Entries.Keys.SelectMany(a => result.Callers[a]).Distinct().Order())
        foreach (var entry in facts.CodeMap.At(address).Where(e => e.Method?.Method.DeclaresCilBody == true && (e.Kind == EntryKind.Method
            || e.Kind == EntryKind.GenericMethod && (GenericWitness.IsCanonical(e.Method) || GenericWitness.IsValueInstance(e.Method))))
            .DistinctBy(e => e.Method!.Method))
        {
            var method = MethodRef.Open(entry.Method!.Method);
            var kind = entry.Kind == EntryKind.GenericMethod ? BindingEntryKind.SharedGeneric : BindingEntryKind.Ordinary;
            var signature = binder.Definition(method, kind, entry.Method).Value;
            if (signature is null) continue;
            var context = new MethodContext(method.Method, entry, facts);
            var lifted = frontend.Run(entry, context);
            if (lifted is not Completed<NativeFunction> body) { unliftable++; continue; }
            ITypeLayouts concreteLayouts = GenericWitness.IsGeneric(method.Method) ? new GenericWitness(method, entry.Method, layouts) : layouts;
            var transformed = StructureRecovery.Run(body.Value, context, binder, kind, concreteLayouts);
            var state = new StateQueries(new ManagedCallEffects(calls), image: facts.Image);
            var types = new ManagedTypes(facts.Model, concreteLayouts, pointer);
            var names = new ValueNamingQuery(state, calls, transformed.Names, facts.Spec, binder, signature,
                new MetadataRgctxDecoder(facts), concreteLayouts as GenericWitness, types.Object, stringType: types.String);
            var locations = new ManagedLocationQuery(state, names, concreteLayouts, facts.Spec);
            var query = locations.CreateContext(transformed.Function);
            foreach (var call in transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
                .Where(c => c.Target is ImageFunction target && result.Facts.Entries.ContainsKey(target.EntryOffset)))
            {
                var target = ((ImageFunction)call.Target).EntryOffset;
                var classified = query.Get(calls, call.Identity).Value;
                var candidates = classified.Candidates!.Candidates;
                MethodRef? selected = null;
                if (candidates.Any(c => c.Entry.Kind == BindingEntryKind.SharedGeneric))
                {
                    var shared = query.Get(new SharedCallQuery(binder, calls, names, new(state)), call.Identity);
                    if (shared.IsSuccess) selected = shared.Value.Method;
                }
                else if (candidates.Length == 1 && candidates[0].Binding.Success) selected = candidates[0].Entry.Method;
                else if (candidates.All(c => c.Entry.Kind == BindingEntryKind.Ordinary))
                {
                    var direct = query.Get(new DirectCallQuery(calls, names, new(state), types), call.Identity);
                    if (direct.IsSuccess && direct.Value.Binding.Success) selected = direct.Value.Entry.Method;
                }
                if (selected is null) { unresolved++; continue; }
                adopted++;
                var expected = expectedDefinitions.GetValueOrDefault(target) ?? [];
                bool valid = expected.Contains(RecoverySession.Identity(selected.Method)) && (symbols.GetValueOrDefault(target) ?? []).Any(n => n.Contains("_inline", StringComparison.Ordinal));
                if (!valid) errors++;
                checks.True(valid, $"调用方 0x{address:x} 在 0x{call.Trace?.NativeAddress:x} 对副本 0x{target:x} 实际采纳的身份与真值一致");
            }
        }
        return (errors, adopted, unresolved, unliftable);
    }

}
