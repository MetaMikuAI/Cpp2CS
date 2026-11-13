using System.Collections.Immutable;
using System.Diagnostics;
using System.Text.Json;
using System.Globalization;
using Cpp2CS.Input;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Targets.Elf;
using Cpp2CS.Targets.Frontend;

namespace Cpp2CS.Tests;

internal static class InitializationFlagCorpusChecks
{
    public const string Command = "init-flags-corpus";
    private static readonly System.Text.RegularExpressions.Regex SpecialMember = new(@"^[CD][012]E", System.Text.RegularExpressions.RegexOptions.CultureInvariant);
    internal static bool NoIndirectResult(string symbol)
    {
        if (!symbol.StartsWith("_ZN", StringComparison.Ordinal)) return false;
        int cursor = 3;
        while (cursor < symbol.Length && char.IsAsciiDigit(symbol[cursor]))
        {
            int length = 0;
            while (cursor < symbol.Length && char.IsAsciiDigit(symbol[cursor])) { length = checked(length * 10 + symbol[cursor] - '0'); cursor++; }
            if (length == 0 || length > symbol.Length - cursor) return false;
            cursor += length;
        }
        return cursor < symbol.Length && SpecialMember.IsMatch(symbol[cursor..]);
    }
    // 返回协议来自运行时声明；只投影间接结果槽，不猜测其他实参。
    private static readonly HashSet<string> ScalarReturns =
    [
        "_ZdlPv", // C++ operator delete(void*)。
        "_ZN6il2cpp2os13LibraryLoader21SetFindPluginCallbackEPFPKcS3_E", // os/LibraryLoader.h：void。
        "_ZN6il2cpp6icalls8mscorlib6System10ReflectionL30SetCustomAttributeTypeArgumentEPK10MethodInfoPvPKNS_8metadata23CustomAttributeArgumentE", // icalls/mscorlib/System.Reflection/CustomAttributeData.cpp：void。
        "_ZN6il2cpp2vm7Runtime6InvokeEPK10MethodInfoPvPS5_PP15Il2CppException", // vm/Runtime.h：Il2CppObject*。
        "_ZN6il2cpp8metadataL24RecursiveGenericDepthForEPK17Il2CppGenericInst", // metadata/GenericMetadata.cpp：int。
    ];
    private static HashSet<ulong> CallbackSlots(string corpus, ulong preferredBase)
    {
        // 回调声明：os/c-api/Allocator.h 的 allocate_func；os/Thread.h 的 ThreadCleanupFunc。
        var names = new HashSet<string> { "_ZL15s_AllocatorFunc", "_ZN6il2cpp2osL13s_CleanupFuncE" };
        var start = new ProcessStartInfo("readelf") { RedirectStandardOutput = true, UseShellExecute = false };
        start.ArgumentList.Add("--wide"); start.ArgumentList.Add("--symbols");
        start.ArgumentList.Add(Path.Combine(corpus, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.dbg.so"));
        using var process = Process.Start(start)!; var text = process.StandardOutput.ReadToEnd(); process.WaitForExit();
        if (process.ExitCode != 0) throw new InvalidDataException("读取匹配构建的全局符号失败。");
        var result = new HashSet<ulong>();
        foreach (var line in text.Split('\n'))
        {
            var parts = line.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
            if (parts.Length >= 8 && parts[3] == "OBJECT" && names.Contains(parts[7]))
                result.Add(ulong.Parse(parts[1], NumberStyles.HexNumber, CultureInfo.InvariantCulture) - preferredBase);
        }
        return result;
    }
    // Itanium C++ 构造与析构不返回聚合体；匹配符号仅给核对补足这一条 ABI 凭据。
    internal static NativeFunction ProjectNativeReturnProtocol(NativeFunction function, IReadOnlySet<ulong> known, StateQueries? state = null, IReadOnlySet<ulong>? callbacks = null)
    {
        var context = state?.CreateContext(function);
        bool NoBuffer(Call call)
        {
            if (call.Target is ImageFunction direct) return known.Contains(direct.EntryOffset);
            if (call.Target is ImportedTarget imported) return imported.Symbol.Name == "pthread_key_delete";
            if (call.Target is not ComputedTarget target || state is null || context is null || callbacks is null) return false;
            var read = context.Get(new ReadLocationQuery(state), target.Value);
            return read.IsSuccess && read.Value is { Region: Region.Image, Offset: { } offset } && offset >= 0 && offset <= ulong.MaxValue && callbacks.Contains((ulong)offset);
        }
        if (!function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(call => NoBuffer(call)
            && call.Arguments.Any(a => a.Slot.Kind == SlotKind.IndirectResult))) return function;
        var edit = new SnapshotRewrite(function); bool changed = false;
        foreach (var block in function.Blocks)
        {
            var statements = block.Statements.Select(statement =>
            {
                if (statement is not Call call || !NoBuffer(call)) return statement;
                var inputs = call.Arguments.Where(a => a.Slot.Kind != SlotKind.IndirectResult).ToImmutableArray();
                if (inputs.Length == call.Arguments.Length) return statement;
                changed = true; return call with { Arguments = inputs };
            }).ToImmutableArray();
            edit.Blocks[block.Identity] = block with { Statements = statements };
        }
        return changed ? edit.Apply() : function;
    }
    private sealed record Access(ulong Function, ulong? Position, ulong Address, int Width, bool Escape, FlagEvidence? Evidence);
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        if (string.IsNullOrEmpty(corpus)) { Console.WriteLine("跳过初始化标志核对：未设置 CPP2CS_CORPUS。"); return 0; }
        var checks = new Assertions(); var timer = Stopwatch.StartNew();
        var image = ElfImage.Load(Path.Combine(corpus, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.so"));
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var (model, registration) = ModelBuilder.Load(image, Path.Combine(corpus, "artifacts/il2cppOutput/data/Metadata/global-metadata.dat"), spec);
        var (map, problems) = RegistrationReader.Read(image, model, spec, registration.CodeRegistration, registration.MetadataRegistration);
        checks.True(problems.Count == 0, "代码地图完整");
        var facts = new GlobalFacts(image, model, map, spec, "arm64") { Symbols = RecoverySession.CompanionSymbols(image,
            ElfImage.Load(Path.Combine(corpus, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.dbg.so"))) };
        var binder = new MethodBinder(new(new FieldLayouts(spec, image.PointerWidth, image.PointerWidth)), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var code = new NamingCodeMap(map);
        var calls = new CallNamingQuery(binder, code, new RuntimeFunctionMap(facts.RuntimeFunctions), catalog);
        var instructionSet = new Arm64InstructionSet(image); var noReturn = NoReturnCorpusChecks.Analyze(image);
        var noIndirectResult = facts.Symbols.Where(s => NoIndirectResult(s.Name) || ScalarReturns.Contains(s.Name)).Select(s => s.Offset).ToHashSet();
        var callbackSlots = CallbackSlots(corpus, image.PreferredBase);
        var protocolState = new StateQueries(image: image);
        var accepted = new SortedSet<ulong>(); var accesses = new List<Access>(); var failures = new List<object>();
        int good = 0;
        foreach (var range in image.Functions)
        {
            var lifted = FunctionLifter.Lift(instructionSet, Arm64Registers.Convention, noReturn, range, range.Start);
            if (lifted.Function is not { } function)
            { failures.Add(new { Function = range.Start, Reason = lifted.Failure!.Reason }); continue; }
            function = ProjectNativeReturnProtocol(function, noIndirectResult, protocolState, callbackSlots);
            good++;
            if (good % 5000 == 0) Console.WriteLine($"初始化标志核对进度：已提升 {good}/{image.Functions.Length}");
            var candidates = code.At(range.Start);
            var signatures = candidates.Select(candidate => binder.Entry(candidate).Value).Where(s => s is not null).ToArray();
            var entry = signatures.FirstOrDefault();
            if (entry is null && calls.RuntimeIdentity(new ImageFunction(range.Start))?.Signature is { } signature)
                entry = binder.Classify(signature).Value;
            var survey = new NamingSurvey(calls, new MetadataSlotDecoder(facts), image, binder, spec, entry);
            survey.Observe(function); var local = survey.Finish();
            accepted.UnionWith(local.Flags.Where(p => p.Value.IsFlag).Select(p => p.Key));
            var state = new StateQueries(image: image); var context = state.CreateContext(function);
            ulong? Address(Term term, int width)
            {
                if (term.Width != function.AddressWidth || term.ContainsUndefined) return null;
                var resolved = context.Get(state.Resolve, term);
                var location = resolved.IsSuccess ? context.Get(state.Locations, new(resolved.Value, width)) : default;
                return location.IsSuccess && location.Value is { Region: Region.Image, Offset: { } offset } && offset >= 0 && offset <= ulong.MaxValue ? (ulong)offset : null;
            }
            var uses = new SemanticUses(context, calls, state, binder, entry);
            foreach (var statement in function.Blocks.SelectMany(b => b.Statements))
            {
                var request = statement switch
                { MemoryRead read => new AddressRequest(read.Address, read.Width), MemoryWrite write => new AddressRequest(write.Address, write.Width), _ => default };
                if (request.Address is null) continue;
                var addresses = Address(request.Address, request.Width) is { } actual ? new HashSet<ulong> { actual } : uses.ImageAddresses(request.Address, context, state);
                foreach (var address in addresses)
                    accesses.Add(new(range.Start, statement.Trace?.NativeAddress, address, request.Width, false, local.Flags.GetValueOrDefault(address)));
            }
            var escaped = new HashSet<ulong>();
            foreach (var use in uses.Roots.Where(u => !u.Address)) escaped.UnionWith(uses.ImageAddresses(use.Value, context, state));
            foreach (var address in escaped) accesses.Add(new(range.Start, null, address, 8, true, local.Flags.GetValueOrDefault(address)));
        }
        var relevant = new List<(ulong Flag, Access Access)>();
        foreach (var access in accesses)
        {
            var bytes = (ulong)((access.Width + 7L) / 8);
            ulong end = access.Address > ulong.MaxValue - bytes + 1 ? ulong.MaxValue : access.Address + bytes - 1;
            foreach (var flag in accepted.GetViewBetween(access.Address, end)) relevant.Add((flag, access));
        }
        var invalid = relevant.Where(x => x.Access.Escape || x.Access.Width != 8 || x.Access.Address != x.Flag || x.Access.Evidence?.IsFlag != true).ToArray();
        var byFlag = relevant.GroupBy(x => x.Flag).ToDictionary(g => g.Key, g => g.Select(x => x.Access.Function).Distinct().Order().ToArray());
        var multiple = byFlag.Count(p => p.Value.Length > 1);
        var output = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", "init-flags-corpus.local.json");
        File.WriteAllText(output, JsonSerializer.Serialize(new
        {
            Functions = image.Functions.Length, Lifted = good, Unliftable = failures.Count, Addresses = accepted.Count, MultipleFunctions = multiple,
            InvalidAccesses = invalid.Length, Seconds = timer.Elapsed.TotalSeconds,
            Flags = accepted.Select(flag => new { Address = flag, Functions = byFlag.GetValueOrDefault(flag) ?? [] }),
            Violations = invalid.Select(x => new { x.Flag, x.Access }), UnliftableFunctions = failures,
        }, new JsonSerializerOptions { WriteIndented = true }));
        Console.WriteLine($"初始化标志全映像核对：地址={accepted.Count}，多函数地址={multiple}，不符合模板访问={invalid.Length}，提升={good}，不能提升={failures.Count}，用时={timer.Elapsed.TotalSeconds:F2}s");
        foreach (var (flag, access) in invalid)
            Console.WriteLine($"标志 0x{flag:x}：函数 0x{access.Function:x}，访问 0x{access.Position:x}，宽 {access.Width}，逃逸={access.Escape}：{string.Join("；", access.Evidence?.Reasons.Select(r => r.Message) ?? [])}");
        checks.True(accepted.Count > 0, "至少一个函数提供方法初始化标志的模板凭据");
        checks.True(invalid.Length == 0, "其他能提升函数里的全部访问也符合模板；不能提升函数仅列为检验边界");
        return checks.Finish("初始化标志全映像核对");
    }
}
