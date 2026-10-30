#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Cpp2CS.Facts;

namespace Cpp2CS.Input
{
    /// <summary>从磁盘上的 libil2cpp.so 与 global-metadata.dat 建立 <see cref="ProgramFacts"/>，并运行全部不变式检查。</summary>
    public static class FactsBuilder
    {
        public static ProgramFacts Build(string binaryPath, string metadataPath, Action<string>? log = null, bool inferUnregistered = true, string? cacheDirectory = null, Cpp2CS.Options.RecoveryOptions? options = null)
        {
            var timings = new Dictionary<string, double>();
            var clock = Stopwatch.StartNew();
            T Step<T>(string name, Func<T> action)
            {
                var start = clock.Elapsed.TotalSeconds;
                var result = action();
                timings[name] = Math.Round(clock.Elapsed.TotalSeconds - start, 3);
                log?.Invoke($"{name}: {timings[name]:F1}s");
                return result;
            }

            var (model, builder) = Step("model", () => ModelBuilder.Load(binaryPath, metadataPath));
            var map = Step("codemap", () => CodeMap.Build(model.Image));
            var scan = Step("scan", () => CodeScan.Run(map));
            var (registrations, problems) = Step("registrations", () => RegistrationReader.Read(model, builder.CodeRegistration, builder.MetadataRegistration));

            var checks = new FactChecks();
            checks.Add("registrations.read", "Error", registrations.Entries.Count, (IReadOnlyCollection<string>)problems,
                $"CodeRegistration 0x{builder.CodeRegistration:x}，MetadataRegistration 0x{builder.MetadataRegistration:x}，元数据版本 {model.MetadataVersion}");
            Step("checks.code", () => { CodeChecks.Run(checks, map, scan, registrations); return 0; });
            var usages = Step("usages", () => UsageSlots.Build(model, map, scan));
            usages.Check(checks, registrations);
            var helpers = Step("helpers", () => IdentifyHelpers(map, scan, registrations, usages, checks));
            Step("checks.exceptions", () => { ExceptionFacts.Check(checks, map, scan, helpers); return 0; });
            Step("checks.runtime-layout", () => { LayoutChecks.Run(checks, map, scan, helpers); return 0; });
            var layouts = new FieldLayouts(model);
            Step("layouts", () => { layouts.Check(checks); return 0; });
            var generic = registrations.Entries.Where(e => e.Kind is EntryKind.GenericMethod or EntryKind.GenericAdjustorThunk && e.Method is not null).ToArray();
            var shared = generic.Where(e => e.Method!.TypeArguments.Concat(e.Method.MethodArguments).Any(FieldLayouts.IsFullyShared)).ToArray();
            checks.Info("generic.fully-shared", generic.Length,
                $"泛型方法实例代码 {generic.Length} 个，其中实参含完全共享占位类型（偏移、大小经 RGCTX 在运行时取得）的 {shared.Length} 个；" +
                $"共享实例所属 Assembly-CSharp 类型 {shared.Count(e => e.Method!.Method.Owner.Assembly == "Assembly-CSharp.dll")} 个方法");
            var basis = new BaseFacts
            {
                Model = model,
                Code = map,
                Scan = scan,
                Registrations = registrations,
                Usages = usages,
                Helpers = helpers,
                Layouts = layouts,
                Checks = checks,
                Timings = timings,
                Options = options ?? new(),
            };
            var registered = new ProgramFacts(basis, new());
            cacheDirectory ??= basis.Options.FactCacheDirectory ?? Path.Combine(".cpp2cs", "unregistered");
            var inferred = inferUnregistered ? Step("unregistered", () => UnregisteredFactsCache.GetOrBuild(registered, metadataPath, cacheDirectory, log)) : UnregisteredMethods.Empty;
            timings["total"] = Math.Round(clock.Elapsed.TotalSeconds, 3);
            return new ProgramFacts(basis, new() { Unregistered = inferred });
        }

        /// <summary>托管代码调用的、没有托管所有者的目标：运行时 helper、PLT 导入，以及 il2cpp 节中生成的无元数据函数。</summary>
        private static RuntimeHelpers IdentifyHelpers(CodeMap map, CodeScan scan, Registrations registrations, UsageSlots usages, FactChecks checks)
        {
            var targets = new Dictionary<ulong, int>();
            for (var i = 0; i < map.Functions.Count; i++)
            {
                if (map.Functions[i].Region != CodeRegion.Managed) continue;
                foreach (var r in scan.Of(i))
                    if (r.Kind is RefKind.Call or RefKind.TailCall && !registrations.ByAddress.ContainsKey(r.Target))
                        targets[r.Target] = targets.GetValueOrDefault(r.Target) + 1;
            }
            var helpers = RuntimeHelpers.Identify(map, scan, targets, usages.SlotAddressBeforeCall);
            var all = helpers.Helpers.Values.ToArray();
            string Census(IEnumerable<RuntimeHelper> list) => string.Join("，", list.GroupBy(h => h.Kind).OrderByDescending(g => g.Sum(h => h.CallSites))
                .Select(g => $"{g.Key}={g.Count()}个/{g.Sum(h => h.CallSites)}次"));
            var runtime = all.Where(h => map.RegionOf(h.Address) != CodeRegion.Managed).ToArray();
            var generated = all.Where(h => map.RegionOf(h.Address) == CodeRegion.Managed).ToArray();
            var unknown = runtime.Where(h => h.Kind == HelperKind.Unknown).OrderByDescending(h => h.CallSites).ToArray();
            long sites = runtime.Sum(h => h.CallSites);
            checks.Add("helpers.runtime", "Warning", sites,
                unknown.Select(h => $"0x{h.Address:x} {h.CallSites} 次：{h.Evidence}").ToArray(),
                $"托管代码对运行时/PLT 目标的调用点 {sites}，未识别 {unknown.Sum(h => h.CallSites)}（{unknown.Length} 个目标）；" + Census(runtime), samples: 25);
            checks.Info("helpers.generated", generated.Sum(h => h.CallSites),
                $"il2cpp 节中没有元数据所有者、被托管代码调用的生成函数 {generated.Length} 个；" + Census(generated));
            return helpers;
        }
    }
}
