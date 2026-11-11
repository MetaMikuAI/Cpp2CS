using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Locations;
using System.Diagnostics;
using Cpp2CS.Input;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
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
internal static class LocationCorpusChecks
{
    public const string Command = "locations-corpus";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_CORPUS"); var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(root) || string.IsNullOrEmpty(truth)) { Console.WriteLine("跳过定位语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var a = new Assertions(); var watch = Stopwatch.StartNew();
        var binary = Path.Combine(root,"artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.so");
        var image = ElfImage.Load(binary); var spec = InputCorpusChecks.Spec("arm64-v8a");
        var (model,registration) = ModelBuilder.Load(image,Path.Combine(root,"artifacts/il2cppOutput/data/Metadata/global-metadata.dat"),spec);
        var (map,problems) = RegistrationReader.Read(image,model,spec,registration.CodeRegistration,registration.MetadataRegistration);
        a.True(problems.Count==0,"代码地图完整");
        // 与管线相同的配置：运行时函数按符号定位，符号来自同一次构建的未去符号文件。
        var facts = new GlobalFacts(image,model,map,spec,"arm64") { Symbols = RecoverySession.CompanionSymbols(image, ElfImage.Load(Path.Combine(root,"artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.dbg.so"))) };
        var layouts = new FieldLayouts(spec,image.PointerWidth,image.PointerWidth);
        var binder = new MethodBinder(new(layouts),new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion,spec.Layout.Triple,spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder,new NamingCodeMap(map),new RuntimeFunctionMap(facts.RuntimeFunctions),catalog);
        var survey = new NamingSurvey(calls,new MetadataSlotDecoder(facts),image);
        using var cases = InputCorpusChecks.Json(truth,"cases.json");
        var selected = cases.RootElement.EnumerateArray().SelectMany(item=>item.GetProperty("mapping").GetProperty("targets").GetProperty("arm64-v8a").EnumerateArray()
            .Select(target=>(Address:InputCorpusChecks.Hex(target.GetProperty("address"))-image.PreferredBase,Name:item.GetProperty("case").GetProperty("method").GetString()!))).ToDictionary(x=>x.Address,x=>x.Name);
        var saved = new Dictionary<ulong,NativeFunction>();
        var managed = map.Entries.Where(e=>e.Method is not null).Select(e=>e.Address).ToHashSet();
        var isa = new Arm64InstructionSet(image); var flow = NoReturnCorpusChecks.Analyze(image);
        int bad=0;
        foreach (var range in image.Functions)
        {
            if (!managed.Contains(range.Start)) { survey.Incomplete(); continue; }
            var lifted = FunctionLifter.Lift(isa,Arm64Registers.Convention,flow,range,range.Start);
            if (lifted.Function is not { } function) { survey.Incomplete(); bad++; continue; }
            survey.Observe(function); saved.Add(range.Start,function);
            if(saved.Count%2000==0) Console.WriteLine($"定位普查进度 {saved.Count}");
        }
        var names = survey.Finish();
        var counts=new Dictionary<ManagedLocationKind,int>(); var missing=new Dictionary<string,(int Count,string Example)>(); int casesFound=0;
        int liftedCount=saved.Count;
        foreach(var address in saved.Keys.ToArray())
        {
            var item=new KeyValuePair<ulong,NativeFunction>(address,saved[address]);
            saved.Remove(address);
            var state=new StateQueries(image:image);
            var entry=map.ByAddress[item.Key].FirstOrDefault(e=>e.Kind==EntryKind.Method);
            var signature=entry is null ? null : binder.Entry(BindingCorpusChecks.Project(entry)).Value;
            var naming=new ValueNamingQuery(state,calls,names,spec,binder,signature);
            var query=new ManagedLocationQuery(state,naming,layouts,spec);
            var c=query.CreateContext(item.Value); bool chosen=selected.TryGetValue(item.Key,out var label);
            if(chosen) { casesFound++; Console.WriteLine($"用例 {label} @0x{item.Key:x}"); }
            foreach(var statement in item.Value.Blocks.SelectMany(b=>b.Statements))
            {
                var request=statement switch { MemoryRead r=>new AddressRequest(r.Address,r.Width), MemoryWrite w=>new AddressRequest(w.Address,w.Width), _=>default };
                if(request.Address is null) continue;
                var resolved=c.Get(state.Resolve,request.Address);
                if(resolved.IsSuccess && c.Get(state.Locations,new(resolved.Value,request.Width)) is { IsSuccess:true,Value.Region:Region.Frame }) continue;
                var outcome=c.Get(query,request);
                var result=outcome.IsSuccess ? outcome.Value : new LocationResult(ManagedLocationKind.Unknown,[],outcome.Why);
                counts[result.Kind]=counts.GetValueOrDefault(result.Kind)+1;
                var text=$"0x{statement.Trace?.NativeAddress:x} {statement.GetType().Name} {request.Width} {result.Kind} " +
                    string.Join(" | ",result.Views.Select(v=>$"{string.Join(".",v.Path.Select(f=>f.Field.ToString()))} offset={v.Offset} index={TermText(v.Index)} type={v.Type}")) + $" {result.Why?.Code}";
                if(chosen) Console.WriteLine("  "+text);
                if(result.Kind==ManagedLocationKind.Unknown)
                { var code=result.Why?.Code ?? "unknown"; var prior=missing.GetValueOrDefault(code); missing[code]=(prior.Count+1,prior.Example ?? $"方法=0x{item.Key:x} {text}"); }
            }
        }
        foreach(var pair in counts.OrderBy(p=>p.Key)) Console.WriteLine($"定位 {pair.Key}={pair.Value}");
        foreach(var pair in missing.OrderByDescending(p=>p.Value.Count)) Console.WriteLine($"不能定位 {pair.Key}={pair.Value.Count}");
        foreach(var pair in missing.OrderByDescending(p=>p.Value.Count).Take(10)) Console.WriteLine($"例 {pair.Key}: {pair.Value.Example}");
        Console.WriteLine($"托管提升={liftedCount} 失败={bad} 用例={casesFound}/{selected.Count} 总秒={watch.Elapsed.TotalSeconds:F3}");
        a.True(casesFound==selected.Count,"全部用例有访问清单");
        return a.Finish("定位定向检查");
    }
    private static string TermText(Term? term, int depth=0) => term is null ? "-" : depth>6 ? "…" :
        term.ConstantValue is { } n ? n.ToString() : term.Identity is { } atom ? atom.StableText :
        $"{term.Operator?.Name ?? term.Kind.ToString()}[{term.Width}:{term.SliceLow}]({string.Join(",",term.Operands.Select(t=>TermText(t,depth+1)))})";
}
