using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Checks;
using Cpp2CS.Kernel.Flow;
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
internal static class CheckCorpusChecks
{
    public const string Command = "checks-corpus";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_CORPUS"); var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(root) || string.IsNullOrEmpty(truth)) { Console.WriteLine("跳过条件抛出语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
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
            if(saved.Count%2000==0) Console.WriteLine($"检查普查进度 {saved.Count}");
        }
        var names = survey.Finish();
        var counts=RuntimeOperations.All.Values.Where(op=>op.FixedThrownException is not null).Select(op=>op.FixedThrownException!).Distinct().ToDictionary(type=>type,_=>(Absorbed:0,Explicit:0)); var missing=new Dictionary<string,(int Count,string Example)>(); int casesFound=0, failures=0;
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
            var checks=new CheckQueries(state,calls,query);
            var c=query.CreateContext(item.Value); bool chosen=selected.TryGetValue(item.Key,out var label);
            int found=0;
            if(chosen) { casesFound++; Console.WriteLine($"用例 {label} @0x{item.Key:x}"); }
            bool hasFixedThrow=item.Value.Blocks.SelectMany(b=>b.Statements).OfType<Call>()
                .Any(call=>c.Get(calls,call.Identity) is { IsSuccess:true, Value.Operation.FixedThrownException:not null });
            foreach(var block in hasFixedThrow ? item.Value.Blocks : [])
            {
                if(block.End is not Branch branch) continue;
                foreach(var target in new[]{branch.True,branch.False}.Distinct())
                {
                    var outcome=c.Get(checks.Checks,new FlowEdge(block.Identity,target));
                    if(!outcome.IsSuccess) { failures++; if(chosen) Console.WriteLine($"  查询失败 {outcome.Why}"); continue; }
                    if(outcome.Value is not { } check) continue;
                    found++;
                    var prior=counts.GetValueOrDefault(check.Exception);
                    counts[check.Exception]=(prior.Absorbed+(check.CanAbsorb ? 1 : 0),prior.Explicit+(check.CanAbsorb ? 0 : 1));
                    var text=$"块={item.Value.Blocks.IndexOf(block)} {check.Exception} absorb={check.CanAbsorb} reason={check.ExplicitReason?.Code} value={TermText(check.Subject.Value)} array={TermText(check.Subject.Array)} index={TermText(check.Subject.Index)} condition={TermText(check.FailureCondition)}";
                    if(chosen) Console.WriteLine("  "+text);
                    if(!check.CanAbsorb)
                    {
                        var code=check.Exception+"/"+check.ExplicitReason!.Code; var old=missing.GetValueOrDefault(code);
                        missing[code]=(old.Count+1,old.Example ?? $"方法=0x{item.Key:x} {text}");
                    }
                }
            }
            if(chosen) Console.WriteLine($"  检查数={found}");
        }
        foreach(var pair in counts.OrderBy(p=>p.Key)) Console.WriteLine($"检查 {pair.Key} 合计={pair.Value.Absorbed+pair.Value.Explicit} 吸收={pair.Value.Absorbed} 显式={pair.Value.Explicit}");
        foreach(var pair in missing.OrderByDescending(p=>p.Value.Count).Take(10)) Console.WriteLine($"显式原因 {pair.Key}={pair.Value.Count}");
        foreach(var pair in missing.OrderByDescending(p=>p.Value.Count).Take(10)) Console.WriteLine($"例 {pair.Key}: {pair.Value.Example}");
        Console.WriteLine($"托管提升={liftedCount} 失败={bad} 用例={casesFound}/{selected.Count} 查询失败={failures} 总秒={watch.Elapsed.TotalSeconds:F3}");
        a.True(casesFound==selected.Count,"全部用例有检查清单");
        a.True(failures==0,"查询无失败");
        return a.Finish("条件抛出定向检查");
    }
    private static string TermText(Term? term, int depth=0) => term is null ? "-" : depth>6 ? "…" :
        term.ConstantValue is { } n ? n.ToString() : term.Identity is { } atom ? atom.StableText :
        $"{term.Operator?.Name ?? term.Kind.ToString()}[{term.Width}:{term.SliceLow}]({string.Join(",",term.Operands.Select(t=>TermText(t,depth+1)))})";
}
