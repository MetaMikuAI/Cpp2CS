using System.Collections.Immutable;
using System.Diagnostics;
using System.Globalization;
using System.Text.Json;
using System.Text.RegularExpressions;
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
internal static class NamingCorpusChecks
{
    public const string Command = "naming-corpus";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_CORPUS"); var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(root) || string.IsNullOrEmpty(truth)) { Console.WriteLine("跳过命名语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var a = new Assertions(); var watch = Stopwatch.StartNew();
        var binary = Path.Combine(root,"artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.so");
        var image = ElfImage.Load(binary); var spec = InputCorpusChecks.Spec("arm64-v8a");
        var (model,registration) = ModelBuilder.Load(image,Path.Combine(root,"artifacts/il2cppOutput/data/Metadata/global-metadata.dat"),spec);
        var (map,problems) = RegistrationReader.Read(image,model,spec,registration.CodeRegistration,registration.MetadataRegistration);
        a.True(problems.Count==0,"代码地图完整");
        // 与管线相同的配置：运行时函数按符号定位，符号来自同一次构建的未去符号文件。
        var facts = new GlobalFacts(image,model,map,spec,"arm64") { Symbols = RecoverySession.CompanionSymbols(image, ElfImage.Load(Path.Combine(root,"artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.dbg.so"))) };
        var binder = new MethodBinder(new(new FieldLayouts(spec,image.PointerWidth,image.PointerWidth)),new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion,spec.Layout.Triple,spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder,new NamingCodeMap(map),new RuntimeFunctionMap(facts.RuntimeFunctions),catalog);
        var survey = new NamingSurvey(calls,new MetadataSlotDecoder(facts),image);
        using var cases = InputCorpusChecks.Json(truth,"cases.json");
        var selected = cases.RootElement.EnumerateArray().SelectMany(item=>item.GetProperty("mapping").GetProperty("targets").GetProperty("arm64-v8a").EnumerateArray()
            .Select(target=>(Address:InputCorpusChecks.Hex(target.GetProperty("address"))-image.PreferredBase,Name:item.GetProperty("case").GetProperty("method").GetString()!))).ToDictionary(x=>x.Address,x=>x.Name);
        var saved = new Dictionary<ulong,NativeFunction>(); var failures = new Dictionary<string,int>();
        var managed = map.Entries.Where(e=>e.Method is not null).Select(e=>e.Address).ToHashSet();
        int unresolvedSlots=0;
        var counts = new Dictionary<CallKind,int>(); var unknown = new Dictionary<string,int>();
        var isa = new Arm64InstructionSet(image); var flow = NoReturnCorpusChecks.Analyze(image);
        var lifting = Stopwatch.StartNew(); int good=0, bad=0, managedGood=0;
        foreach (var range in image.Functions)
        {
            // 只普查托管方法：槽位的凭据来自托管方法里的元数据初始化调用；全映像普查不在主链路上。
            if (!managed.Contains(range.Start)) { survey.Incomplete(); continue; }
            var lifted = FunctionLifter.Lift(isa,Arm64Registers.Convention,flow,range,range.Start);
            if (lifted.Function is not { } function)
            {
                survey.Incomplete(); bad++; var code=lifted.Failure!.Reason.Code; failures[code]=failures.GetValueOrDefault(code)+1;
                if(selected.TryGetValue(range.Start,out var label)) Console.WriteLine($"用例 {label}：提升失败 {code}");
                continue;
            }
            good++; survey.Observe(function);
            if (selected.ContainsKey(range.Start)) saved[range.Start]=function;
            if (managed.Contains(range.Start))
            {
                managedGood++; var state = new StateQueries(image: image); var c = state.CreateContext(function);
                foreach(var call in function.Blocks.SelectMany(b=>b.Statements).OfType<Call>())
                {
                    var named=c.Get(calls,call.Identity).Value; counts[named.Kind]=counts.GetValueOrDefault(named.Kind)+1;
                    if (named.Operation?.Name=="InitializeMetadata" && named.Inputs?.GetValueOrDefault("slot")?.Source is TermSource source)
                    {
                        var value=c.Get(state.Resolve,source.Term);
                        if(value.IsSuccess && value.Value.Identity is MemoryAtom { Location.Region:Region.Image } memory && memory.Location.Offset is { } offset && offset>=0 && offset<=ulong.MaxValue)
                        {
                            unresolvedSlots++;
                            if(unresolvedSlots<=3) Console.WriteLine($"槽位输入残留读取 调用=0x{call.Trace?.NativeAddress:x} 读取位置=0x{(ulong)offset:x} 位宽={value.Value.Width} 映像指针={image.ReadPointer((ulong)offset)} 可写={image.Query((ulong)offset).Writable}");
                        }
                    }
                    if(named.Kind==CallKind.Unknown)
                    {
                        string target=call.Target switch { ImageFunction im=>$"0x{im.EntryOffset:x}",ImportedTarget im=>im.Symbol.Name,_=>"间接" };
                        unknown[target]=unknown.GetValueOrDefault(target)+1;
                    }
                }
            }
            if((good+bad)%2000==0) Console.WriteLine($"命名普查进度 {good+bad}/{image.Functions.Length}");
        }
        var names = survey.Finish(); lifting.Stop();
        Console.WriteLine($"全映像提升与普查：成功={good} 失败={bad} 托管成功={managedGood}/{managed.Count} 秒={lifting.Elapsed.TotalSeconds:F3}");
        foreach(var item in failures.OrderByDescending(x=>x.Value)) Console.WriteLine($"普查缺口 {item.Key}={item.Value}");
        foreach(var item in counts.OrderBy(x=>x.Key)) Console.WriteLine($"调用 {item.Key}={item.Value}");
        foreach(var item in unknown.OrderByDescending(x=>x.Value).Take(20)) Console.WriteLine($"未知目标 {item.Key}={item.Value}");
        Console.WriteLine($"元数据初始化实参仍是映像读取={unresolvedSlots}");
        Console.WriteLine($"槽位={names.Slots.Count} 解码失败={names.Slots.Count(p=>!p.Value.IsSuccess)} 标志={names.Flags.Count(p=>p.Value.IsFlag)} 凭据不成立={names.Flags.Count(p=>!p.Value.IsFlag)} 普查完整={names.Complete}");
        foreach(var group in names.Flags.Values.SelectMany(f=>f.Reasons.Select(r=>r.Code).Distinct()).GroupBy(x=>x).OrderByDescending(g=>g.Count())) Console.WriteLine($"标志拒绝 {group.Key}={group.Count()}");
        var missing = new Dictionary<string,int>();
        foreach(var item in saved.OrderBy(x=>x.Key))
        {
            Console.WriteLine($"用例 {selected[item.Key]} @0x{item.Key:x}");
            var state = new StateQueries(image: image); var c=state.CreateContext(item.Value);
            var entry=map.ByAddress[item.Key].FirstOrDefault(e=>e.Kind==EntryKind.Method);
            var signature=entry is null ? null : binder.Entry(BindingCorpusChecks.Project(entry)).Value;
            var query=new ValueNamingQuery(state,calls,names,spec,binder,signature); c=query.CreateContext(item.Value);
            foreach(var b in item.Value.Blocks)
            foreach(var s in b.Statements)
            {
                if(s is Call call)
                {
                    var named=c.Get(calls,call.Identity).Value;
                    Console.WriteLine($"  调用 0x{s.Trace?.NativeAddress:x} {named.Kind} {named.Function?.Name ?? string.Join(" | ",named.Candidates?.Candidates.Select(x=>x.Entry.Method?.ToString()) ?? [])} {named.Why?.Code}");
                }
                if(s is MemoryRead read)
                {
                    var address=c.Get(state.Resolve,read.Address);
                    var location=address.IsSuccess ? c.Get(state.Locations,new(address.Value,read.Width)) : default;
                    if(location.IsSuccess && location.Value.Region==Region.Frame) continue;
                    var outcome=c.Get(query,read.Result); var named=outcome.IsSuccess ? outcome.Value : new NamedValue(ValueKind.Unnamed,null,Why:outcome.Why);
                    Console.WriteLine($"  读取 0x{s.Trace?.NativeAddress:x} {read.Width} {named.Kind} {named.Name} {named.Why?.Code}");
                    if(named.Kind==ValueKind.Unnamed) { var code=named.Why?.Code ?? "unknown"; missing[code]=missing.GetValueOrDefault(code)+1; }
                }
            }
        }
        foreach(var item in missing.OrderByDescending(x=>x.Value).Take(5)) Console.WriteLine($"未命名前五 {item.Key}={item.Value}");
        VerifySlots(root,names,model,a);
        Console.WriteLine($"用例清单={saved.Count}/{selected.Count} 总秒={watch.Elapsed.TotalSeconds:F3}");
        a.True(saved.Count==selected.Count,"全部用例有逐句清单");
        return a.Finish("命名定向检查");
    }
    private static void VerifySlots(string root,NamingFacts facts,ProgramModel model,Assertions checks)
    {
        var source=File.ReadAllText(Path.Combine(root,"artifacts/il2cppOutput/cpp/Il2CppMetadataUsage.c"));
        var encoded=Regex.Matches(source,@"\b(\w+)\s*=\s*\([^;]+\)\s*(\d+)\s*;").ToDictionary(m=>m.Groups[1].Value,m=>uint.Parse(m.Groups[2].Value,CultureInfo.InvariantCulture));
        // 测试只读工具提取全局符号；符号不进入产品的槽位发现。
        var start=new ProcessStartInfo("readelf") { RedirectStandardOutput=true,UseShellExecute=false };
        start.ArgumentList.Add("--wide"); start.ArgumentList.Add("--symbols"); start.ArgumentList.Add(Path.Combine(root,"artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.sym.so"));
        using var process=Process.Start(start)!; var output=process.StandardOutput.ReadToEnd(); process.WaitForExit();
        checks.True(process.ExitCode==0,"读取匹配构建的符号表");
        var globals=new Dictionary<ulong,List<string>>();
        foreach(var line in output.Split('\n'))
        {
            var parts=line.Split((char[]?)null,StringSplitOptions.RemoveEmptyEntries);
            if(parts.Length<8 || parts[3]!="OBJECT" || !encoded.ContainsKey(parts[7])) continue;
            var address=ulong.Parse(parts[1],NumberStyles.HexNumber,CultureInfo.InvariantCulture);
            if(!globals.TryGetValue(address,out var names)) globals[address]=names=[]; names.Add(parts[7]);
        }
        int compared=0,mismatch=0,absent=0;
        foreach(var (address,result) in facts.Slots.Where(p=>p.Value.IsSuccess))
        {
            if(!globals.TryGetValue(address,out var symbols)) { absent++; continue; }
            foreach(var symbol in symbols.Distinct())
            {
                var raw=encoded[symbol]; var usage=MetadataTokens.Decode(model,raw>>29,(raw&0x1fffffff)>>1);
                MetadataEntity? expected=usage?.Kind switch
                {
                    UsageKind.TypeInfo=>new ClassEntity((TypeRef)usage.Value), UsageKind.Il2CppType=>new TypeEntity((TypeRef)usage.Value),
                    UsageKind.MethodDef or UsageKind.MethodRef=>new MethodEntity((MethodRef)usage.Value), UsageKind.FieldInfo=>new FieldEntity((FieldRef)usage.Value),
                    UsageKind.StringLiteral=>new StringEntity((string)usage.Value),_=>null
                };
                compared++; if(expected!=result.Value) mismatch++;
            }
        }
        Console.WriteLine($"槽位符号实体核对={compared} 不一致={mismatch} 缺符号声明={absent}");
        checks.True(compared>0 && mismatch==0 && absent==0,"槽位与符号所指生成声明实体一致");
    }
}
