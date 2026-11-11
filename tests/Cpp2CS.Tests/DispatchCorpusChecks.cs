using Cpp2CS.Recovery.Dispatch;
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
internal static class DispatchCorpusChecks
{
    public const string Command = "dispatch-corpus";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_CORPUS"); var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(root) || string.IsNullOrEmpty(truth)) { Console.WriteLine("跳过分派语料：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
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
            if(saved.Count%2000==0) Console.WriteLine($"分派普查进度 {saved.Count}");
        }
        var names = survey.Finish();
        var counts=new Dictionary<string,int>(); var shapes=new Dictionary<TargetShape,(int Count,string Example)>(); int casesFound=0;
        int liftedCount=saved.Count; int ilSamples=0;
        var modules=new Dictionary<string,Mono.Cecil.ModuleDefinition>();
        using var truthMethods=InputCorpusChecks.Json(truth,"methods.json");
        var ilBodies=truthMethods.RootElement.EnumerateArray().ToDictionary(x=>x.GetProperty("id").GetString()!,x=>x);

        foreach(var address in saved.Keys.ToArray())
        {
            var function=saved[address]; saved.Remove(address);
            var state=new StateQueries(image:image);
            var entry=map.ByAddress[address].FirstOrDefault(e=>e.Kind==EntryKind.Method);
            var signature=entry is null ? null : binder.Entry(BindingCorpusChecks.Project(entry)).Value;
            var naming=new ValueNamingQuery(state,calls,names,spec,binder,signature);
            var locations=new ManagedLocationQuery(state,naming,layouts,spec);
            var query=new DispatchQuery(state,calls,naming,locations,binder,spec);
            var c=locations.CreateContext(function); bool chosen=selected.TryGetValue(address,out var label);
            var local=new Dictionary<string,int>();
            var resolvedCalls=new List<(Call Call,DispatchResult Result)>();
            if(chosen) casesFound++;
            foreach(var call in function.Blocks.SelectMany(b=>b.Statements).OfType<Call>().Where(x=>x.Target is ComputedTarget))
            {
                var outcome=c.Get(query,call.Identity);
                var result=outcome.IsSuccess ? outcome.Value : new DispatchResult(DispatchKind.Unresolved,TargetShape.Other,Why:outcome.Why);
                var kind=result.Kind==DispatchKind.Unresolved ? result.Why?.Code ?? "unknown" : result.Kind.ToString();
                counts[kind]=counts.GetValueOrDefault(kind)+1; local[kind]=local.GetValueOrDefault(kind)+1;
                var text=$"caller={entry?.Method} token=0x{entry?.Method?.Method.Token:x} native=0x{call.Trace?.NativeAddress:x} {kind} shape={result.Shape} type={result.StaticType} slot={result.Slot} method={result.Method} targetToken=0x{result.Method?.Method.Token:x}";
                if(result.Kind==DispatchKind.Virtual) resolvedCalls.Add((call,result));
                if(result.Kind!=DispatchKind.Unresolved || chosen) Console.WriteLine(text);
                if(result.Kind==DispatchKind.Unresolved)
                { var prior=shapes.GetValueOrDefault(result.Shape); shapes[result.Shape]=(prior.Count+1,prior.Example ?? text); }
            }
            // 唯一原生虚调用与唯一 IL callvirt 建立无歧义位置对应；不把同方法内任意同名调用算命中。
            if(ilSamples<20 && resolvedCalls.Count==1 && local.Values.Sum()==1 && entry?.Method is { } caller)
            {
                var id=$"{caller.Method.Owner.Assembly}:0x{caller.Method.Token:x8}";
                if(ilBodies.TryGetValue(id,out var truthMethod) && truthMethod.GetProperty("has_body").GetBoolean())
                {
                    var assembly=caller.Method.Owner.Assembly;
                    if(!modules.TryGetValue(assembly,out var module))
                        modules[assembly]=module=Mono.Cecil.ModuleDefinition.ReadModule(Path.Combine(root,truthMethod.GetProperty("assembly_path").GetString()!));
                    if(module.LookupToken((int)caller.Method.Token) is Mono.Cecil.MethodDefinition { HasBody:true } definition)
                    {
                        var virtuals=definition.Body.Instructions.Where(i=>i.OpCode==Mono.Cecil.Cil.OpCodes.Callvirt).ToArray();
                        var found=resolvedCalls[0];
                        if(virtuals.Length==1 && virtuals[0].Operand is Mono.Cecil.MethodReference reference &&
                            reference.MetadataToken.ToUInt32()==found.Result.Method!.Method.Token && reference.DeclaringType.FullName.Replace('/', '.')==found.Result.Method.Method.Owner.FullName)
                        {
                            // 真值中的 IL 字节同时核对 opcode 与操作数，程序集读取只用于解析其身份。
                            var bytes=Convert.FromHexString(truthMethod.GetProperty("il_hex").GetString()!);
                            var offset=virtuals[0].Offset;
                            a.True(bytes[offset]==0x6f && BitConverter.ToUInt32(bytes,offset+1)==reference.MetadataToken.ToUInt32(),"真实 IL callvirt 位置与方法 token");
                            ilSamples++;
                            Console.WriteLine($"IL抽查 {ilSamples}: {id} {caller} native=0x{found.Call.Trace?.NativeAddress:x} IL_{offset:x4} callvirt {reference.FullName} slot={found.Result.Slot}");
                        }
                    }
                }
            }
            if(chosen) Console.WriteLine($"用例 {label}: {string.Join(", ",local.OrderBy(x=>x.Key).Select(x=>$"{x.Key}={x.Value}"))}");
        }
        foreach(var pair in counts.OrderBy(p=>p.Key)) Console.WriteLine($"分派 {pair.Key}={pair.Value}");
        foreach(var pair in shapes.OrderByDescending(p=>p.Value.Count)) Console.WriteLine($"形状 {pair.Key}={pair.Value.Count} 例：{pair.Value.Example}");
        Console.WriteLine($"托管提升={liftedCount} 失败={bad} 用例={casesFound}/{selected.Count} 总秒={watch.Elapsed.TotalSeconds:F3}");
        foreach(var module in modules.Values) module.Dispose();
        a.True(ilSamples==20,"完成二十个唯一调用位置的真实 IL 抽查");
        a.True(casesFound==selected.Count,"全部用例有调用清单");
        return a.Finish("分派定向检查");
    }
}
