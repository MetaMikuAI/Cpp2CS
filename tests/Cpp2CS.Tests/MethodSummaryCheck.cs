using System.Reflection;
using Cpp2CS.Calls;
using Cpp2CS.Model;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class MethodSummaryCheck
{
    [Command("method-summaries", "摘要依赖按使用方补齐，失败、入口、恢复方式与原生布局分别缓存", Gate = Gate.Unit)]
    public static int Run()
    {
        var owner = new TypeDef { Index = 0, Assembly = "Summary.Tests.dll", Namespace = "Tests", Name = "Worker",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        MethodRef Method(int index) => MethodRef.Open(new MethodDef { Index = index, Owner = owner, Name = "Run" + index,
            Token = 0, Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1 });
        var dependency = new MethodRequest(Method(0), 0x100);
        var missing = new MethodRequest(Method(1), 0x200);
        var recoveries = 0;
        var service = new MethodSummaryService(request =>
        {
            recoveries++;
            return request == missing ? new(request.Method, request.Entry, null, [new(request.Entry, "unsupported")])
                : new(request.Method, request.Entry, new(request.Method, [new(0, [new ManagedReturn(0, null)])]), []);
        });
        var runs = new Dictionary<int, int>();
        int Analyze(int item, IMethodSummaries catalog)
        {
            runs[item] = runs.GetValueOrDefault(item) + 1;
            if (item == 0) return 7;
            if (catalog.Find(dependency) is null) return 0;
            return item == 1 ? catalog.Find(missing) is { Body: null } ? -1 : 0 : 9;
        }
        var results = service.Complete([0, 1, 2], Analyze);
        var a = new Assertions();
        a.Equal(1, runs[0], "无依赖的方法只分析一次");
        a.Equal(3, runs[1], "逐轮发现的依赖只重放当前方法");
        a.Equal(2, runs[2], "已经完成的方法不随其他依赖重放");
        a.Equal(2, recoveries, "共同依赖只恢复一次");
        a.Equal(-1, results[1], "缺失的方法体作为明确失败结果保留");
        a.Equal(9, results[2], "独立完成结果保留");
        service.Complete([1], Analyze);
        a.Equal(2, recoveries, "失败摘要也缓存，不重复恢复");
        a.Equal(2, service.DiscoveryRounds, "已知摘要不增加依赖轮数");
        var seeded = Method(2);
        var seed = new MethodRecoveryResult(seeded, 0x300, new(seeded, []), []);
        service.Seed(new(seeded, 0x300), seed);
        a.True(ReferenceEquals(seed, service.Recover(seeded, 0x300)), "批量恢复结果可直接复用");
        a.True(!ReferenceEquals(seed, service.RecoverInstance(seeded, 0x300)), "实例恢复与定义恢复分别缓存");
        a.True(!ReferenceEquals(seed, service.Recover(seeded, 0x304)), "入口不同不能共用摘要");
        var generic = Method(3).Method;
        var slot = new GenericParameterDef { Name = "T", Position = 0, Attributes = GenericParameterAttributes.None };
        generic.GenericParameters = [slot];
        var parameter = new GenericParameterRef("T", true, 0) { Parameter = slot };
        var narrow = new MethodRef(generic, [], [parameter with { Binding = new(NativeBindingKind.Reference, new DefinitionRef(owner, []), 0x400) }]);
        var wide = new MethodRef(generic, [], [parameter with { Binding = new(NativeBindingKind.Reference, new DefinitionRef(owner, []), 0x500) }]);
        a.True(narrow.Equals(wide), "托管身份忽略原生布局来源");
        a.True(!ReferenceEquals(service.RecoverInstance(narrow, 0x600), service.RecoverInstance(wide, 0x600)), "摘要键保留原生布局来源");
        return a.Finish("method-summaries");
    }
}
