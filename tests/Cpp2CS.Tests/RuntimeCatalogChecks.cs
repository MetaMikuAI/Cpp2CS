using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using Cpp2CS.Native.Abi;
using Cpp2CS.Runtime;

namespace Cpp2CS.Tests;

internal static class RuntimeCatalogChecks
{
    public const string Command = "runtime-catalog";
    internal static string[] Paths() => Directory.GetFiles(Path.Combine(ArchitectureChecks.FindRoot(), "spec"), "functions-unity-*.json");
    internal static RuntimeFunctionCatalog Load(string path)
    {
        using var doc = JsonDocument.Parse(File.ReadAllText(path));
        var root = doc.RootElement;
        var target = root.GetProperty("target");
        return RuntimeFunctionCatalog.LoadWithSystem(path, Path.Combine(Path.GetDirectoryName(path)!, "functions-system-android-lp64.json"), root.GetProperty("unity_version").GetString()!, target.GetProperty("triple").GetString()!, target.GetProperty("data_model").GetString()!);
    }
    public static int Run()
    {
        var checks = new Assertions();
        var catalogs = Paths().Select(Load).ToArray();
        checks.True(catalogs.Length > 0 && RuntimeOperations.All.Count > 0, "目录与登记表非空");
        foreach (var op in RuntimeOperations.All.Values)
        {
            checks.True(op.Name.Length > 0 && op.Evidence.Length > 0 && op.Preconditions.Length > 0 &&
                op.Il.Name.Length > 0 && op.Il.Description.Length > 0 && op.Exceptions.Description.Length > 0, op.Name + " 必填栏");
            checks.True(!op.Inputs.IsDefault && !op.PointerEffects.IsDefault && !op.Normal.IsDefault && !op.Exceptional.IsDefault, op.Name + " 集合初始化");
            checks.True(op.Inputs.Select(i => i.Name).Distinct().Count() == op.Inputs.Length && op.Inputs.All(i => i.Name.Length > 0), op.Name + " 输入唯一");
            checks.True((op.Result.Kind == RuntimeValueKind.Void) == (op.Result.Width == RuntimeWidth.None), op.Name + " 结果位宽");
            checks.True(op.Result.Relation.Kind == RuntimeResultRelationKind.None ? op.Result.Relation.Input is null
                : op.Result.Relation.Kind == RuntimeResultRelationKind.InstanceOfInput
                    ? op.Result.Kind == RuntimeValueKind.ManagedReference && op.Inputs.Any(i => i.Name == op.Result.Relation.Input && i.Kind == RuntimeValueKind.Class)
                : op.Inputs.Any(i => i.Name == op.Result.Relation.Input && i.Kind == op.Result.Kind), op.Name + " 结果关系");
            checks.True(op.Result.Relation.Kind != RuntimeResultRelationKind.InputOrNull || op.Result.Kind is RuntimeValueKind.ManagedReference or RuntimeValueKind.NativePointer or RuntimeValueKind.ManagedAddress, op.Name + " 可空结果关系");
            checks.True((op.EventCondition is null) == (op.EventTrigger == RuntimeEventTrigger.Never), op.Name + " 事件条件");
            checks.True(op.DoesNotReturn == (op.Termination != RuntimeTermination.None), op.Name + " 终止类别");
            checks.True(op.Observation != RuntimeObservation.Unobservable || op.EventTrigger == RuntimeEventTrigger.Never, op.Name + " 不可观察事件条件");
            checks.True(op.DoesNotReturn == op.Normal.IsEmpty, op.Name + " 正常结局");
            checks.True(op.Exceptions.MayThrow == (op.Exceptions.Types.Length > 0) && op.Exceptions.MayThrow == (op.Exceptional.Length > 0), op.Name + " 异常结局");
            checks.True((op.Observation == RuntimeObservation.IdempotentEvent) == (op.Idempotence is not null), op.Name + " 幂等条件");
            if (op.Idempotence is { } idempotence)
                checks.True(idempotence.Representations.Length > 0 && op.Normal.Contains(idempotence), op.Name + " 幂等表示与正常后置条件");
            foreach (var effect in op.PointerEffects)
            {
                checks.True(effect.Extent.Kind switch
                {
                    RuntimeExtentKind.ClassValueSize => op.Inputs.Any(i => i.Name == effect.Extent.Input && i.Kind == RuntimeValueKind.Class),
                    RuntimeExtentKind.InputLength => effect.Extent.ElementBytes > 0 && op.Inputs.Any(i => i.Name == effect.Extent.Input && i.Kind == RuntimeValueKind.Integer && i.Use == RuntimeInputUse.Value),
                    RuntimeExtentKind.FixedBytes => effect.Extent.Bytes > 0,
                    _ => effect.Extent.Input is null
                }, op.Name + " 范围输入");
                checks.True(op.Inputs.Any(i => i.Name == effect.Input) && effect.Extent.Description.Length > 0 && effect.Condition.Description.Length > 0 && op.Inputs.Any(i => i.Name == effect.Input && i.Use is RuntimeInputUse.Location or RuntimeInputUse.Pointee), op.Name + " 指针效果");
            }
            foreach (var fact in op.Normal.Concat(op.Exceptional))
            {
                checks.True(fact.Predicate.Length > 0 && fact.When.Description.Length > 0 && fact.Description.Length > 0, op.Name + " 后置条件");
                foreach (var state in fact.Representations)
                {
                    checks.True(op.Inputs.Any(i => i.Name == state.Input) && state.Evidence.Length > 0, op.Name + " 状态输入");
                    checks.True((state.Record is null) == (state.Field is null), op.Name + " 字段引用完整");
                    foreach (var catalog in catalogs)
                    {
                        var layout = RuntimeSpec.Select(catalog.UnityVersion, catalog.Triple, catalog.DataModel).Layout;
                        if (state.Record is { } record) checks.True(layout.Field(record, state.Field!).Size > 0, op.Name + " 布局字段存在");
                        else checks.True(state.Test == RuntimeStateTest.ResolvedMetadata, "匿名状态必须有元数据凭据");
                    }
                }
            }
        }
        foreach (var catalog in catalogs)
        {
            foreach (var function in catalog.Functions)
            {
                checks.True(ReferenceEquals(function, catalog.ByMangledName(function.MangledName)) && catalog.ByName(function.Name).Contains(function), "名称与修饰名查询");
                checks.True(function.Signature is not null && CTypes.Validate(function.RequireSignature()) is null, function.Name + " 原型");
                checks.True(function.Arguments.All(a => function.Operation.Inputs.Any(i => i.Name == a)), function.Name + " 每个形参均对应操作输入");
                checks.True(function.Arguments.Length == function.RequireSignature().Parameters.Length && ReferenceEquals(function.Operation, RuntimeOperations.Get(function.Operation.Name)), "参数与唯一语义");
                checks.True(function.Basis.Length > 0 && function.Recognition is { Symbol: true, Export: null, CallGraph: null, ReferenceShape: null }, "仅符号识别依据");
                if (function.ManagedMethod is { } managed)
                    checks.True(function.Recognition.Import == function.Name && managed.DeclaringType == "System.Math"
                        && managed.TypeArguments.IsEmpty && managed.Parameters.Length == function.Arguments.Length,
                        "数学导入的身份与完整签名来自目录");
            }
            Reject<KeyNotFoundException>(checks, () => catalog.ByName("missing"));
            Reject<KeyNotFoundException>(checks, () => catalog.ByMangledName("missing"));
            Reject<InvalidDataException>(checks, () => RuntimeFunctionCatalog.Load(catalog.Source, "missing", catalog.Triple, catalog.DataModel));
            void Mutation(Action<JsonNode> mutate, Type exception)
            {
                var node = JsonNode.Parse(File.ReadAllText(catalog.Source))!;
                mutate(node);
                using var stream = new MemoryStream(Encoding.UTF8.GetBytes(node.ToJsonString()));
                try { RuntimeFunctionCatalog.Read(stream, "fixture", catalog.UnityVersion, catalog.Triple, catalog.DataModel); checks.True(false, "应拒绝损坏目录"); }
                catch (Exception e) when (e.GetType() == exception) { checks.True(true, "拒绝损坏目录"); }
            }
            Mutation(n => n["schema_version"] = 99, typeof(InvalidDataException));
            Mutation(n => n["functions"]![0]!["recognition"]!["usage_conditions"] = JsonNode.Parse(
                "[{\"kind\":\"unknown\",\"parameter\":0,\"basis\":\"无效条件\"}]"), typeof(InvalidDataException));
            Mutation(n => n["functions"]![0]!["recognition"]!["usage_conditions"] = JsonNode.Parse(
                "[{\"kind\":\"metadata_slot_address\",\"parameter\":-1,\"basis\":\"无效形参\"}]"), typeof(InvalidDataException));
            Mutation(n => n["schema_version"] = "unknown", typeof(InvalidDataException));
            Mutation(n => n["functions"]![0]!["operation"] = "missing", typeof(KeyNotFoundException));
            Mutation(n => n["functions"]![0]!["arguments"] = new JsonArray("missing"), typeof(InvalidDataException));
            Mutation(n => n["functions"]![1]!["mangled_name"] = n["functions"]![0]!["mangled_name"]!.GetValue<string>(), typeof(InvalidDataException));
            var original = catalog.Functions.First(f => f.Name == "Castclass");
            checks.True(original.Operation.Result.ReturnInput == "object", "castclass 正常返回恒等");
            checks.True(RuntimeOperations.Get("IsInstance").Result.Relation == new RuntimeResultRelation(RuntimeResultRelationKind.InputOrNull, "object"), "isinst 输入或空关系");
            checks.True(RuntimeOperations.Get("UnboxAny").Result.ReturnInput is null, "unbox.any 不能无条件当作返回缓冲区");
            checks.True(RuntimeOperations.Get("InitializeClassBeforeFieldInit").HeapEffect == RuntimeHeapEffect.ArbitraryManagedCode, "放宽初始化时机不消除静态构造的堆效果");
            checks.True(RuntimeOperations.Get("InitializeClassBeforeFieldInit") is { Observation: RuntimeObservation.Unobservable, Il.Name: "EraseBeforeFieldInit" },
                "beforefieldinit 契约下消去显式初始化时机");
        }
        Console.WriteLine($"运行时操作 {RuntimeOperations.All.Count}；目录 {string.Join('；', catalogs.Select(c => c.Triple + "=" + c.Functions.Length))}");
        return checks.Finish("运行时操作与目录");
    }
    private static void Reject<T>(Assertions checks, Action action) where T : Exception
    {
        try { action(); checks.True(false, "应抛出 " + typeof(T).Name); }
        catch (T) { checks.True(true, "明确拒绝缺项"); }
    }
}
