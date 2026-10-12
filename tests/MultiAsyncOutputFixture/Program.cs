using System.Runtime.CompilerServices;
using System.Text.Json;
using Cysharp.Threading.Tasks;

var observations = JsonSerializer.Deserialize<JsonElement[]>(File.ReadAllText("artifacts/multi-async-observations.json"))!;
var count = 0;
foreach (var observation in observations)
{
    Scenario.Input = observation; Scenario.Trace.Clear(); Scenario.Pending.Clear();
    var manager = new Sekai.Mysekai.MysekaiBGMManager();
    Task output = Scenario.Text("kind") switch
    {
        "branch" => manager.PlayDefaultBGMAsync(42, Scenario.Number("branch") == 0 ? 77 : 88, default).Task,
        "generic" => manager.LoadAndPlayAsync(new(), Scenario.Flag("fade"), default).Task,
        _ => new AnimationOverride().PlayInAnimationAsync().Task
    };
    while (Scenario.Pending.TryDequeue(out var continuation)) continuation();
    var expected = observation.GetProperty("trace").EnumerateArray().Select(x => x.GetString()).ToArray();
    if (!output.IsCompleted || output.IsFaulted != observation.GetProperty("failed").GetBoolean() || !Scenario.Trace.SequenceEqual(expected))
        throw new InvalidOperationException($"Case {count}: {observation}\nactual {string.Join(',', Scenario.Trace)} fault={output.Exception}");
    if (!output.IsFaulted && output is Task<bool> generic && Scenario.Text("kind") == "generic" && generic.Result != Scenario.Flag("result"))
        throw new InvalidOperationException("泛型结果不匹配");
    count++;
}
File.WriteAllText("artifacts/multi-async-compiled.json", JsonSerializer.Serialize(new { status = "passed", cases = count,
    scope = "actual generated C# compiled and executed; traces and failures compared with real ARM64 under matching stubs",
    notValidated = new[] { "real game runtime", "real UniTask scheduler" } }, new JsonSerializerOptions { WriteIndented = true }));
Console.WriteLine($"PASS: {count} generated C# / ARM64 scenarios");

static class Scenario
{
    public static JsonElement Input;
    public static readonly List<string> Trace = [];
    public static readonly Queue<Action> Pending = [];
    public static string Text(string key) => Input.GetProperty(key).GetString()!;
    public static bool Flag(string key) => Input.GetProperty(key).GetBoolean();
    public static int Number(string key) => Input.GetProperty(key).GetInt32();
    public static void Throw(string label) { if (Text("throws") == label) throw new InvalidOperationException(label); }
    public static UniTask Work(int index) { Throw("work" + index); return new(index); }
}
sealed class AnimationOverride : Sekai.Mysekai.MysekaiHousingCompetition.MysekaiHousingCompetitionViewBase
{
    public override UniTask PlayPageInAnimationAsync() { Scenario.Trace.Add("page"); return Scenario.Work(0); }
    public override UniTask PlayListInAnimationAsync() { Scenario.Trace.Add("list"); return Scenario.Work(1); }
}
namespace Cysharp.Threading.Tasks
{
    // 差分测试调度器，提供可控的挂起与恢复行为。
    [AsyncMethodBuilder(typeof(TestBuilder))]
    public readonly struct UniTask
    {
        public readonly Task<bool> Task;
        private readonly int index;
        public UniTask(int index) { this.index = index; Task = null!; }
        public UniTask(Task<bool> task) { Task = task; index = -1; }
        public TestAwaiter<bool> GetAwaiter() => new(Task, index);
    }
    [AsyncMethodBuilder(typeof(TestBuilder<>))]
    public readonly struct UniTask<T>
    {
        public readonly Task<T> Task;
        private readonly int index;
        public UniTask(int index) { this.index = index; Task = null!; }
        public UniTask(Task<T> task) { Task = task; index = -1; }
        public TestAwaiter<T> GetAwaiter() => new(Task, index);
    }
    public readonly struct TestAwaiter<T>(Task<T>? task, int index) : ICriticalNotifyCompletion
    {
        public bool IsCompleted
        {
            get
            {
                if (task is not null) return task.IsCompleted;
                if (!Scenario.Flag("source")) return true;
                Scenario.Trace.Add("status" + index); Scenario.Throw("status" + index);
                return Scenario.Input.GetProperty("ready")[index].GetBoolean();
            }
        }
        public T GetResult()
        {
            if (task is not null) return task.GetAwaiter().GetResult();
            if (Scenario.Flag("source")) { Scenario.Trace.Add("result" + index); Scenario.Throw("result" + index); }
            return (T)(object)Scenario.Flag("result");
        }
        public void OnCompleted(Action continuation) => UnsafeOnCompleted(continuation);
        public void UnsafeOnCompleted(Action continuation)
        {
            Scenario.Trace.Add("schedule" + index); Scenario.Throw("schedule" + index); Scenario.Pending.Enqueue(continuation);
        }
    }
    public struct TestBuilder
    {
        private TaskCompletionSource<bool> completion;
        public static TestBuilder Create() => new() { completion = new() };
        public UniTask Task => new(completion.Task);
        public void SetResult() => completion.SetResult(true);
        public void SetException(Exception error) => completion.SetException(error);
        public void SetStateMachine(IAsyncStateMachine stateMachine) { }
        public void Start<T>(ref T stateMachine) where T : IAsyncStateMachine => stateMachine.MoveNext();
        public void AwaitOnCompleted<T, S>(ref T awaiter, ref S stateMachine) where T : INotifyCompletion where S : IAsyncStateMachine => awaiter.OnCompleted(stateMachine.MoveNext);
        public void AwaitUnsafeOnCompleted<T, S>(ref T awaiter, ref S stateMachine) where T : ICriticalNotifyCompletion where S : IAsyncStateMachine => awaiter.UnsafeOnCompleted(stateMachine.MoveNext);
    }
    public struct TestBuilder<T>
    {
        private TaskCompletionSource<T> completion;
        public static TestBuilder<T> Create() => new() { completion = new() };
        public UniTask<T> Task => new(completion.Task);
        public void SetResult(T result) => completion.SetResult(result);
        public void SetException(Exception error) => completion.SetException(error);
        public void SetStateMachine(IAsyncStateMachine stateMachine) { }
        public void Start<S>(ref S stateMachine) where S : IAsyncStateMachine => stateMachine.MoveNext();
        public void AwaitOnCompleted<A, S>(ref A awaiter, ref S stateMachine) where A : INotifyCompletion where S : IAsyncStateMachine => awaiter.OnCompleted(stateMachine.MoveNext);
        public void AwaitUnsafeOnCompleted<A, S>(ref A awaiter, ref S stateMachine) where A : ICriticalNotifyCompletion where S : IAsyncStateMachine => awaiter.UnsafeOnCompleted(stateMachine.MoveNext);
    }
}
namespace CP
{
    public class SingletonMonoBehaviour<T> where T : new()
    {
        public static T? Instance { get { Scenario.Trace.Add("manager"); return Scenario.Text("missing") == "manager" ? default : new(); } }
    }
}
namespace Sekai
{
    public enum MysekaiPhenomenaBrightnessType { Unknown = -1, Day = 0, Night = 2 }
    public class Phenomena { public MysekaiPhenomenaBrightnessType PhenomenaBrightnessType => Scenario.Number("branch") == 2 ? MysekaiPhenomenaBrightnessType.Unknown : MysekaiPhenomenaBrightnessType.Night; }
    public class Bgm { public string assetbundleName = "101"; public string cue = "102"; }
    public class MasterDataManager
    {
        public Bgm? GetMysekaiSiteBgm(int site, MysekaiPhenomenaBrightnessType brightness) { Scenario.Trace.Add($"site:{site}:{(int)brightness}"); return Scenario.Text("missing") == "bgm" ? null : new(); }
        public Phenomena? GetMysekaiPhenomena(int id, bool include) { if (!include) throw new InvalidOperationException(); Scenario.Trace.Add("phenomena:" + id); return Scenario.Text("missing") == "phenomena" ? null : new(); }
        public Bgm? GetMysekaiPhenomenaBgm(int id) { Scenario.Trace.Add("phenomena-bgm:" + id); return Scenario.Text("missing") == "bgm" ? null : new(); }
    }
    public static class ClientConfig { public static class Mysekai { public static int DeliveryPhenomenaId { get { Scenario.Trace.Add("delivery"); return 77; } } } }
    public static class AssetBundleNames { public static string GetBgmName(string name) { Scenario.Trace.Add("asset:" + name); return "103"; } }
}
namespace Sekai.Mysekai
{
    public class MysekaiMusicRecordModel { public (string,string) BGMResourceInfo = ("101","102"); public float FillerSec => 1.25f; }
    public partial class MysekaiBGMManager
    {
        public UniTask PlayDefaultBGMAsync(string name, string cue, System.Threading.CancellationToken ct) { Scenario.Trace.Add($"bgm:{name}:{cue}"); return Scenario.Work(0); }
        public UniTask<bool> LoadAndPlayAsync(string name, string cue, bool fade, float seconds, System.Threading.CancellationToken ct)
        {
            Scenario.Trace.Add($"load:{name}:{cue}:{(fade ? 1 : 0)}:{seconds.ToString(System.Globalization.CultureInfo.InvariantCulture)}");
            Scenario.Throw("work0"); return new(0);
        }
    }
}
namespace Sekai.Mysekai.MysekaiHousingCompetition
{
    public abstract partial class MysekaiHousingCompetitionViewBase
    {
        public abstract UniTask PlayPageInAnimationAsync();
        public abstract UniTask PlayListInAnimationAsync();
    }
}
