using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text.Json;
using Cysharp.Threading.Tasks;
using Cysharp.Threading.Tasks.CompilerServices;

var cases = JsonDocument.Parse(File.ReadAllText(args[0])).RootElement.EnumerateArray().ToArray();
var count = 0;
var stateChecks = 0;
var clearChecks = 0;
foreach (var scenario in cases)
{
    var context = new FixtureContext(scenario);
    FixtureContext.Current = context;
    var invocation = System.Threading.Tasks.Task.Run(() =>
    {
        if (!scenario.GetProperty("resumed").GetBoolean())
            _ = Sekai.Mysekai.AvatarFactory.CreatePlayerAvatar(true, context.Info, context.Parent, context.View, context.Cancellation.Token);
        else
        {
            var method = typeof(Sekai.Mysekai.AvatarFactory).GetMethod("CreatePlayerAvatar")!;
            var stateType = method.GetCustomAttribute<AsyncStateMachineAttribute>()!.StateMachineType;
            var state = Activator.CreateInstance(stateType)!;
            foreach (var field in stateType.GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
            {
                if (field.FieldType == typeof(int)) field.SetValue(state, 0);
                else if (field.FieldType == typeof(AsyncUniTaskMethodBuilder)) field.SetValue(state, AsyncUniTaskMethodBuilder.Create());
                else if (field.FieldType == typeof(UniTask.Awaiter)) field.SetValue(state, new UniTask(context).GetAwaiter());
            }
            context.StateSnapshot = state;
            ((IAsyncStateMachine)state).MoveNext();
        }
    });
    ((IAsyncResult)invocation).AsyncWaitHandle.WaitOne();
    var expectedTrace = scenario.GetProperty("trace").EnumerateArray().Select(x => x.GetString()).ToArray();
    var actualExit = invocation.Exception is null ? "return" : "propagate";
    if (!context.Trace.SequenceEqual(expectedTrace) || actualExit != scenario.GetProperty("exit").GetString())
        throw new InvalidDataException($"case {count}: {string.Join(',', context.Trace)} / {actualExit}; expected {string.Join(',', expectedTrace)} / {scenario.GetProperty("exit")}; error={invocation.Exception}");
    if (context.StateSnapshot is { } snapshot && actualExit == "return")
    {
        var fields = snapshot.GetType().GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
        var state = (int)fields.Single(f => f.Name == "<>1__state").GetValue(snapshot)!;
        if (unchecked((uint)state) != scenario.GetProperty("state").GetUInt32()) throw new InvalidDataException("state mismatch");
        stateChecks++;
        if (scenario.GetProperty("resumed").GetBoolean())
        {
            var awaiter = fields.Single(f => f.FieldType == typeof(UniTask.Awaiter)).GetValue(snapshot)!;
            if (!awaiter.Equals(default(UniTask.Awaiter))) throw new InvalidDataException("awaiter was not cleared");
            clearChecks++;
        }
    }
    count++;
}
var report = JsonSerializer.Serialize(new { status = "passed", cases = count, stateChecks, clearChecks,
    scope = "generated async C# compiled by Roslyn; runtime contract stubs; traces, state and exception exits compared with ARM64 observations",
    notValidated = new[] { "real UniTask scheduler", "game runtime", "foreign C++ exceptions" } });
File.WriteAllText("artifacts/async-output-oracle.json", report);
Console.WriteLine(report);

public sealed class FixtureContext(JsonElement scenario)
{
    public static FixtureContext Current = null!;
    public JsonElement Scenario { get; } = scenario;
    public List<string> Trace { get; } = [];
    public Sekai.Mysekai.MysekaiAudienceAvatarInfo Info { get; } = new();
    public Sekai.Mysekai.PlayerAvatarView View { get; } = new();
    public UnityEngine.Transform Parent { get; } = new();
    public CancellationTokenSource Cancellation { get; } = new();
    public object? StateSnapshot { get; set; }
    public bool Source => Scenario.GetProperty("source").GetBoolean();
    public bool Runner => Scenario.GetProperty("runner").GetBoolean();
    public short Token => unchecked((short)Scenario.GetProperty("token").GetUInt64());
    public void Call(string name)
    {
        Trace.Add(name);
        ThrowAt(name);
    }
    public void ThrowAt(string name) { if ((Scenario.GetProperty("throws").GetString() ?? "").Split(',').Contains(name)) throw new InvalidOperationException(name); }
}

namespace UnityEngine { public sealed class Transform; }
namespace Sekai.Mysekai
{
    public sealed class MysekaiAudienceAvatarInfo;
    public sealed class PlayerAvatarView;
    public sealed class PlayerAvatarPresenter
    {
        public PlayerAvatarPresenter()
        {
            FixtureContext.Current.ThrowAt("allocate");
            FixtureContext.Current.ThrowAt("ctor");
        }
        public UniTask SetUp(MysekaiAudienceAvatarInfo info, PlayerAvatarView view, UnityEngine.Transform parent, CancellationToken ct)
        {
            var c = FixtureContext.Current;
            if (!ReferenceEquals(info, c.Info) || !ReferenceEquals(view, c.View) || !ReferenceEquals(parent, c.Parent) || ct != c.Cancellation.Token)
                throw new InvalidDataException("captured argument mismatch");
            c.Call("setup");
            return new(c);
        }
    }
}
namespace Cysharp.Threading.Tasks
{
    [AsyncMethodBuilder(typeof(AsyncUniTaskMethodBuilder))]
    public readonly struct UniTask(FixtureContext? context)
    {
        public Awaiter GetAwaiter() => new(context);
        public readonly struct Awaiter(FixtureContext? context) : ICriticalNotifyCompletion
        {
            private readonly short token = context?.Token ?? 0;
            public bool IsCompleted
            {
                get
                {
                    if (context?.Source != true) return true;
                    if (token != context.Token) throw new InvalidDataException("status token mismatch");
                    context.Call("status");
                    return context.Scenario.GetProperty("ready").GetBoolean();
                }
            }
            public void GetResult()
            {
                if (context?.Source != true) return;
                if (token != context.Token) throw new InvalidDataException("result token mismatch");
                context.Call("result");
            }
            public void OnCompleted(Action continuation) => throw new NotSupportedException();
            public void UnsafeOnCompleted(Action continuation) => throw new NotSupportedException();
        }
    }
}
namespace Cysharp.Threading.Tasks.CompilerServices
{
    public struct AsyncUniTaskMethodBuilder
    {
        public static AsyncUniTaskMethodBuilder Create() => new();
        public UniTask Task => new(null);
        public void Start<TStateMachine>(ref TStateMachine state) where TStateMachine : IAsyncStateMachine
        {
            state.MoveNext();
            FixtureContext.Current.StateSnapshot = state;
        }
        public void SetStateMachine(IAsyncStateMachine state) { }
        public void SetResult() { if (FixtureContext.Current.Runner) FixtureContext.Current.Call("complete"); }
        public void SetException(Exception exception) { if (FixtureContext.Current.Runner) FixtureContext.Current.Call("fail"); }
        public void AwaitUnsafeOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine state)
            where TAwaiter : ICriticalNotifyCompletion where TStateMachine : IAsyncStateMachine => FixtureContext.Current.Call("await");
        public void AwaitOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine state)
            where TAwaiter : INotifyCompletion where TStateMachine : IAsyncStateMachine => throw new NotSupportedException();
    }
}
