using System.Runtime.CompilerServices;
using Cysharp.Threading.Tasks;
using Sekai.Mysekai;

var checks = 0;
foreach (var detail in new[] { false, true })
foreach (var show in new[] { false, true })
foreach (var outcome in new[] { "ready", "pending", "cancel", "fault" })
{
    Context.Reset();
    var list = new SecretShopListView(); var item = new SecretShopItemDetailView();
    if (outcome == "ready") Context.Completion.SetResult();
    var task = (detail ? (show ? item.ShowFadeAsync(default) : item.HideFadeAsync(default)) :
        (show ? list.ShowFadeAsync(default) : list.HideFadeAsync(default))).AsTask();
    if (outcome == "pending")
    {
        if (task.IsCompleted || Context.Trace.Contains("Show") || Context.Trace.Contains("Hide")) throw new Exception("await continuation ran early");
        Context.Completion.SetResult();
    }
    if (outcome == "cancel") Context.Completion.SetCanceled();
    if (outcome == "fault") Context.Completion.SetException(new InvalidOperationException("fixture"));
    await task.ContinueWith(_ => { });
    var tail = outcome == "fault" ? "Suppress" : show ? "Show" : "Hide";
    if (task.IsFaulted != (outcome == "fault") || Context.Trace.Last() != tail ||
        Context.EndValue != (show ? 1f : 0f) || Context.Duration != 0.2f) throw new Exception("fade contract mismatch");
    checks++;
}
foreach (var next in new[] { false, true })
{
    Context.Reset();
    var processor = new MysekaiTutorialProcessor();
    var task = (next ? processor.Execute1_3(null, default) : processor.Execute1_2(null, default)).AsTask();
    if (task.IsCompleted || processor.IsDisableActionButtonSwitch) throw new Exception("tutorial resumed early");
    Context.Completion.SetResult();
    await task;
    if (!Context.Trace.Contains("Forget") || Context.Trace.Count(s => s == "SeqNext") != 1 || processor.IsDisableActionButtonSwitch != next)
        throw new Exception("tutorial side effect missing");
    checks++;
}
Console.WriteLine($"PASS: {checks} generated async C# scenarios; contract stubs only, not game/UniTask runtime proof");

public static class Context
{
    public static List<string> Trace = [];
    public static TaskCompletionSource Completion = new();
    public static float EndValue, Duration;
    public static void Reset() { Trace = []; Completion = new(); }
}
namespace Cysharp.Threading.Tasks
{
    [AsyncMethodBuilder(typeof(TestBuilder))]
    public readonly struct UniTask(Task task)
    {
        public Task AsTask() => task ?? Task.CompletedTask;
        public TaskAwaiter GetAwaiter() => AsTask().GetAwaiter();
        public UniTask<bool> SuppressCancellationThrow()
        {
            Context.Trace.Add("Suppress");
            return new(AsTask().ContinueWith(t => { if (t.IsCanceled) return true; t.GetAwaiter().GetResult(); return false; }));
        }
    }
    public readonly struct UniTask<T>(Task<T> task) { public TaskAwaiter<T> GetAwaiter() => task.GetAwaiter(); }
    public struct TestBuilder
    {
        private AsyncTaskMethodBuilder inner;
        public static TestBuilder Create() => new() { inner = AsyncTaskMethodBuilder.Create() };
        public UniTask Task => new(inner.Task);
        public void SetResult() => inner.SetResult();
        public void SetException(Exception e) => inner.SetException(e);
        public void SetStateMachine(IAsyncStateMachine s) => inner.SetStateMachine(s);
        public void Start<S>(ref S s) where S : IAsyncStateMachine => inner.Start(ref s);
        public void AwaitOnCompleted<A, S>(ref A a, ref S s) where A : INotifyCompletion where S : IAsyncStateMachine => inner.AwaitOnCompleted(ref a, ref s);
        public void AwaitUnsafeOnCompleted<A, S>(ref A a, ref S s) where A : ICriticalNotifyCompletion where S : IAsyncStateMachine => inner.AwaitUnsafeOnCompleted(ref a, ref s);
    }
    public static class UniTaskExtensions { public static void Forget(UniTask task) => Context.Trace.Add("Forget"); }
}
namespace UnityEngine { public struct Vector3 { public float x, y, z; } public class CanvasGroup; }
namespace DG.Tweening
{
    public class Tween;
    public static class ShortcutExtensions46
    {
        public static Tween DOFade(UnityEngine.CanvasGroup target, float value, float duration)
        { Context.Trace.Add("Fade"); Context.EndValue = value; Context.Duration = duration; return new(); }
    }
}
namespace Sekai
{
    public enum MysekaiSiteType { }
    public enum MenuScreenType { }
    public readonly struct TweenAwaiter;
    public static class TweenAwaiterExtention
    {
        public static TweenAwaiter ToAwaiter(DG.Tweening.Tween tween, CancellationToken token)
        { if (token != default) throw new Exception("default token lost"); Context.Trace.Add("ToAwaiter"); return default; }
        public static UniTask ToUniTask(TweenAwaiter awaiter, CancellationToken token)
        { Context.Trace.Add("ToUniTask"); return new(Context.Completion.Task); }
    }
}
namespace CP { public class SingletonMonoBehaviour<T> where T : new() { public static T Instance { get; } = new(); } }
namespace Sekai.Mysekai
{
    public partial class SecretShopListView
    {
        public UnityEngine.CanvasGroup _canvasGroup = new();
        public void Show() => Context.Trace.Add("Show");
        public void Hide() => Context.Trace.Add("Hide");
    }
    public partial class SecretShopItemDetailView
    {
        public UnityEngine.CanvasGroup _canvasGroup = new();
        public void Show() => Context.Trace.Add("Show");
        public void Hide() => Context.Trace.Add("Hide");
    }
    public class NPCAvatarPresenter { public void Show() => Context.Trace.Add("NPC.Show"); }
    public class AvatarDataStore { public NPCAvatarPresenter FindNPC(int id) { if (id != 21) throw new Exception(); return new(); } }
    public class MysekaiTutorialManager
    {
        public void SeqNext() => Context.Trace.Add("SeqNext");
        public UniTask ExecuteProcess(int chapter, int stage, object arg) { Context.Trace.Add($"Execute:{chapter}:{stage}"); return default; }
    }
    public partial class MysekaiTutorialProcessor
    {
        public bool IsDisableActionButtonSwitch { get; set; }
        public void ChangeSiteNPC(NPCAvatarPresenter npc, Sekai.MysekaiSiteType site) => Context.Trace.Add("ChangeSite");
        public void AttachCharacterPlacement(string name) { if (name != "tutorial_1_2") throw new Exception(); Context.Trace.Add("Placement"); }
        public UniTask WaitReadyScreenLayer<T>(Sekai.MenuScreenType screen, CancellationToken token) => new(Context.Completion.Task);
        public UniTask WaitToWaitingTalkAndShowNavigation(NPCAvatarPresenter npc, int talk, bool navi, UnityEngine.Vector3 offset, CancellationToken token, Action onTalk, bool rotate)
        {
            if (talk != 3 || navi || rotate || onTalk is not null || offset.x != 0 || offset.y != 1 || offset.z != 0) throw new Exception("value type arguments lost");
            return new(Context.Completion.Task);
        }
    }
}
