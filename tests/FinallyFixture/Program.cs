using Sekai.Mysekai;

var checks = 0;
void Check(bool value, string name) { if (!value) throw new Exception(name); checks++; }
async Task Throws(Exception expected, Action action)
{
    var task = Task.Run(action); await task.ContinueWith(_ => { });
    Check(task.Exception?.InnerException == expected, "exception identity preserved");
}
async Task ThrowsNull(Action action)
{
    var task = Task.Run(action); await task.ContinueWith(_ => { });
    Check(task.Exception?.InnerException is NullReferenceException, "null reference preserved");
}
void Reset(params int[] ids)
{
    CP.SingletonMonoBehaviour<MasterDataManager>.Instance = new()
    {
        Groups = [new() { id = 1, seq = 5 }, new() { id = 2, seq = 2 }, new() { id = 3, seq = 2 }, new() { id = 4, seq = 9 }]
    };
    BulkHarvestMasterUtility.Targets = new(ids.Select(id => new MasterMysekaiSiteBulkHarvestTarget { mysekaiSiteBulkHarvestTargetGroupId = id }).ToList());
    BulkHarvestMasterUtility.SiteCalls = 0;
}
Reset(1, 2, 2, 3);
var result = BulkHarvestMasterUtility.GetOrderedTargetGroups(7);
Check(result.Select(g => g.id).SequenceEqual(new[] { 2, 3, 1 }), "filter, deduplicate membership and stable ordering");
Check(BulkHarvestMasterUtility.Targets.DisposeCount == 1, "normal exit disposes exactly once");
Reset();
Check(BulkHarvestMasterUtility.GetOrderedTargetGroups(7).Count == 0 && BulkHarvestMasterUtility.Targets.DisposeCount == 1, "empty enumeration disposes");
Reset(1);
CP.SingletonMonoBehaviour<MasterDataManager>.Instance.Groups = null;
Check(BulkHarvestMasterUtility.GetOrderedTargetGroups(7).Count == 0 && BulkHarvestMasterUtility.SiteCalls == 0 && BulkHarvestMasterUtility.Targets.DisposeCount == 0, "null group array skips target enumeration");
Reset(1);
BulkHarvestMasterUtility.Targets.Items[0] = null;
await ThrowsNull(() => BulkHarvestMasterUtility.GetOrderedTargetGroups(7));
Check(BulkHarvestMasterUtility.Targets.DisposeCount == 1, "body exception disposes exactly once");
Reset(1);
var move = new Exception("MoveNext failed"); BulkHarvestMasterUtility.Targets.MoveError = move;
await Throws(move, () => BulkHarvestMasterUtility.GetOrderedTargetGroups(7));
Check(BulkHarvestMasterUtility.Targets.DisposeCount == 1, "MoveNext exception disposes exactly once");
Reset(1);
var dispose = new Exception("Dispose failed"); BulkHarvestMasterUtility.Targets.DisposeError = dispose;
await Throws(dispose, () => BulkHarvestMasterUtility.GetOrderedTargetGroups(7));
Check(BulkHarvestMasterUtility.Targets.DisposeCount == 1, "Dispose exception is not retried");
Reset(1);
BulkHarvestMasterUtility.Targets.Items[0] = null; BulkHarvestMasterUtility.Targets.DisposeError = dispose;
await Throws(dispose, () => BulkHarvestMasterUtility.GetOrderedTargetGroups(7));
Check(BulkHarvestMasterUtility.Targets.DisposeCount == 1, "finally exception replaces body exception once");
Reset(1);
CP.SingletonMonoBehaviour<MasterDataManager>.Instance.Groups = [null];
await ThrowsNull(() => BulkHarvestMasterUtility.GetOrderedTargetGroups(7));
Check(BulkHarvestMasterUtility.Targets.DisposeCount == 1, "LINQ predicate runs after enumeration cleanup");
Reset(1);
BulkHarvestMasterUtility.Targets = null;
await ThrowsNull(() => BulkHarvestMasterUtility.GetOrderedTargetGroups(7));
Reset(1);
var prior = BulkHarvestMasterUtility.GetOrderedTargetGroups(7);
Reset(4);
Check(BulkHarvestMasterUtility.GetOrderedTargetGroups(7).Single().id == 4 && prior.Single().id == 1, "separate invocations have independent captures");
Console.WriteLine($"PASS: {checks} generated-body execution checks");

public sealed class MasterMysekaiSiteBulkHarvestTargetGroup { public int id; public int seq; }
public sealed class MasterMysekaiSiteBulkHarvestTarget { public int mysekaiSiteBulkHarvestTargetGroupId; }
public sealed class MasterDataManager
{
    public MasterMysekaiSiteBulkHarvestTargetGroup[] Groups;
    public MasterMysekaiSiteBulkHarvestTargetGroup[] GetMasterMysekaiSiteBulkHarvestTargetGroups() => Groups;
}
namespace CP { public class SingletonMonoBehaviour<T> { public static T Instance; } }
namespace Sekai.Mysekai
{
    public static partial class BulkHarvestMasterUtility
    {
        public static ObservedTargets Targets;
        public static int SiteCalls;
        public static ObservedTargets GetSiteTargets(int id) { SiteCalls++; return Targets; }
    }
    // 包装真实 List 枚举器，仅增加故障注入和清理计数；恢复的方法体不修改。
    public sealed class ObservedTargets(List<MasterMysekaiSiteBulkHarvestTarget> items)
    {
        public List<MasterMysekaiSiteBulkHarvestTarget> Items = items;
        public int DisposeCount;
        public Exception MoveError, DisposeError;
        public Enumerator GetEnumerator() => new(this);
        public struct Enumerator : IDisposable
        {
            private readonly ObservedTargets owner;
            private List<MasterMysekaiSiteBulkHarvestTarget>.Enumerator inner;
            public Enumerator(ObservedTargets owner) { this.owner = owner; inner = owner.Items.GetEnumerator(); }
            public MasterMysekaiSiteBulkHarvestTarget Current => inner.Current;
            public bool MoveNext() { if (owner.MoveError is { } error) throw error; return inner.MoveNext(); }
            public void Dispose() { owner.DisposeCount++; inner.Dispose(); if (owner.DisposeError is { } error) throw error; }
        }
    }
}
