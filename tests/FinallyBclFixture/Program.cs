using Sekai.Mysekai;

var checks = 0;
void Check(bool condition, string name) { if (!condition) throw new Exception(name); checks++; }
async Task ThrowsNull(Action action)
{
    var task = Task.Run(action); await task.ContinueWith(_ => { });
    Check(task.Exception?.InnerException is NullReferenceException, "null exception");
}
void Reset()
{
    CP.SingletonMonoBehaviour<MasterDataManager>.Instance = new()
    { Groups = [new() { id = 1, seq = 3 }, new() { id = 2, seq = 1 }, new() { id = 3, seq = 1 }, new() { id = 4, seq = 0 }] };
    BulkHarvestMasterUtility.Targets = [new() { mysekaiSiteBulkHarvestTargetGroupId = 1 }, new() { mysekaiSiteBulkHarvestTargetGroupId = 3 }, new() { mysekaiSiteBulkHarvestTargetGroupId = 2 }, new() { mysekaiSiteBulkHarvestTargetGroupId = 1 }];
}
Reset();
Check(BulkHarvestMasterUtility.GetOrderedTargetGroups(1).Select(g => g.id).SequenceEqual(new[] { 2, 3, 1 }), "real List Enumerator, HashSet and stable LINQ ordering");
BulkHarvestMasterUtility.Targets = [];
Check(BulkHarvestMasterUtility.GetOrderedTargetGroups(1).Count == 0, "empty targets");
CP.SingletonMonoBehaviour<MasterDataManager>.Instance.Groups = null;
Check(BulkHarvestMasterUtility.GetOrderedTargetGroups(1).Count == 0, "null groups returns empty list");
Reset(); BulkHarvestMasterUtility.Targets[0] = null;
await ThrowsNull(() => BulkHarvestMasterUtility.GetOrderedTargetGroups(1));
Reset(); CP.SingletonMonoBehaviour<MasterDataManager>.Instance.Groups = [null];
await ThrowsNull(() => BulkHarvestMasterUtility.GetOrderedTargetGroups(1));
Reset(); BulkHarvestMasterUtility.Targets = null;
await ThrowsNull(() => BulkHarvestMasterUtility.GetOrderedTargetGroups(1));
Reset(); CP.SingletonMonoBehaviour<MasterDataManager>.Instance = null;
await ThrowsNull(() => BulkHarvestMasterUtility.GetOrderedTargetGroups(1));
Console.WriteLine($"PASS: {checks} actual-BCL generated-body checks");

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
        public static List<MasterMysekaiSiteBulkHarvestTarget> Targets;
        public static List<MasterMysekaiSiteBulkHarvestTarget> GetSiteTargets(int id) => Targets;
    }
}
