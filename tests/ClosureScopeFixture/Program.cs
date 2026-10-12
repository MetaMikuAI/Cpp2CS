using Sekai;
using Sekai.Mysekai;
using Sekai.Mysekai.ContentList;
using Sekai.UI;

var checks = 0;
void Check(bool condition, string name) { if (!condition) throw new Exception(name); checks++; }
async Task Throws<T>(Action action) where T : Exception
{
    var run = Task.Run(action); await run.ContinueWith(_ => { });
    Check(run.Exception?.InnerException is T, typeof(T).Name);
}
var group = new UIPartsCustomScorePlayerTabGroup { _selectorCells = [new(), new(), new()] };
group.SetCellCallback();
foreach (var cell in group._selectorCells) cell.Callback(99);
Check(group.Clicks.SequenceEqual(new[] { 0, 1, 2 }), "deferred callbacks retain per-iteration index");
var oldCallback = group._selectorCells[1].Callback;
group.SetCellCallback(); oldCallback(-1); group._selectorCells[2].Callback(-1);
Check(group.Clicks.TakeLast(2).SequenceEqual(new[] { 1, 2 }), "different setup invocations have independent captures");
var empty = new UIPartsCustomScorePlayerTabGroup { _selectorCells = [] }; empty.SetCellCallback();
Check(empty.Clicks.Count == 0, "empty loop");
await Throws<NullReferenceException>(() => new UIPartsCustomScorePlayerTabGroup().SetCellCallback());
await Throws<NullReferenceException>(() => new UIPartsCustomScorePlayerTabGroup { _selectorCells = [null] }.SetCellCallback());
var filter = new CanvasMemberListFilterDialog { _rarityTypeCheckBoxies = [new(), new(), new()] };
filter.SettingResult.UnCheckedFilterRarityTypes = [CardRarityFilterType.Two];
ImprovedLinq.Saved.Clear(); filter.SetRarityFilterType();
Check(filter._rarityTypeCheckBoxies.Select(c => c.Value).SequenceEqual(new[] { true, false, true }), "shared index updated each iteration");
var deferred = ImprovedLinq.Saved.ToArray();
Check(deferred.Length == 3 && deferred.All(p => !p((CardRarityFilterType)3)), "all predicates share final index after loop");
filter._rarityTypeCheckBoxies = [new()]; filter.SetRarityFilterType();
Check(deferred.All(p => !p((CardRarityFilterType)3)) && !ImprovedLinq.Saved.Last()((CardRarityFilterType)1), "loop environment independent between calls");
var owner = new DerivedList(); var firstCell = new UIPartsItemThumbnailListViewItem { CurrentIndex = 7 };
var ordinary = new UserResource(11, 2, 3, 4);
owner.SetupCellInPlaceable(5, firstCell, ordinary); firstCell.CurrentIndex = 9; firstCell.Callback(null);
Check(owner.Clicks.Last() == (ordinary, 9), "outer callback reads cell index at invocation and dispatches virtually");
var special = new UserResource(21, 28, 8, 99); var secondCell = new UIPartsItemThumbnailListViewItem { CurrentIndex = 10 };
owner.SetupCellInPlaceable(6, secondCell, special); secondCell.CurrentIndex = 12; secondCell.Callback(null);
Check(owner.Clicks.Last().Resource == secondCell.Resource && secondCell.Resource != special && secondCell.Resource.Count == 17 && owner.Clicks.Last().Index == 12, "nested environment uses reconstructed resource and live parent cell");
owner.SetupCellInPlaced(6, secondCell, special); secondCell.Callback(null);
Check(owner.Clicks.Last().Resource.Count == 23, "second real nested method selects placed count");
firstCell.Callback(null);
Check(owner.Clicks.Last() == (ordinary, 9), "different nested environment instances remain independent");
var (outer, inner, update) = SharedCaptures.Create(owner, firstCell, ordinary);
var replacement = new UserResource(31, 28, 1, 3);
update(secondCell, replacement); outer(null); inner(null);
Check(owner.Clicks.TakeLast(2).SequenceEqual(new[] { (ordinary, 12), (replacement, 12) }), "parent reassignment shared; child resource mutation confined to child capture");
update(null, replacement);
await Throws<NullReferenceException>(() => outer(null)); await Throws<NullReferenceException>(() => inner(null));
await Throws<NullReferenceException>(() => owner.SetupCellInPlaced(0, firstCell, null));
Console.WriteLine($"PASS: {checks} generated closure scope checks; UI and manager contract stubs, not game runtime");

public sealed class DerivedList : UserResourceContentList
{
    public List<(UserResource Resource, int Index)> Clicks = [];
    public override void OnClickCell(UserResource resource, int index) => Clicks.Add((resource, index));
}
public static class ImprovedLinq
{
    public static List<Func<CardRarityFilterType, bool>> Saved = [];
    public static bool All<T>(IEnumerable<T> items, Func<T, bool> predicate)
    {
        if (predicate is Func<CardRarityFilterType, bool> p) Saved.Add(p);
        return items.All(predicate);
    }
}
namespace Sekai
{
    public sealed class UIPartsCustomScorePlayerSelectorCell { public Action<int> Callback; public void SetCallback(Action<int> callback) => Callback = callback; }
    public enum CardRarityFilterType { One, Two, Three }
    public sealed class UIPartsCheckBox { public bool Value; public void set_Check(bool value) => Value = value; }
    public sealed class UserResource(int id, int type, int level, int count)
    {
        public int resourceId = id, ResourceType = type, resourceLevel = level, Count = count;
    }
}
namespace Sekai.UI
{
    public partial class UIPartsCustomScorePlayerTabGroup
    {
        public UIPartsCustomScorePlayerSelectorCell[] _selectorCells;
        public List<int> Clicks = [];
        public void OnClickCell(int index) => Clicks.Add(index);
    }
}
namespace Sekai.Mysekai
{
    public partial class CanvasMemberListFilterDialog { public UIPartsCheckBox[] _rarityTypeCheckBoxies; public FilterSettings SettingResult = new(); }
    public sealed class FilterSettings { public List<CardRarityFilterType> UnCheckedFilterRarityTypes = []; }
    public sealed class FixtureSiteLayoutedManager
    {
        public int GetCustomProfileCollectionResourcePlaceableCount(int id) => 17;
        public int GetCustomProfileCollectionResourcePlacedCount(int id) => 23;
    }
}
namespace Sekai.Mysekai.ContentList
{
    public partial class UserResourceContentList { public virtual void OnClickCell(UserResource resource, int index) => throw new Exception("virtual dispatch lost"); }
    public sealed class UIPartsItemThumbnailListViewItem
    {
        public int CurrentIndex;
        public Action<UserResource> Callback;
        public UserResource Resource;
        public void Setup(int index, UserResource resource, Action<UserResource> callback, object a, object b) { Resource = resource; Callback = callback; }
        public void SetupCustomProfileCollectionResource(int index, UserResource resource, Action<UserResource> callback, object a, object b) => Setup(index, resource, callback, a, b);
    }
}
namespace CP { public static class SingletonMonoBehaviour<T> where T : new() { public static T Instance = new(); } }
