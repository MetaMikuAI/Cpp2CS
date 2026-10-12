using Sekai.ApiData;

var checks = 0;
void Check(bool condition, string name) { if (!condition) throw new Exception(name); checks++; }
async Task Throws<T>(Action run) where T : Exception
{
    var task = Task.Run(run);
    await task.ContinueWith(_ => { });
    Check(task.Exception?.InnerException is T, typeof(T).Name);
}
var fixture = new ClosureFixture();
var nameMatch = new MasterMysekaiFixture { name = "chair", assetbundleName = null };
var assetMatch = new MasterMysekaiFixture { name = "table", assetbundleName = "chair_asset" };
var other = new MasterMysekaiFixture { name = "desk", assetbundleName = "desk_asset" };
fixture._allFixtures = [nameMatch, assetMatch, other];
var callback = fixture.CreateCallback();
callback("chair");
Check(fixture._filterdFixtureList.SequenceEqual(new[] { nameMatch, assetMatch }), "both matching paths");
Check(fixture._listView.Events.SequenceEqual(new[] { "create:2:True:False:True", "position:0:0:False" }), "UI order and arguments");
Check(fixture._listView.CurrentItems == fixture._filterdFixtureList, "list published before UI effects");
fixture._allFixtures = [other];
callback("missing");
Check(fixture._filterdFixtureList.Count == 0, "new invocation uses new captured value");
callback("");
Check(fixture._filterdFixtureList.Count == 1, "empty query");
await Throws<ArgumentNullException>(() => callback(null));
fixture._allFixtures = [new() { name = null, assetbundleName = "match" }];
await Throws<NullReferenceException>(() => callback("match"));
fixture._allFixtures = [new() { name = "miss", assetbundleName = null }];
await Throws<NullReferenceException>(() => callback("match"));
fixture._allFixtures = [null];
await Throws<NullReferenceException>(() => callback("match"));
fixture._allFixtures = null;
await Throws<ArgumentNullException>(() => callback("match"));
fixture._allFixtures = [other]; fixture._listView = null;
await Throws<NullReferenceException>(() => callback("desk"));
Check(fixture._filterdFixtureList.SequenceEqual(new[] { other }), "assignment precedes failing UI access");
var (first, second, update) = ClosureFixture.Capture("desk");
var (independent, _, _) = ClosureFixture.Capture("chair");
Check(first(other) && second(other) && !independent(other), "shared scope and independent allocation");
update("chair");
Check(!first(other) && !second(other) && first(nameMatch), "both delegates observe capture mutation");
await Throws<ArgumentNullException>(() => { update(null); first(other); });
Console.WriteLine($"PASS: {checks} generated closure C# checks; real BCL LINQ, UI/Vector2 contract stubs; not game-runtime proof");

public partial class ClosureFixture
{
    public List<MasterMysekaiFixture> _allFixtures;
    public List<MasterMysekaiFixture> _filterdFixtureList;
    public ListView _listView;
    public ClosureFixture() { _listView = new(this); }
}
public sealed class ListView(ClosureFixture owner)
{
    public List<string> Events = [];
    public List<MasterMysekaiFixture> CurrentItems;
    public void CreateViewItem(int count, bool a, bool b, bool c) { CurrentItems = owner._filterdFixtureList; Events.Add($"create:{count}:{a}:{b}:{c}"); }
    public void SetContentPosition(UnityEngine.Vector2 position, bool animate) => Events.Add($"position:{position.x}:{position.y}:{animate}");
}
namespace Sekai.ApiData { public sealed class MasterMysekaiFixture { public string name; public string assetbundleName; } }
namespace UnityEngine { public struct Vector2 { public float x, y; public static Vector2 zero => default; } }
