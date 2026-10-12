"""把实际生成的视图嵌入最小托管夹具，检查结构化输出的编译及正常分支行为。"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
folder = ROOT / 'artifacts/ViewFixture'
folder.mkdir(exist_ok=True)
view = (ROOT / 'artifacts/recovered/0x51f7f44.cs.txt').read_text(encoding='utf-8')
(folder / 'ViewFixture.csproj').write_text('''<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><ImplicitUsings>enable</ImplicitUsings><Nullable>disable</Nullable><TreatWarningsAsErrors>true</TreatWarningsAsErrors></PropertyGroup></Project>''', encoding='utf-8')
source = r'''
using System.Text.Json;
public static class Runtime
{
    public static byte Flag;
    public static List<object[]> Trace = new();
    public static ref byte Global(ulong address) => ref Flag;
    public static void InitializeMetadata(ulong slot) => Trace.Add(new object[] { "metadata", slot });
    public static void EnsureMetadataInitialized(ulong flag, params ulong[] slots)
    {
        if ((Flag & 1) != 0) return;
        foreach (var slot in slots) InitializeMetadata(slot);
        Flag = 1;
    }
}
public sealed class Subject
{
    public Action<Sekai.APICore<Sekai.EmptyRequest, Sekai.SuiteUser>> onFinishAPI;
    private static ulong MetadataSlot(string name) => name switch
    {
        "Method$Sekai.APICore<EmptyRequest, SuiteUser>.get_Response()" => 0xba73378,
        "Method$CP.SingletonMonoBehaviour<UserDataManager>.get_Instance()" => 0xbaa9218,
        _ => throw new InvalidOperationException(name)
    };
    VIEW
    public void Run(Sekai.APICore<Sekai.EmptyRequest, Sekai.SuiteUser> api) => OnCallBack(api);
}
public static class Entry
{
    public static void Main()
    {
        var cases = new List<object>();
        foreach (var flag in new byte[] { 0, 1, 2 })
        foreach (var state in new[] { 0, 18, 19 })
        foreach (var callback in new[] { false, true })
        {
            Runtime.Flag = flag; Runtime.Trace.Clear();
            var subject = new Subject();
            if (callback) subject.onFinishAPI = api => Runtime.Trace.Add(new object[] { "callback", 0x1001000 });
            subject.Run(new() { Result = new() { State = (Sekai.APIState)state }, Response = new() });
            cases.Add(new { flag, state, callback, trace = Runtime.Trace.ToArray(), finalFlag = Runtime.Flag });
        }
        Console.WriteLine(JsonSerializer.Serialize(cases));
    }
}
namespace Sekai
{
    public class EmptyRequest { }
    public class SuiteUser { }
    public enum APIState { Other = 0, SuccessComplete = 18 }
    public class APIResult { public APIState State { get; set; } }
    public class APICore<A, B> { public APIResult Result { get; set; } public B Response { get; set; } }
}
public sealed class UserDataManager
{
    public void UpdateAll(Sekai.SuiteUser response, bool enabled) => Runtime.Trace.Add(new object[] { "update", 0x1003000, 0x1004000, enabled ? 1 : 0 });
}
namespace CP
{
    public class SingletonMonoBehaviour<T> where T : new()
    {
        public static T Instance { get { Runtime.Trace.Add(new object[] { "singleton" }); return new T(); } }
    }
}
'''
(folder / 'Program.cs').write_text(source.replace('VIEW', view), encoding='utf-8')
print(folder)
