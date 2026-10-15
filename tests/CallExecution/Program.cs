using System.Text.Json;
using Sekai.Mysekai;

var oracle = JsonDocument.Parse(File.ReadAllText(args[0])).RootElement;
int assertions = 0;
foreach (var row in oracle.GetProperty("stamina").EnumerateArray())
{
    var a = row.GetProperty("a").EnumerateArray().Select(x=>x.GetInt32()).ToArray();
    var b = row.GetProperty("b").EnumerateArray().Select(x=>x.GetInt32()).ToArray();
    var source = new StaminaData(b[0],b[1],b[2]);
    var actual = CallTests.Entry.Execute(source,a[0],a[1],a[2]);
    if (actual != row.GetProperty("sum").GetInt32()) throw new Exception("constructor -> getter native comparison");
    if (source.normal != b[0] || source.enhance != b[1] || source.boost != b[2]) throw new Exception("value receiver escaped");
    int total = 0;
    for (int i=0;i<(a[0]&31);i++)
    {
        if (i==3) continue;
        total += i;
        if (i==8) break;
    }
    if (CallTests.Entry.ExecuteFlow(source,a[0],a[1],a[2]) != unchecked(row.GetProperty("sum").GetInt32()+total))
        throw new Exception("loop, continue, break, jump into an if body");
    if (CallTests.Entry.ExecuteFor(source,a[0],a[1],a[2]) != unchecked(row.GetProperty("sum").GetInt32()+total))
        throw new Exception("for loop step and continue");
    int choice = (a[0]&3) switch { 0=>100,1=>30,2=>20,_=>30 };
    if (CallTests.Entry.ExecuteSwitch(source,a[0],a[1],a[2]) != unchecked(row.GetProperty("sum").GetInt32()+choice))
        throw new Exception("switch fallthrough and default");
    if (CallTests.Entry.ExecuteDo(source,a[0],a[1],a[2]) != unchecked(row.GetProperty("sum").GetInt32()+Math.Max(1,a[0]&31)))
        throw new Exception("do loop first iteration");
    assertions += 6;
}
Console.WriteLine($"PASS: {assertions} assertions, synthetic call sites execute recovered native method bodies");
