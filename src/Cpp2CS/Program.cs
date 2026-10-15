using System.Text.Json;
using Cpp2CS.Metadata;
using Cpp2CS.Input;
using Cpp2CS.Recovery;
using Cpp2CS.Output;

if (args.Length == 0) throw new ArgumentException("metadata <DummyDll> <case.json> <output-dir> | recover <catalog> <ctree-dir> <output-dir>");
if (args[0] == "metadata")
{
    var spec = JsonSerializer.Deserialize<CaseSpec>(File.ReadAllText(args[2]), Catalog.Json)!;
    var catalog = Read.Load(args[1], spec);
    Directory.CreateDirectory(args[3]);
    File.WriteAllText(Path.Combine(args[3], "metadata.json"), JsonSerializer.Serialize(catalog, Catalog.Json));
    var requests = catalog.Types.SelectMany(t => t.Methods).Select(m => JsonSerializer.Serialize(new
    {
        action = "decompile", address = m.Address, prototype = m.NativePrototype,
        binary_sha256 = catalog.BinarySha256
    }));
    File.WriteAllLines(Path.Combine(args[3], "requests.jsonl"), requests.Append("{\"action\":\"close\"}"));
    Console.WriteLine($"metadata: {catalog.Types.Length} types, {catalog.Types.Sum(t => t.Methods.Length)} methods, {catalog.Enums.Length} enums");
}
else if (args[0] == "recover")
{
    var catalog = JsonSerializer.Deserialize<Catalog>(File.ReadAllText(args[1]), Catalog.Json)!;
    var bodies = catalog.Types.ToDictionary(t => t.Name, t => t.Methods.Select(m =>
        new Recover(catalog, t, m, new Ctree(Path.Combine(args[2], m.Address[2..] + ".json"), catalog, m)).Run()).ToArray());
    var writer = new CSharp(catalog);
    Cpp2CS.Semantics.Dependencies.Verify(catalog, bodies);
    var code = writer.Generate(bodies);
    Directory.CreateDirectory(args[3]);
    File.WriteAllText(Path.Combine(args[3], "Recovered.cs"), code);
    File.WriteAllText(Path.Combine(args[3], "Recovered.csproj"), """
        <Project Sdk="Microsoft.NET.Sdk">
          <PropertyGroup>
            <TargetFramework>net10.0</TargetFramework>
            <CheckForOverflowUnderflow>true</CheckForOverflowUnderflow>
            <TreatWarningsAsErrors>true</TreatWarningsAsErrors>
          </PropertyGroup>
        </Project>
        """);
    File.WriteAllText(Path.Combine(args[3], "source-map.json"), JsonSerializer.Serialize(writer.Mapping, Catalog.Json));
    File.WriteAllText(Path.Combine(args[3], "manifest.json"), JsonSerializer.Serialize(new
    {
        catalog.BinarySha256, catalog.Assembly, Types = catalog.Types.Select(t => new { t.Name, Methods = t.Methods.Select(m => new { m.Name, m.Token, m.Address }) }),
        Methods = bodies.Values.Sum(x => x.Length), CompleteTypes = catalog.Types.Count(t => t.Complete), PlaceholderBodies = 0,
        PartialDependencies = catalog.Types.Where(t => !t.Complete).Select(t => new { t.Name, t.Assembly, Methods = t.Methods.Select(m => m.Token) }),
        Dependencies = bodies.SelectMany(t => t.Value.Select(b => new
        {
            Owner = t.Key, b.Method.Token, Calls = Cpp2CS.Semantics.Dependencies.In(b).Select(c => c.Key)
        })), RuntimeDependencies = new[] { "System.Object..ctor (CLR)" }, GameRuntimeVerified = false
    }, Catalog.Json));
    Console.WriteLine($"recovered: {catalog.Types.Count(t => t.Complete)} complete types, {bodies.Values.Sum(x => x.Length)} methods");
}
else throw new ArgumentException($"未知命令 {args[0]}");
