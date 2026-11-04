using Cpp2CS.Facts;
using Cpp2CS.Input;

internal static class CodeMapProbe
{
    public static int Run(string binary, string metadata, string address)
    {
        var (model, builder) = ModelBuilder.Load(binary, metadata);
        var map = CodeMap.Build(model.Image);
        var value = Convert.ToUInt64(address, 16);
        Console.WriteLine($"container {model.Image.Container}, architecture {model.Image.Architecture}");
        Console.WriteLine($"at {map.At(value)?.Start:x} entry {map.IsEntry(value)} index {map.IndexOf(value)}");
        foreach (var function in map.Functions.Where(f => f.Start + 0x40 >= value && f.Start <= value + 0x40))
            Console.WriteLine($"  {function.Start:x}..{function.End:x} {function.Region} {function.Evidence}");
        var scan = CodeScan.Run(map);
        foreach (var reference in scan.All.Where(r => r.Target == value || r.Site == value))
            Console.WriteLine($"  ref {reference.Kind} site 0x{reference.Site:x} target 0x{reference.Target:x}");
        var (registrations, _) = RegistrationReader.Read(model, builder.CodeRegistration, builder.MetadataRegistration);
        foreach (var entry in registrations.Entries.Where(e => e.Address + 0x40 >= value && e.Address <= value + 0x40))
            Console.WriteLine($"  entry {entry}");
        return 0;
    }
}
