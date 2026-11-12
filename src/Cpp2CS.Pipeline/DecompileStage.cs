using Cpp2CS.Model;
using Cpp2CS.Output;

namespace Cpp2CS.Pipeline;

public sealed record SourceMethodFailure(string Identity, string Name, string Reason);
public sealed record SourceTypeFailure(string Assembly, string Type, string Reason);
public sealed record SourceReport(int Files, SourceTypeFailure[] Types, SourceMethodFailure[] Methods);

internal static class DecompileStage
{
    internal static void Mark(ProgramModel model, MethodReport[] rows, BodyEmitter emitter)
    {
        var reports = rows.ToDictionary(r => r.Identity);
        foreach (var method in model.Methods)
        {
            var report = reports.GetValueOrDefault(RecoverySession.Identity(method));
            if (report?.Status is not (MethodStatus.Complete or MethodStatus.NoBody)) emitter.MarkUnrecovered(method, report?.Entry ?? 0);
        }
    }

    internal static SourceReport Write(string output, Skeleton skeleton, ProgramModel model, string? only = null)
    {
        var directory = Path.Combine(output, "src");
        Directory.CreateDirectory(directory);
        var failures = new List<SourceTypeFailure>();
        var methods = new List<SourceMethodFailure>();
        var count = 0;
        foreach (var assembly in model.Assemblies.Where(a => only is null || a.Name == only))
        {
            var failed = new System.Collections.Concurrent.ConcurrentBag<SourceFailure>();
            var sources = Decompilation.Decompile(Path.Combine(output, Skeleton.ImageFileName(assembly.Name)), output,
                _ => true, false, failure: failed.Add);
            foreach (var source in sources)
            {
                var name = assembly.Name + "_" + source.TypeName;
                var invalid = Path.GetInvalidFileNameChars();
                File.WriteAllText(Path.Combine(directory, new string(name.Select(c => invalid.Contains(c) ? '_' : c).ToArray()) + ".cs"), source.Source);
                count++;
            }
            foreach (var failure in failed.Distinct().OrderBy(f => f.TypeName, StringComparer.Ordinal))
            {
                failures.Add(new(assembly.Name, failure.TypeName, failure.Reason));
                foreach (var method in model.Methods.Where(m => m.Owner.Assembly == assembly.Name))
                {
                    var type = skeleton.Method(method).DeclaringType;
                    while (type.DeclaringType is not null) type = type.DeclaringType;
                    if (type.FullName != failure.TypeName) continue;
                    methods.Add(new(RecoverySession.Identity(method), method.ToString(), failure.Reason));
                }
            }
        }
        return new(count, failures.ToArray(), methods.ToArray());
    }
}
