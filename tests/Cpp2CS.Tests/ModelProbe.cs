#nullable enable
using Cpp2CS.Input;

namespace Cpp2CS.Tests;

/// <summary>еЏЄж ёеЇ№жЁЎећ‹е»єз«‹пјЊдёЌиї›е…Ґд»Јз Ѓж е°„гЂ‚</summary>
internal static class ModelProbe
{
    public static int Run(string binary, string metadata)
    {
        var (model, builder) = ModelBuilder.Load(binary, metadata);
        Console.WriteLine($"metadata {model.MetadataVersion}, il2cpp {model.Il2CppVersion}");
        Console.WriteLine($"codeRegistration 0x{builder.CodeRegistration:x}, metadataRegistration 0x{builder.MetadataRegistration:x}");
        Console.WriteLine($"assemblies {model.Assemblies.Count}, types {model.Types.Count}, methods {model.Methods.Count}, fields {model.Fields.Count}");
        Console.WriteLine($"runtimeTypes {model.RuntimeTypes.Count}, methodSpecs {model.MethodSpecs.Count}, fieldRefs {model.FieldRefs.Count}, strings {model.StringLiterals.Count}");
        var app = model.Assemblies.FirstOrDefault(a => a.Name == "Assembly-CSharp.dll");
        if (app is not null)
            Console.WriteLine($"Assembly-CSharp types {app.Types.Count}, methods {app.Types.Sum(t => t.Methods.Count)}");
        foreach (var type in model.Types.Where(t => t.Assembly == "Assembly-CSharp.dll").Take(5))
            Console.WriteLine($"  {type.FullName}: fields {type.Fields.Count}, methods {type.Methods.Count}");
        return 0;
    }
}

