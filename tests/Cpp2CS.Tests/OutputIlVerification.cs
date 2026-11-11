using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using Cpp2CS.Output;
using ILVerify;

namespace Cpp2CS.Tests;

internal static class OutputIlVerification
{
    public static void Check(Assertions checks, Skeleton skeleton)
    {
        using var resolver = new Resolver(skeleton);
        var verifier = new Verifier(resolver);
        verifier.SetSystemModuleName(AssemblyNameInfo.Parse("mscorlib"));
        var errors = verifier.Verify(resolver.ResolveAssembly(AssemblyNameInfo.Parse("OutputChecks"))!).ToArray();
        foreach (var error in errors) Console.Error.WriteLine($"ILVerify: {error.Code}: {error.Message}");
        checks.True(errors.Length == 0, "写出的程序集通过 Microsoft.ILVerification");
    }

    private sealed class Resolver : IResolver, IDisposable
    {
        private readonly Dictionary<string, PEReader> readers = [];

        public Resolver(Skeleton skeleton)
        {
            foreach (var assembly in skeleton.Assemblies)
            {
                using var stream = new MemoryStream();
                assembly.Write(stream);
                readers.Add(assembly.Name.Name, new PEReader(new MemoryStream(stream.ToArray())));
            }
        }

        public PEReader? ResolveAssembly(AssemblyNameInfo assemblyName) => readers.GetValueOrDefault(assemblyName.Name!);
        public PEReader? ResolveModule(AssemblyNameInfo referencingAssembly, string fileName) => readers.GetValueOrDefault(Path.GetFileNameWithoutExtension(fileName));
        public void Dispose()
        {
            foreach (var reader in readers.Values) reader.Dispose();
        }
    }
}
