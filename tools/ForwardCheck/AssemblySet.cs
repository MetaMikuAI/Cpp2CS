using System.Diagnostics;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel;
using Cpp2CS.Output;
using Cpp2CS.Snapshot;
using ILVerify;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>写入私有暂存目录，回读直接打开磁盘上的 PE。全部核对完成后才发布。</summary>
internal sealed class AssemblySet : IDisposable, IResolver
{
    private readonly DirectoryInfo stage = Directory.CreateTempSubdirectory("cpp2cs-assemblies.local.");
    private readonly Dictionary<EntityRef, (string Image, int Token)> hosts = [];
    public SrmMetadata Reader { get; private set; } = null!;
    public double Seconds { get; private set; }
    public long Peak { get; private set; }
    public int Count { get; private set; }

    public void Generate(Il2CppInput input, ModelMetadata facts, IEnumerable<ManagedBody> recovered)
    {
        var model = facts.Model;
        var grouped = recovered.ToLookup(body =>
        {
            int m = facts.Keys.DescribeMethod(body.Host.Entity)!.Definition;
            int owner = model.Methods[m].Owner;
            return model.Images.Single(i => owner >= i.FirstType && owner < i.FirstType + i.TypeCount);
        });
        var clock = Stopwatch.StartNew();
        using var process = Process.GetCurrentProcess();
        long peak = 0;
        void Measure()
        {
            lock (process)
            {
                process.Refresh();
                peak = Math.Max(peak, process.WorkingSet64);
            }
        }
        var timer = new System.Threading.Timer(_ => Measure(), null, 0, 10);
        try
        {
            foreach (var image in model.Images)
            {
                var builder = new AssemblyImage(facts, input.AssemblyMetadata.Value, image, grouped[image]);
                foreach (var (e, token) in builder.Write(stage.FullName)) hosts.Add(e, (image.Name, token));
            }
            Measure();
        }
        finally { timer.DisposeAsync().AsTask().GetAwaiter().GetResult(); }
        Seconds = clock.Elapsed.TotalSeconds;
        Peak = peak;
        Count = model.Images.Count;
        Reader = new(stage.FullName, facts, input.AssemblyMetadata.Value);
    }

    public (Module Module, int Token) Host(EntityRef entity)
    {
        var (image, token) = hosts[entity];
        return (Reader.LoadImage(image)!, token);
    }

    public PEReader ResolveAssembly(AssemblyNameInfo name) => Reader.Load(name.Name)?.Pe ?? throw new InvalidDataException($"找不到程序集 {name.Name}");
    public PEReader ResolveModule(AssemblyNameInfo _, string name) => Reader.LoadImage(name)?.Pe ?? throw new InvalidDataException($"找不到模块 {name}");
    public Dictionary<string, int> Verify(IEnumerable<EntityRef> entities, out int passed)
    {
        var verifier = new Verifier(this);
        var core = Reader.Facts.CoreType("Object").Definition;
        var model = Reader.Facts.Model;
        int assembly = model.Images.Single(im => core >= im.FirstType && core < im.FirstType + im.TypeCount).Assembly;
        verifier.SetSystemModuleName(AssemblyNameInfo.Parse(model.Assemblies[assembly].Name));
        var errors = new Dictionary<string, int>();
        passed = 0;
        foreach (var e in entities)
        {
            var (module, token) = Host(e);
            bool ok = true;
            var h = (MethodDefinitionHandle)MetadataTokens.EntityHandle(token);
            foreach (var error in verifier.Verify(module.Pe, h))
            {
                ok = false;
                string reason = error.Code == VerifierError.None ? error.Message : error.Code.ToString();
                errors[reason] = errors.GetValueOrDefault(reason) + 1;
            }
            if (ok) passed++;
        }
        return errors;
    }

    public void Publish(string destination)
    {
        Directory.CreateDirectory(destination);
        foreach (var file in stage.GetFiles())
        {
            string path = Path.Combine(destination, file.Name);
            string temp = Path.Combine(destination, Guid.NewGuid() + ".local.tmp");
            try { file.CopyTo(temp); File.Move(temp, path, true); }
            finally { File.Delete(temp); }
        }
    }
    public void Dispose()
    {
        Reader?.Dispose();
        stage.Delete(true);
    }
}
