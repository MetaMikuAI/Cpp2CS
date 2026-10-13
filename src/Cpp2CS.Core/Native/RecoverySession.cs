using System.Security.Cryptography;
using System.Text.Json;

namespace Cpp2CS.Native;

public sealed record NativeInputs(string Binary, string Symbols, string Header, string ManagedAssembly, string Capstone, string Clang, string? Metadata = null);
public sealed record SsaRecovery(NativeSsaProgram Program, InterfaceCall[] Interfaces, SsaManagedCall[] Calls, SsaManagedStore[] Stores,
    AsyncProtocol? Async, string[] Diagnostics, string[] LegacyProblems)
{
    public AwaitSiteAnalysis? AwaitSites { get; init; }
    public VirtualCall[] VirtualCalls { get; init; } = [];
    public AsyncBody? Body { get; init; }
    public SsaCallStorage[] CallStorages { get; init; } = [];
    public string[] OrdinaryProblems { get; init; } = [];
    [System.Text.Json.Serialization.JsonIgnore] public LiftResult? Projection => Body?.Projection ?? Async?.Projection;
    public string? CSharp => Body?.CSharp ?? Async?.CSharp;
}
public sealed class RecoverySession : IDisposable
{
    public ElfImage Image { get; }
    public Symbols Symbols { get; }
    private readonly Arm64Decoder decoder;
    private readonly ManagedNames managed;
    private readonly Arm64MethodReader reader;
    private readonly NativeAbi abi;
    private readonly HeaderLayout layouts;
    private readonly RuntimeProfile runtime;
    private readonly NativeInputs inputs;
    private readonly Dictionary<string, string> inputHashes;
    public RecoverySession(NativeInputs inputs)
    {
        this.inputs = inputs;
        inputHashes = new Dictionary<string, string>();
        foreach (var (role, path) in new[] { ("Symbols", inputs.Symbols), ("Header", inputs.Header), ("ManagedAssembly", inputs.ManagedAssembly), ("Metadata", inputs.Metadata) })
        {
            if (path is null) continue;
            using var file = File.OpenRead(path);
            inputHashes.Add(role, Convert.ToHexString(SHA256.HashData(file)).ToLowerInvariant());
        }
        Image = new(inputs.Binary); Symbols = new(inputs.Symbols);
        decoder = new(inputs.Capstone); managed = new(inputs.ManagedAssembly);
        layouts = new HeaderLayout(inputs.Header, inputs.Clang);
        runtime = new RuntimeProfile(Image);
        abi = new(layouts, managed);
        reader = new(Image, decoder, Symbols);
    }
    public MethodAnalysis Analyze(ulong address) => Analyze(Symbols.Unique(address) ?? throw new InvalidDataException("入口没有唯一符号签名"), Symbols.ForMethod());
    private MethodAnalysis Analyze(NativeMethod source, Symbols symbols)
    {
        var method = abi.Normalize(source);
        ManagedTypeBindings.Bind(method, symbols, layouts, managed);
        var machine = reader.Read(method.Address);
        var flow = NativeControlFlow.Build(machine.Instructions, machine.Boundary, runtime.NoReturn);
        var ssa = new NativeSsa(flow, method, abi, symbols).Build();
        var semantics = new SsaSemantics(ssa, method, symbols, layouts, abi, Image, runtime, new(Image, decoder));
        var virtualCalls = VirtualDispatch.Recover(semantics, symbols, layouts, managed);
        var dispatch = new InterfaceDispatch(semantics, layouts, managed, runtime);
        var interfaces = dispatch.Recover();
        return new(method, machine, flow, ssa, semantics, symbols, virtualCalls, interfaces, dispatch.Diagnostics.ToArray());
    }
    private LiftResult LiftExpression(ulong address)
    {
        var analysis = Analyze(address);
        return new FunctionLifter(Image, decoder, analysis.Symbols, layouts, managed, runtime).Lift(analysis.Machine, analysis.Semantics) with { TypeSymbols = analysis.Symbols };
    }
    public LiftResult Recover(ulong address)
    {
        var analysis = Analyze(address);
        var symbols = analysis.Symbols;
        var flow = analysis.Flow;
        var ssa = analysis.Ssa;
        var semantics = analysis.Semantics;
        SsaSemantics LiftNative(NativeMethod source) => Analyze(source, symbols.ForMethod()).Semantics;
        var async = new AsyncRecovery(semantics, analysis.Method, managed, layouts, symbols, LiftNative).Recover();
        var body = new AsyncBodyRecovery(semantics, analysis.Method, managed, layouts, symbols, LiftNative).Recover();
        var ordinary = async is null && body is null ? SsaBodyRecovery.Recover(analysis, managed, layouts, symbols) : null;
        var result = ordinary?.Body ?? (async is not null || body is not null
            ? new LiftResult(analysis.Method, analysis.Machine.Instructions, [], [], [], new NativeGraph(analysis.Machine.Instructions, runtime.NoReturn))
                { RecoveryPath = "ssa-async" }
            : new FunctionLifter(Image, decoder, symbols, layouts, managed, runtime).Lift(analysis.Machine, semantics));
        var legacyProblems = result.RecoveryPath == "expression" ? result.Problems.ToArray() : [];
        result = result with { TypeSymbols = symbols };
        result.Ssa = new(ssa, analysis.Interfaces, semantics.Calls(), semantics.Stores(), async, analysis.DispatchProblems, legacyProblems)
        { AwaitSites = async is null ? null : Native.AwaitSites.Recover(semantics, symbols, layouts), VirtualCalls = analysis.VirtualCalls, Body = body, CallStorages = semantics.CallStorages(),
            OrdinaryProblems = ordinary?.Problems ?? [] };
        if (result.Ssa.CSharp is not null)
        {
            result.Proofs.AddRange((body?.CSharp is not null ? body.Proofs : async!.Proofs).Select(p => new Proof(address, "SsaAsyncProtocol", p)));
        }
        else if (body is not null)
        {
            result.Problems.AddRange(ssa.Problems.Concat(flow.Problems).Concat(body.Problems).Distinct().Select(p => "SSA: " + p));
            if (result.Problems.Count == 0) result.Problems.Add("SSA: async 源码归约未完成");
        }
        return result;
    }
    public LiftResult View(LiftResult result) => result.Ssa?.CSharp is not null ? result :
        ViewNormalizer.Normalize(DelegateCaches.Normalize(ViewNormalizer.Normalize(result), type => managed.BaseTypeOf(type) == "System.MulticastDelegate"));
    private NativeMethod? LambdaTarget(MetadataExpression referenceExpression)
    {
        var reference = referenceExpression.Reference;
        if (!reference.Name.StartsWith("Method$") || !reference.Name.EndsWith("()")) return null;
        var name = reference.Name[7..^2]; var separator = ManagedNames.LastTopLevelDot(name);
        if (separator < 0 || !Symbols.NamedMethods.TryGetValue(name[..separator] + "$$" + name[(separator + 1)..], out var candidates) ||
            candidates.Length != 1 || Symbols.Unique(candidates[0].Address) is null) return null;
        var method = candidates[0];
        return reference.MethodAddress != 0 && reference.MethodAddress != method.Address ? null : method;
    }
    public LambdaProjection SourceView(LiftResult view)
    {
        var staticMembers = new StaticSourceMembers(layouts, managed, view.TypeSymbols ?? Symbols, LiftExpression);
        var projection = LambdaProjectionBuilder.Build(view, cache =>
        {
        if (LambdaTarget(cache.Method) is not { } method || !managed.IsNonCapturingCachedLambda(view.Method, method, cache)) return null;
        var body = ViewNormalizer.Normalize(LiftExpression(method.Address));
        return LambdaBodies.Expression(body) is { } lambda ? new(cache, lambda, body) : null;
        });
        projection = ClosureProjection.Build(projection, managed, LambdaTarget, address => ViewNormalizer.Normalize(LiftExpression(address)));
        if (projection.Closures.Length > 0)
        {
            var high = staticMembers.Normalize(projection.View);
            foreach (var block in high.Blocks.Values)
            {
                for (var i = 0; i + 1 < block.Statements.Count; i++)
                    if (block.Statements[i] is CallStatement { Result: { } name, Arguments.Length: 0 } allocation && allocation.Name.StartsWith("Runtime.Allocate<") &&
                        block.Statements[i + 1] is CallStatement { Name: ".ctor", Receiver: NameExpression receiver } ctor && receiver.Name == name &&
                        (allocation.Name[17..^1] == ctor.DeclaringType || ctor.Arguments.Length == 0 && ctor.DeclaringType is { } declaring &&
                            ManagedNames.SplitGeneric(declaring) is var definition && ManagedNames.SplitGeneric(allocation.Name[17..^1]) is var concrete &&
                            definition.Name == concrete.Name && definition.Arguments.Length == concrete.Arguments.Length))
                    {
                        block.Statements[i] = new AssignStatement(allocation.Address, name, new InvocationExpression("new " + allocation.Name[17..^1], null, ctor.Arguments, false), allocation.Name[17..^1]);
                        block.Statements.RemoveAt(i + 1);
                        high.Proofs.Add(new(allocation.Address, "SourceObjectConstruction", "adjacent allocation and matching instance constructor; argument evaluations precede allocation"));
                    }
                for (var i = block.Statements.Count - 1; i >= 0; i--)
                    if (block.Statements[i] is EnsureMetadataStatement || i > 0 && block.Statements[i] is CallStatement
                        { Name: "Runtime.GCWriteBarrier", Arguments: [AddressOfExpression address] } && block.Statements[i - 1] is StoreStatement store && store.Target == address.Target)
                        block.Statements.RemoveAt(i);
            }
            projection = projection with { View = high with { SourceLambdaOrigin = managed.GeneratedLambdaOrigin(view.Method) } };
        }
        return projection;
    }
    public string Render(LiftResult result) => result.Ssa?.CSharp ?? new SemanticWriter(result.TypeSymbols ?? Symbols).Structured(SourceView(View(result)).View);

    public void Save(LiftResult result, string directory)
    {
        Directory.CreateDirectory(directory);
        var symbols = result.TypeSymbols ?? Symbols;
        var writer = new SemanticWriter(symbols);
        var prefix = Path.Combine(directory, $"0x{result.Method.Address:x}");
        var analysis = result.Ssa!;
        var ssa = analysis.Program; var flow = ssa.Flow; var async = analysis.Async;
        var csharp = analysis.CSharp;
        var boundary = UnwindBoundary.Read(Image, result.Method.Address);
        File.WriteAllText(prefix + ".async.json", JsonSerializer.Serialize(async, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".finally.json", JsonSerializer.Serialize(result.Finally, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".async-body.json", JsonSerializer.Serialize(analysis.Body, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".await-sites.json", JsonSerializer.Serialize(analysis.AwaitSites, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".ssa-managed.json", JsonSerializer.Serialize(new { interfaces = analysis.Interfaces, analysis.VirtualCalls, analysis.Diagnostics, calls = analysis.Calls, stores = analysis.Stores, callStorages = analysis.CallStorages }, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".ssa-managed.txt", SsaSemanticWriter.Write(analysis));
        File.WriteAllText(prefix + ".ssa.json", JsonSerializer.Serialize(ssa, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".flow.json", JsonSerializer.Serialize(flow, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".flow.txt", string.Join('\n', flow.Nodes.Select(n =>
            $"0x{n.Instruction.Address:x}: {n.Instruction.Mnemonic} {n.Instruction.Display}" +
            (n.Reachable ? "" : " [unreachable]") + "\n" + string.Join('\n', n.Edges.Select(e =>
                $"    {e.Kind} -> {(e.Target is { } target ? $"0x{target:x}" : "<exit>")}" +
                (e.Region is { } region ? $"; actions=[{string.Join(", ", region.Actions.Select(a => $"{a.Filter}:{a.Kind}:type=0x{a.TypeInfo:x}"))}]" : ""))))));
        File.WriteAllText(prefix + ".asm", string.Join('\n', result.Instructions.Select(i => $"0x{i.Address:x}: {i.Mnemonic} {i.Display}")));
        File.WriteAllText(prefix + ".ir.txt", csharp is null ? writer.Raw(result) : SsaSemanticWriter.Write(analysis));
        var view = View(result);
        var projection = SourceView(view);
        File.WriteAllText(prefix + ".lowered.cs.txt", csharp ?? writer.Structured(view));
        File.WriteAllText(prefix + ".cs.txt", csharp ?? writer.Structured(projection.View));
        File.WriteAllText(prefix + ".source.semantics.json", JsonSerializer.Serialize(SemanticData.Function(analysis.Projection ?? projection.View), new JsonSerializerOptions { WriteIndented = true }));
        var lambdaEvidence = new
        {
            kind = "compiler-lambda-source-projection", projection.Diagnostics,
            sites = projection.Sites.Select(s => new { cache = SemanticData.Statement(s.Cache), lambda = SemanticData.Expression(s.Lambda),
                method = s.Body.Method, nativeInstructions = s.Body.Instructions, loweredBody = SemanticData.Function(s.Body), evidence = s.Body.Proofs }),
            limitations = new[] { "source display abstracts compiler cache identity and initialization; lowered view remains authoritative", "capturing environments and method bodies are recorded separately in closures.json", "not a recompilation or game-runtime equivalence proof" }
        };
        File.WriteAllText(prefix + ".lambdas.json", JsonSerializer.Serialize(lambdaEvidence, new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".closures.json", JsonSerializer.Serialize(projection.Closures.Select(c => new
        { c.Allocation, c.EnvironmentType, c.Bindings, lambdas = c.Lambdas.Select(l => new { l.Construction, l.DelegateType,
            lambda = SemanticData.Expression(l.Lambda), method = l.Body.Method, instructions = l.Body.Instructions, body = SemanticData.Function(l.Body) }) }), new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".semantics.json", JsonSerializer.Serialize(SemanticData.Function(result), new JsonSerializerOptions { WriteIndented = true }));
        File.WriteAllText(prefix + ".view.semantics.json", JsonSerializer.Serialize(SemanticData.Function(analysis.Projection ?? view), new JsonSerializerOptions { WriteIndented = true }));
        var report = new
        {
            method = result.Method, binarySha256 = Image.Sha256,
            recoveryPath = analysis.Projection?.RecoveryPath ?? result.RecoveryPath, analysis.OrdinaryProblems,
            status = csharp is not null ? "supported-async-view" : result.Problems.Count == 0 ? "supported-semantic-view" : "partial",
            nativeExecutionValidated = false,
            instructions = result.Instructions.Length, reachableBlocks = result.Blocks.Count,
            unresolved = result.Problems, evidence = projection.View.Proofs,
            sourceProjection = new { lambdaCount = projection.Sites.Length + projection.Closures.Sum(c => c.Lambdas.Length), closureCount = projection.Closures.Length, projection.Diagnostics, loweringPreserved = true },
            blocks = result.Blocks.Values.Select(b => new { b.Address, b.Successors, condition = b.Condition is null ? null : SemanticWriter.Expression(b.Condition), statements = b.Statements.Select(s => new { s.Address, kind = s.GetType().Name, text = SemanticWriter.Statement(s) }) }),
            inputs = new { Symbols = Path.GetFileName(inputs.Symbols), Header = Path.GetFileName(inputs.Header), ManagedAssembly = Path.GetFileName(inputs.ManagedAssembly) },
            inputSha256 = inputHashes,
            compilerContext = managed.CompilerContext(result.Method, Symbols, csharp is not null),
            exceptionTable = boundary,
            nativeFlow = new { instructions = flow.Nodes.Length, reachable = flow.Nodes.Count(n => n.Reachable), flow.Cycles, flow.Problems,
                status = csharp is not null ? "SSA and managed protocol connected" : "native SSA available; high-level protocol unproved" },
            entryAbi = AbiData(result.Method),
            nativeSsa = new { values = ssa.Values.Length, ssa.Problems },
            asyncProtocol = async,
            asyncBody = analysis.Body,
            runtimeFieldEvidence = runtime.Fields,
            nativeCalls = result.Instructions.Where(i => i.Mnemonic == "bl").Select(i => new { i.Address, target = NativeGraph.Target(i),
                candidates = Symbols.Methods.GetValueOrDefault(NativeGraph.Target(i), []).Select(m => m.Name),
                abi = Symbols.Unique(NativeGraph.Target(i)) is { } method ? AbiData(method) : null }),
            limitations = csharp is not null ? ["acyclic business body; supported UniTask storage and compiler protocol must be proved", "runtime initialization and native exception ABI are represented by runtime contracts", "real UniTask scheduler and foreign exception runtime not executed"] : new[] { "legacy semantic propagation is acyclic; native SSA retains cycles", "Dumper symbol/header adapter, not full raw metadata importer",
                "C# view retains runtime operations", "LSDA actions and exception edges parsed; handler state propagation not connected to C# view",
                "indirect aggregate storage and entry stack arguments remain unresolved" }
        };
        File.WriteAllText(prefix + ".json", JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }));
    }
    private object? AbiData(NativeMethod source)
    {
        var method = abi.Normalize(source);
        var layout = abi.Classify(method);
        if (layout is null) return null;
        object Value(Abi.AbiValue value) => new { kind = value.Shape.Kind.ToString(), value.Shape.Size, value.Shape.Alignment, value.Indirect,
            pieces = value.Pieces.Select(p => new { p.ValueOffset, p.Size,
                register = (p.Location as Abi.RegisterLocation)?.Name, bitOffset = (p.Location as Abi.RegisterLocation)?.BitOffset,
                stackOffset = (p.Location as Abi.StackLocation)?.Offset }) };
        return new { arguments = layout.Arguments.Select((a, index) => new { method.Parameters[index].Name, method.Parameters[index].Type, layout = Value(a) }),
            @return = Value(layout.Return), layout.StackBytes };
    }
    public void Dispose() { managed.Dispose(); decoder.Dispose(); }
}
