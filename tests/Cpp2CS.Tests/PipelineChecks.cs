using System.Collections.Immutable;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Mono.Cecil;
using Mono.Cecil.Cil;
using R = System.Reflection;

namespace Cpp2CS.Tests;

internal static class PipelineChecks
{
    public const string Command = "pipeline";
    public static int Run()
    {
        var checks = new Assertions();
        string[] names = ["Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference", "Void"];
        var types = names.Select((n, i) => new TypeDef { Index = i, Assembly = "mscorlib.dll", Namespace = "System", Name = n,
            Token = (uint)(0x02000001 + i), Attributes = R.TypeAttributes.Public, IsValueType = n is not ("Object" or "String"), IsEnum = false }).ToArray();
        var owner = types[0];
        var methods = new[] { "Present", "Missing" }.Select((n, i) => new MethodDef { Index = i, Owner = owner, Name = n,
            Token = (uint)(0x06000001 + i), Attributes = R.MethodAttributes.Public | R.MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1, ReturnType = new DefinitionRef(types.Single(t => t.Name == "Int32"), []) }).ToArray();
        owner.Methods = methods;
        var model = new ProgramModel { MetadataVersion = 31, Assemblies = [new AssemblyDef { Name = "mscorlib.dll", AssemblyName = "mscorlib", Version = new(1, 0), Culture = "", PublicKey = [], Types = types }],
            Types = types, Methods = methods, Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [] };
        var entries = methods.Select((m, i) => new CodeEntry((ulong)(16 + i * 4), EntryKind.Method, MethodRef.Open(m), i, null)).ToArray();
        var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = entries,
            ByAddress = entries.ToDictionary(e => e.Address, e => ImmutableArray.Create(e)), Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(),
            MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
        var facts = new GlobalFacts(new EmptyImage(), model, map, InputCorpusChecks.Spec("arm64-v8a"), "test");
        var output = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", "pipeline-check.local.output");
        var session = new RecoverySession(frontend: new FakeFrontend(), recovery: new FakeRecovery());
        var request = new RecoveryRequest("", "", output) { Jobs = 2 };
        var report = session.Run(facts, request);
        checks.True(report.Summary.Complete == 1 && report.Summary.Holes == 1, "混合结果不互相阻断");
        checks.True(report.Methods[1].Hole is { Layer: "恢复", Reason.Code: "test.missing" }, "洞保留层和结构化原因");
        using var module = ModuleDefinition.ReadModule(Path.Combine(output, "mscorlib.dll"));
        var written = module.Types.Single(t => t.Name == "Object").Methods;
        checks.True(written[0].Body.Instructions.Any(i => i.OpCode.Code == Code.Ldc_I4 && (int)i.Operand == 7 || i.OpCode.Code == Code.Ldc_I4_7)
            && written[0].Body.Instructions.Last().OpCode.Code == Code.Ret, "完整体写出返回常量");
        checks.True(written[1].Body.Instructions.Last().OpCode.Code == Code.Throw, "洞保留占位体");
        using var json = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "recovery.json")));
        checks.True(json.RootElement.GetProperty("methods").GetArrayLength() == 2, "报告落盘并读回");
        using var streamed = new MemoryStream();
        RecoveryReport.Write(streamed, report);
        checks.True(System.Text.Encoding.UTF8.GetString(streamed.ToArray()) == RecoveryReport.Json(report), "流式报告与原格式逐字节一致");
        var withSource = report with { Source = new(1, [new("test", "Type", "类型诊断")], [new("method", "Method", "方法诊断")]) };
        streamed.SetLength(0); streamed.Position = 0; RecoveryReport.Write(streamed, withSource);
        checks.True(System.Text.Encoding.UTF8.GetString(streamed.ToArray()) == RecoveryReport.Json(withSource), "源码诊断数组保持原报告格式");
        var serial = session.Run(facts, request with { Jobs = 1 });
        checks.True(RecoveryReport.Json(report.Methods) == RecoveryReport.Json(serial.Methods), "结果不依赖并行度");
        var filtered = session.Run(facts, request with { Method = "Present", Address = 16 });
        checks.True(filtered.Methods.Length == 1 && filtered.Summary.Complete == 1, "名字和地址筛选");
        var terms = new TermTable(); var entry = new BlockIdentity(); var handler = new BlockIdentity();
        var exception = terms.Atom(new ExceptionAtom(handler), 64);
        var handlerEntry = new HandlerEntry(exception, terms.Atom(new SelectorAtom(handler), 64), [new(ClauseKind.Cleanup, [])]);
        var exceptionContext = new MethodContext(methods[0], entries[0], facts with { Architecture = "arm64" });
        var recovery = new IntegerRecoveryStage();
        foreach (bool hasCall in new[] { false, true })
        {
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            builder.Blocks.Add(new(entry, [], hasCall ? [new Call(new(), new ImageFunction(0), [], [], Unwind: handler)] : [new MemoryFence(new(), "test")], new Return([])));
            builder.Blocks.Add(new(handler, [], [new MemoryWrite(new(), terms.Atom(new RootAtom(AddressRoot.Frame), 64), 32, terms.Constant(1, 32))], new ResumeUnwind(exception), handlerEntry));
            var result = recovery.Run(builder.Freeze(), exceptionContext);
            checks.True(hasCall ? result is Missing<ManagedBody> { Hole.Reason.Code: "lowering.Exception.Fault" }
                : result is Missing<ManagedBody> { Hole.Reason.Code: "lowering.Synchronization" },
                "生产门控拒绝未证明私有的清理与未定义的同步访问");
        }
        return checks.Finish("Pipeline 快速检查");
    }
    private sealed class FakeFrontend : IMethodStage<CodeEntry, NativeFunction>
    {
        public string Name => "前端";
        public StageResult<NativeFunction> Run(CodeEntry input, MethodContext context)
        {
            var terms = new TermTable();
            var entry = new BlockIdentity();
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Constant(0, 64)));
            builder.Blocks.Add(new(entry, [], [], new Return([])));
            return new Completed<NativeFunction>(builder.Freeze());
        }
    }
    private sealed class FakeRecovery : IMethodStage<NativeFunction, ManagedBody>
    {
        public string Name => "恢复";
        public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context) => context.Method.Index == 0
            ? new Completed<ManagedBody>(new(MethodRef.Open(context.Method), [new(0, [new ManagedReturn(0, new ConstantValue(7, context.Method.ReturnType, 32))])]))
            : new Missing<ManagedBody>(new(Name, context.Entry.Address, "测试步骤", new("test.missing", "测试洞")));
    }
    private sealed class EmptyImage : IImage
    {
        public ulong PreferredBase => 0;
        public int PointerWidth => 8;
        public ByteOrder ByteOrder => ByteOrder.LittleEndian;
        public ImmutableArray<ImageRange> Ranges => [];
        public IReadOnlyList<ImageRelocation> Relocations => [];
        public ImmutableArray<ImportSymbol> Imports => [];
        public ImmutableArray<ExportSymbol> Exports => [];
        public ImmutableArray<FunctionSymbol> FunctionSymbols { get; init; } = [];
        public ImmutableArray<FunctionRange> Functions => [];
        public ImmutableArray<TryRegion> TryRegions => [];
        public ImmutableArray<string> Diagnostics => [];
        public AddressInfo Query(ulong offset) => new(StorageKind.Unmapped, 0, false, false);
        public bool IsExecutable(ulong offset, ulong length = 1) => false;
        public bool IsWritable(ulong offset, ulong length = 1) => false;
        public void ReadBytes(ulong offset, Span<byte> destination) => throw new InvalidDataException();
        public ulong ReadUnsigned(ulong offset, int width) => throw new InvalidDataException();
        public PointerTarget ReadPointer(ulong offset) => throw new InvalidDataException();
    }
}
