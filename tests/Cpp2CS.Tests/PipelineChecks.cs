using System.Collections.Immutable;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
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
        foreach (bool cooperative in new[] { true, false })
        {
            var release = new ManualResetEventSlim();
            var stalled = new RecoverySession(frontend: new FakeFrontend(), recovery: new StallingRecovery(cooperative, release))
                .Run(facts, request with { MethodTimeoutSeconds = 1 });
            release.Set();
            checks.True(stalled.Summary.Complete == 1 && stalled.Summary.ProgramErrors.Length == 1
                && stalled.Methods[1].Hole?.Reason.Code == (cooperative ? "internal.error" : "internal.timeout"),
                (cooperative ? "经过检查点" : "不经过检查点") + "的不结束方法记为程序错误，其余结果照常写出：" + string.Join('；', stalled.Summary.ProgramErrors));
            checks.True(!WorkAbort.Requested, "中止请求不留到下一次运行");
        }
        var timed = session.Run(facts, request with { MethodTimeoutSeconds = 1 });
        checks.True(RecoveryReport.Json(report.Methods) == RecoveryReport.Json(timed.Methods), "带时限的正常运行结果不变");
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
        ReturnBitsChecks(checks, facts);
        return checks.Finish("Pipeline 快速检查");
    }
    private static void ReturnBitsChecks(Assertions checks, GlobalFacts basis)
    {
        var owner = new TypeDef { Index = basis.Model.Types.Count, Assembly = "ReturnFacts.dll", Namespace = "", Name = "Facts",
            Token = 0x02000001, Attributes = R.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var boolean = new DefinitionRef(basis.Model.Types.Single(t => t.Name == "Boolean"), []);
        string[] names = ["Leaf", "Tail", "BadLeaf", "BadTail", "CycleA", "CycleB", "Masked", "OtherSlot", "Indirect", "Inverted", "LiftFailure"];
        var methods = names.Select((name, i) => new MethodDef { Index = i, Owner = owner, Name = name,
            Token = (uint)(0x06000001 + i), Attributes = R.MethodAttributes.Public | R.MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1, ReturnType = boolean }).ToArray();
        owner.Methods = methods;
        var model = new ProgramModel { MetadataVersion = 31, Types = basis.Model.Types.Append(owner).ToArray(), Methods = methods,
            Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = basis.Model.Assemblies.Append(new AssemblyDef { Name = "ReturnFacts.dll", AssemblyName = "ReturnFacts", Version = new(1, 0), Culture = "", PublicKey = [], Types = [owner] }).ToArray() };
        var entries = methods.Select((method, i) => new CodeEntry((ulong)(16 + i * 4), EntryKind.Method, MethodRef.Open(method), i, null)).ToArray();
        var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = entries,
            ByAddress = entries.ToDictionary(e => e.Address, e => ImmutableArray.Create(e)), Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(),
            MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
        var functions = new Dictionary<ulong, NativeFunction>();
        for (int i = 0; i < names.Length; i++)
        {
            var t = new TermTable(); var block = new BlockIdentity();
            var f = new FunctionBuilder(t, block, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var statements = new List<Statement>(); Term returned;
            if (names[i] is "Leaf" or "BadLeaf" or "LiftFailure") returned = t.Constant(names[i] == "BadLeaf" ? 256 : 1, 64);
            else
            {
                int target = names[i] switch { "Tail" or "OtherSlot" or "Indirect" or "Inverted" => 0, "BadTail" => 2, "CycleA" => 5, _ => 4 };
                var id = new CallIdentity(); returned = t.Atom(new ResultAtom(id), 64); var other = t.Atom(new ResultAtom(id, 1), 64);
                statements.Add(new Call(id, names[i] == "Indirect" ? new ComputedTarget(t.Constant(entries[target].Address, 64)) : new ImageFunction(entries[target].Address),
                    [new(new(SlotKind.Integer), t.Constant(0, 64))], [new(new(SlotKind.Integer), returned), new(new(SlotKind.Integer, 1), other)]));
                if (names[i] == "OtherSlot") returned = other;
                if (names[i] == "Masked") returned = t.Concat(t.Slice(returned, 0, 1), t.Constant(0, 63));
                if (names[i] == "Inverted") returned = t.Concat(t.Apply(new CoreOperator(CoreOperation.Xor), 32,
                    t.Slice(returned, 0, 32), t.Constant(1, 32)), t.Undefined(32));
            }
            f.Blocks.Add(new(block, [], [.. statements], new Return([new(new(SlotKind.Integer), returned)])));
            functions.Add(entries[i].Address, f.Freeze());
        }
        bool[] expected = [true, true, false, false, false, false, true, false, false, true, false];
        foreach (bool reverse in new[] { false, true })
        {
            var facts = new GlobalFacts(new EmptyImage(), model, map, basis.Spec, "arm64");
            var frontend = new ReturnFactsFrontend(functions, entries[^1].Address);
            var source = ReturnValueBitsAssembly.Get(facts, frontend);
            foreach (int i in reverse ? Enumerable.Range(0, names.Length).Reverse() : Enumerable.Range(0, names.Length))
            {
                var result = source.Get(entries[i].Address, MethodRef.Open(methods[i]));
                checks.True(result.IsSuccess == expected[i], names[i] + " 跨方法返回事实与请求次序 " + reverse + "：" + result.Why);
            }
            Parallel.For(0, 16, _ => source.Get(entries[1].Address, MethodRef.Open(methods[1])));
            foreach (int i in Enumerable.Range(0, names.Length))
            {
                source.Get(entries[i].Address, MethodRef.Open(methods[i]));
                checks.True(frontend.Lifts.GetValueOrDefault(entries[i].Address) == 1, names[i] + " 成功、失败、循环均复用原生见证");
            }
        }
    }
    private sealed class ReturnFactsFrontend(IReadOnlyDictionary<ulong, NativeFunction> functions, ulong missing) : IMethodStage<CodeEntry, NativeFunction>
    {
        public Dictionary<ulong, int> Lifts { get; } = [];
        public string Name => "前端";
        public StageResult<NativeFunction> Run(CodeEntry input, MethodContext context)
        {
            Lifts[input.Address] = Lifts.GetValueOrDefault(input.Address) + 1;
            return input.Address == missing ? new Missing<NativeFunction>(new(Name, input.Address, "提升", new("test.return-bits", "提升失败")))
                : new Completed<NativeFunction>(functions[input.Address]);
        }
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
    private sealed class StallingRecovery(bool cooperative, ManualResetEventSlim release) : IMethodStage<NativeFunction, ManagedBody>
    {
        public string Name => "恢复";
        public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context)
        {
            if (context.Method.Index == 0)
                return new Completed<ManagedBody>(new(MethodRef.Open(context.Method), [new(0, [new ManagedReturn(0, new ConstantValue(7, context.Method.ReturnType, 32))])]));
            while (!release.Wait(10))
                if (cooperative) WorkAbort.Check();
            return new Missing<ManagedBody>(new(Name, context.Entry.Address, "测试步骤", new("test.missing", "测试洞")));
        }
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
