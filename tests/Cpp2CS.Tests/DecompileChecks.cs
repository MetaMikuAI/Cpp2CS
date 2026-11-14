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

internal static class DecompileChecks
{
    public const string Command = "decompile";
    private const int DeepLevels = 6000;
    public static int Run()
    {
        var checks = new Assertions();
        string[] names = ["Object", "Exception", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference", "Void"];
        var types = names.Select((n, i) => new TypeDef { Index = i, Assembly = "mscorlib.dll", Namespace = "System", Name = n,
            Token = (uint)(0x02000001 + i), Attributes = R.TypeAttributes.Public, IsValueType = n is not ("Object" or "Exception" or "String"), IsEnum = false }).ToArray();
        var owner = types[0];
        var methods = new[] { "Present", "Missing", "Deep" }.Select((n, i) => new MethodDef { Index = i, Owner = owner, Name = n,
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
        var output = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", "decompile-check.local.output");
        var session = new RecoverySession(frontend: new FakeFrontend(), recovery: new FakeRecovery());
        var request = new RecoveryRequest("", "", output) { Jobs = 2, Source = true };
        var report = session.Run(facts, request);
        checks.True(report.Summary.Complete == 2 && report.Summary.Holes == 1, "混合结果不互相阻断");
        checks.True(report.Methods[1].Hole is { Layer: "恢复", Reason.Code: "test.missing" }, "洞保留层和结构化原因");
        using var module = ModuleDefinition.ReadModule(Path.Combine(output, "mscorlib.dll"));
        var written = module.Types.Single(t => t.Name == "Object").Methods;
        checks.True(written[0].Body.Instructions.Any(i => i.OpCode.Code == Code.Ldc_I4 && (int)i.Operand == 7 || i.OpCode.Code == Code.Ldc_I4_7)
            && written[0].Body.Instructions.Last().OpCode.Code == Code.Ret, "完整体写出返回常量");
        checks.True(written[1].Body.Instructions.Last().OpCode.Code == Code.Throw, "洞保留占位体");
        var source = File.ReadAllText(Path.Combine(output, "src", "mscorlib.dll_System.Object.cs"));
        checks.True(source.Contains("return 7;", StringComparison.Ordinal), "完整方法导出返回语句");
        checks.True(source.Contains("throw Unrecovered.Fail(20uL);", StringComparison.Ordinal), "洞导出地址标注与占位体");
        checks.True(report.Source is { Files: > 0, Types.Length: 0, Methods.Length: 0 }, "导出无失败");
        checks.True(source.Split(" + ").Length > DeepLevels, "嵌套很深的表达式导出成源码（反编译器按深度递归，不能栈溢出）");
        return checks.Finish("C# 导出快速检查");
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
        public StageResult<ManagedBody> Run(NativeFunction input, MethodContext context) => context.Method.Index switch
        {
            0 => new Completed<ManagedBody>(new(MethodRef.Open(context.Method), [new(0, [new ManagedReturn(0, new ConstantValue(7, context.Method.ReturnType, 32))])])),
            2 => new Completed<ManagedBody>(new(MethodRef.Open(context.Method), [new(0, [new ManagedReturn(0, Deep(context.Method.ReturnType))])])),
            _ => new Missing<ManagedBody>(new(Name, context.Entry.Address, "测试步骤", new("test.missing", "测试洞"))),
        };
        private static ManagedValue Deep(TypeRef type)
        {
            ManagedValue value = new ConstantValue(3, type, 32);
            for (int i = 0; i < DeepLevels; i++) value = new BinaryValue(BinaryOperator.Add, value, new ConstantValue(3, type, 32), type, 32);
            return value;
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
