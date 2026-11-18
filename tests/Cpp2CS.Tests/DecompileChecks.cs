using System.Collections.Immutable;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Output;
using Cpp2CS.Tests.Execution;
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
        ConstrainedReceiver(checks, output);
        return checks.Finish("C# 导出快速检查");
    }

    private static void ConstrainedReceiver(Assertions checks, string output)
    {
        using var fixture = new CompiledSource("""
            public static class Sample
            {
                public interface IChange { int Change(ref int delta); int Level { get; set; } }
                public struct Counter : IChange
                {
                    public int Value;
                    int IChange.Change(ref int delta) { Value += delta; return ++delta; }
                    public int Change(ref int delta) { Value = -1; return -1; }
                    int IChange.Level { get => ++Value; set => Value = value + 1; }
                }
                static int Change<T>(ref T value, ref int delta) where T : IChange => value.Change(ref delta);
                static int Read<T>(ref T value) where T : IChange => value.Level;
                static void Write<T>(ref T value, int level) where T : IChange => value.Level = level;
                public static int Run()
                {
                    var cells = new Counter[2];
                    int index = 0, delta = 7;
                    int result = Change(ref cells[index++], ref delta);
                    Write(ref cells[1], 3);
                    int level = Read(ref cells[1]);
                    ((IChange)cells[0]).Change(ref delta);
                    return cells[0].Value * 100000 + result * 10000 + delta * 1000 + level * 100 + cells[1].Value * 10 + index;
                }
            }
            """);
        var run = fixture.Method("Sample", "Run");
        var il = run.Body.GetILProcessor();
        // 将封闭泛型转发内联，保留 Roslyn 产生的实参求值、取址与独立装箱。
        foreach (var call in run.Body.Instructions.Where(i => i.Operand is GenericInstanceMethod).ToArray())
        {
            var closed = (GenericInstanceMethod)call.Operand;
            var target = closed.Resolve().Body.Instructions.Single(i => i.OpCode.Code == Code.Callvirt);
            il.InsertBefore(call, il.Create(OpCodes.Constrained, closed.GenericArguments.Single()));
            call.OpCode = OpCodes.Callvirt;
            call.Operand = target.Operand;
        }
        var path = Path.Combine(output, "Constrained.local.dll");
        fixture.Module.Write(path);
        // 依赖从真实框架程序集解析。
        var framework = Path.GetDirectoryName(typeof(object).Assembly.Location)!;
        var source = Decompilation.Decompile(path, framework, t => t.FullName == "Sample", false).Single();
        using var exported = new CompiledSource(source.Source);
        static int Execute(ModuleDefinition module)
        {
            using var image = new MemoryStream();
            module.Write(image);
            return (int)R.Assembly.Load(image.ToArray()).GetType("Sample")!.GetMethod("Run")!.Invoke(null, null)!;
        }
        const int expected = 789551;
        var original = Execute(fixture.Module);
        var actual = Execute(exported.Module);
        checks.True(original == expected && actual == expected,
            $"具体结构体接口调用保持槽位、原址、ref 实参、求值次数与独立装箱，预期 {expected}，CIL {original}，导出 {actual}");
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
