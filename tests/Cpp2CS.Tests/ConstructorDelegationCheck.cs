using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class ConstructorDelegationCheck
{
    public static readonly List<string> Events = [];
    public static float Next;
    public static bool FailRange;
    public static object?[] Arguments = [];

    public class BaseProbe
    {
        public BaseProbe(object presenter, object model, object context)
        {
            Events.Add("base");
            Arguments = [presenter, model, context];
        }
    }

    public static float Range(float minimum, float maximum)
    {
        Require(minimum == 5f && maximum == 8f, "真实随机范围参数");
        Events.Add("range");
        if (FailRange) throw new InvalidOperationException("range probe");
        return Next;
    }

    public static void Run(RecoverySession session)
    {
        var method = session.Model.Code[0x5631084].Single().Method;
        Require(method.ToString() == "Sekai.Mysekai.IdleLowerState..ctor" && method.Method.Parameters.Count == 3, "真实构造函数身份");
        var raw = BodyRecovery.Recover(session, session.Analyze(method, 0x5631084), recoverConstructors: false).Body
            ?? throw new InvalidOperationException("真实构造函数原始方法体未恢复");
        var recovered = session.Constructors.Recover(raw);
        Require(recovered.Constructors is [{ Address: 0x56310e4 }], "完整后缀对应四参数构造函数");
        var proof = recovered.Constructors[0];
        var store = raw.Blocks.SelectMany(b => b.Statements).OfType<ManagedStore>().Single();
        var field = ((FieldValue)store.Target).Field;
        ManagedBody ReplaceStore(ManagedValue value) => raw with
        {
            Blocks = raw.Blocks.Select(b => b with { Statements = b.Statements.Select(s => s == store ? store with { Value = value } : s).ToArray() }).ToArray(),
        };
        Require(ConstructorDelegations.Match(session.Types, ReplaceStore(store.Target), proof) is null, "不能把基类调用之后的字段读取提前为构造参数");
        var extra = proof.Body with { Blocks = proof.Body.Blocks.Select(b => b with
        {
            Statements = b.Statements.SelectMany(s => s is ManagedStore ? new[] { s, s } : new[] { s }).ToArray(),
        }).ToArray() };
        Require(ConstructorDelegations.Match(session.Types, raw, proof with { Body = extra }) is null, "拒绝含额外字段写入的候选");
        var wrong = proof.Body with { Blocks = proof.Body.Blocks.Reverse().ToArray() };
        if (wrong.Blocks.Count > 1) Require(ConstructorDelegations.Match(session.Types, raw, proof with { Body = wrong }) is null, "不能忽略入口与控制流");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeConstructorDelegationChecks", new Version(1, 0)), "NativeConstructorDelegationChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Idle", TypeAttributes.Public, module.ImportReference(typeof(BaseProbe))); module.Types.Add(host);
        var actualField = new FieldDefinition("Duration", FieldAttributes.Public | FieldAttributes.InitOnly, module.TypeSystem.Single); host.Fields.Add(actualField);
        var methods = new Dictionary<MethodRef, MethodDefinition>();
        foreach (var body in new[] { recovered, proof.Body })
        {
            var actual = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
            foreach (var parameter in body.Method.Method.Parameters)
                actual.Parameters.Add(new ParameterDefinition(parameter.Type == session.Types.Single ? module.TypeSystem.Single : module.TypeSystem.Object));
            host.Methods.Add(actual); methods.Add(body.Method, actual);
        }
        var baseCall = proof.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Invocation.Method;
        var range = raw.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single(c => c.Invocation.Method.Method.Name == "Range").Invocation.Method;
        TypeReference Reference(TypeRef type) => type == method.DeclaringType ? host : type == method.Method.Owner.BaseType ? module.ImportReference(typeof(BaseProbe))
            : type == session.Types.Single ? module.TypeSystem.Single : ManagedTypes.IsReferenceType(type) ? module.TypeSystem.Object
            : module.ImportReference(System.Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var emitter = new BodyEmitter(session.Types, Reference, f => f == field ? actualField : throw new NotSupportedException(f.ToString()),
            m => methods.TryGetValue(m, out var actual) ? actual : m == baseCall ? module.ImportReference(typeof(BaseProbe).GetConstructors().Single())
                : m == range ? module.ImportReference(typeof(ConstructorDelegationCheck).GetMethod(nameof(Range))) : throw new NotSupportedException(m.ToString()));
        foreach (var body in new[] { proof.Body, recovered })
        {
            var problem = emitter.Emit(body, methods[body.Method]); Require(problem is null, problem ?? "构造委托输出");
        }
        using var bytes = new MemoryStream(); assembly.Write(bytes);
        Execute(SR.Assembly.Load(bytes.ToArray()).GetType("Checks.Idle", true)!);

        var directory = Path.Combine("artifacts", "constructor-source-check", Guid.NewGuid().ToString("N")); Directory.CreateDirectory(directory);
        var path = Path.Combine(directory, assembly.Name.Name + ".dll"); assembly.Write(path);
        var sources = Decompilation.Decompile(path, Path.GetDirectoryName(typeof(ConstructorDelegationCheck).Assembly.Location)!, _ => true,
            assemblyAttributes: false, recoveringBodies: true);
        File.WriteAllText(Path.Combine(directory, "Recovered.cs"), string.Join(Environment.NewLine, sources.Select(s => s.Source)));
        Require(sources.Single().Source.Contains(": this("), "源码保留构造委托");
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Append(typeof(ConstructorDelegationCheck).Assembly.Location).Distinct().Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("RecompiledConstructorChecks", sources.Select(s => CSharpSyntaxTree.ParseText(s.Source)), references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        using var compiled = new MemoryStream(); var result = compilation.Emit(compiled);
        Require(result.Success, string.Join(Environment.NewLine, result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        Execute(SR.Assembly.Load(compiled.ToArray()).GetType("Checks.Idle", true)!);
        Console.WriteLine("真实构造函数 0x5631084 → 0x56310e4 的 CIL 与 C# 重新编译执行通过：参数、位型、求值顺序和异常顺序；随机与基类使用记录宿主");
    }

    private static void Execute(Type runtime)
    {
        object[] arguments = [new object(), new object(), new object()];
        foreach (var bits in new uint[] { 0, 0x80000000, 0x40a00000, 0x41000000, 0x7fc01234 })
        {
            Events.Clear(); Next = BitConverter.Int32BitsToSingle(unchecked((int)bits)); FailRange = false;
            var instance = Activator.CreateInstance(runtime, arguments)!;
            Require(Events.SequenceEqual(new[] { "range", "base" }) && Arguments.SequenceEqual(arguments), "先计算随机参数，再调用基类，且参数身份不变");
            Require(unchecked((uint)BitConverter.SingleToInt32Bits((float)runtime.GetField("Duration")!.GetValue(instance)!)) == bits, "时长字段位型不变");
        }
        Events.Clear(); FailRange = true;
        var failed = Task.Run(() => Activator.CreateInstance(runtime, arguments));
        ((IAsyncResult)failed).AsyncWaitHandle.WaitOne();
        Require(failed.IsFaulted && failed.Exception!.Flatten().InnerExceptions.Single() is SR.TargetInvocationException { InnerException: InvalidOperationException }
            && Events.SequenceEqual(new[] { "range" }), "参数计算抛异常时不得调用基类");
        FailRange = false;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
