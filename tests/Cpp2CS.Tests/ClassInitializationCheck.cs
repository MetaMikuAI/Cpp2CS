using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Runtime;
using Cpp2CS.Ssa;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class ClassInitializationCheck
{
    public static readonly List<int> Events = [];
    public static void Mark(int value) => Events.Add(value);

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        Wrapper(session.Machine.Convention);
        Require(session.Resolver.Resolve(0x44106e8) is HelperCallee { Helper: { Kind: HelperKind.ClassInit, ReturnedArgument: null } },
            "真实快速路径包装的慢路径尾调用 void 初始化函数，不能承诺返回原类型指针");
        var types = session.Types;
        Require(RuntimeClassLayout.For(session.Model) is { StaticFields: 0xb8, ConstructorFinished: 0xe0 }, "目标版本的类布局");
        var slot = new Variable(Storage.Gpr(8), 1);
        var klass = new Variable(Storage.Gpr(9), 1);
        var flag = new Variable(Storage.Gpr(10), 1);
        var initialize = new Call(0x1010, CallKind.Direct, Expr.C(0x49c871c, 64))
        {
            Sources = [Storage.Gpr(0)], Arguments = [new Use(klass, 64)], Results = [], Defines = [],
        };
        MachineFunction Function(int offset = 0xe0, bool otherType = false, bool extraStore = false, int conditionWidth = 32)
        {
            var entry = new Block(0x1000) { Statements =
            [
                new Define(0x1000, slot, new Load(Expr.C(0xb6e7cc0, 64), 64)),
                new Define(0x1004, klass, new Load(new Use(slot, 64), 64)),
                new Define(0x1008, flag, new Load(new Binary(BinOp.Add, new Use(klass, 64), Expr.C((ulong)offset, 64), 64), 32)),
                new Branch(0x100c, new Compare(Cond.Ne, new Use(flag, conditionWidth), Expr.C(0, conditionWidth)), 0x1020, 0x1010),
            ] };
            var call = otherType ? initialize with { Arguments = [new Load(new Load(Expr.C(0xb737490, 64), 64), 64)] } : initialize;
            var slow = new Block(0x1010) { Statements = [call, new Jump(0x1014, 0x1020)] };
            if (extraStore) slow.Statements.Insert(0, new Store(0x100f, Expr.C(0x8000, 64), Expr.C(1, 32)));
            var join = new Block(0x1020) { Statements = [new Return(0x1020)] };
            entry.Successors.AddRange([join, slow]); join.Predecessors.Add(entry); slow.Predecessors.Add(entry);
            slow.Successors.Add(join); join.Predecessors.Add(slow);
            return new() { Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1024, BoundaryEvidence.SymbolCandidate, "合成检查"), Blocks = [entry, slow, join] };
        }
        foreach (var negative in new[] { Function(offset: 0xe4), Function(otherType: true), Function(extraStore: true), Function(conditionWidth: 8) })
        {
            ClassInitialization.NormalizeGuards(session.Resolver, negative);
            Require(negative.EntryBlock.Statements.Last() is Branch, "其他偏移、不同类型、窄比较及额外写入不能当作类初始化快速路径");
        }
        var function = Function();
        new Prepare(session.Resolver, session.Calls, session.Machine.Convention).Run(function);
        Require(function.EntryBlock.Statements.Last() is Jump && function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Count() == 1,
            "移除快速路径后必须保留类初始化调用");
        Require(SsaCheck.Verify(function, Dominators.Compute(function)).Count == 0, "修改前驱与后继后 SSA 仍成立");
        var owner = new TypeDef { Index = -1, Assembly = "ClassInitChecks.dll", Namespace = "Checks", Name = "Harness", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        MethodRef Method(string name, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = types.Void,
            Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
        }, [], []);
        var method = Method("Ready");
        var recovered = BodyRecovery.Recover(session, new(method, null, function, null, []));
        Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
        var initializer = recovered.Body!.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single();
        Require(initializer.Invocation.Method.Method.Name == "RunClassConstructor" && initializer.Invocation.Arguments is [TypeHandleValue], "使用元数据中的 CLR 初始化接口");
        var target = ((TypeHandleValue)initializer.Invocation.Arguments[0]).TargetType;
        var unknown = Function();
        unknown.Blocks[1].Statements[0] = initialize with { Arguments = [Expr.C(0, 64)] };
        Require(BodyRecovery.Recover(session, new(method, null, unknown, null, [])).Problems.Any(p => p.Reason == "类初始化的类型信息尚未确定"),
            "未知类型的类初始化不得被删除");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ClassInitChecks", new Version(1, 0)), "ClassInitChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(host);
        var mark = module.ImportReference(typeof(ClassInitializationCheck).GetMethod(nameof(Mark)));
        TypeDefinition Probe(string name, int marker, bool fail)
        {
            var type = new TypeDefinition("Checks", name, TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(type);
            var ctor = new MethodDefinition(".cctor", MethodAttributes.Private | MethodAttributes.Static | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName,
                module.TypeSystem.Void); type.Methods.Add(ctor);
            var il = ctor.Body.GetILProcessor(); il.Emit(OpCodes.Ldc_I4, marker); il.Emit(OpCodes.Call, mark);
            if (fail)
            {
                il.Emit(OpCodes.Newobj, module.ImportReference(typeof(InvalidOperationException).GetConstructor(Type.EmptyTypes))); il.Emit(OpCodes.Throw);
            }
            else il.Emit(OpCodes.Ret);
            return type;
        }
        var markerMethod = Method("Mark", types.Int32);
        ManagedCall Marker(int value) => new(0x2000, new(markerMethod, null, [new ConstantValue((ulong)value, types.Int32, 32)]), null, false);
        foreach (var (name, probe) in new[] { ("Ready", Probe("ReadyProbe", 10, false)), ("Fault", Probe("FaultProbe", 20, true)) })
        {
            var body = recovered.Body with { Method = Method(name), Blocks = recovered.Body.Blocks.Select((b, index) => b with
            {
                Statements = (index == 0 ? new ManagedStatement[] { Marker(1) } : []).Concat(b.Statements.SelectMany(s =>
                    s is ManagedReturn ? new ManagedStatement[] { Marker(2), s } : [s])).ToArray(),
            }).ToArray() };
            var actual = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Void); host.Methods.Add(actual);
            TypeReference Reference(TypeRef type) => type == target ? probe : type == types.Corlib("System.RuntimeTypeHandle") ? module.ImportReference(typeof(RuntimeTypeHandle))
                : type == types.Int32 ? module.TypeSystem.Int32 : ManagedTypes.IsVoid(type) ? module.TypeSystem.Void : throw new NotSupportedException(type.ToString());
            var emitter = new BodyEmitter(types, Reference, f => throw new NotSupportedException(f.ToString()),
                m => m == markerMethod ? mark : m == initializer.Invocation.Method
                    ? module.ImportReference(typeof(System.Runtime.CompilerServices.RuntimeHelpers).GetMethod("RunClassConstructor", [typeof(RuntimeTypeHandle)]))
                    : throw new NotSupportedException(m.ToString()));
            var problem = emitter.Emit(body, actual); Require(problem is null, problem ?? "类初始化输出");
        }
        using var bytes = new MemoryStream(); assembly.Write(bytes);
        Execute(SR.Assembly.Load(bytes.ToArray()).GetType("Checks.Harness", true)!);
        var directory = Path.Combine("artifacts", "class-init-source-check", Guid.NewGuid().ToString("N")); Directory.CreateDirectory(directory);
        var path = Path.Combine(directory, "ClassInitChecks.dll"); assembly.Write(path);
        var sources = Decompilation.Decompile(path, Path.GetDirectoryName(typeof(ClassInitializationCheck).Assembly.Location)!, _ => true, false, recoveringBodies: true);
        foreach (var source in sources) File.WriteAllText(Path.Combine(directory, source.TypeName + ".cs"), source.Source);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Append(typeof(ClassInitializationCheck).Assembly.Location).Distinct().Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("RecompiledClassInitChecks", sources.Select(s => CSharpSyntaxTree.ParseText(s.Source)), references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        using var compiled = new MemoryStream(); var result = compilation.Emit(compiled);
        Require(result.Success, string.Join(Environment.NewLine, result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        Execute(SR.Assembly.Load(compiled.ToArray()).GetType("Checks.Harness", true)!);
        Console.WriteLine("类初始化检查通过：包装函数与快速路径证明、未知类型及副作用拒绝、CIL/C# 执行顺序、仅执行一次及异常缓存");
        return 0;
    }

    private static void Execute(Type runtime)
    {
        Events.Clear(); runtime.GetMethod("Ready")!.Invoke(null, []);
        Require(Events.SequenceEqual(new[] { 1, 10, 2 }), "类初始化保留在两个可见副作用之间");
        Events.Clear(); runtime.GetMethod("Ready")!.Invoke(null, []);
        Require(Events.SequenceEqual(new[] { 1, 2 }), "类型构造函数仅执行一次");
        for (var i = 0; i < 2; i++)
        {
            Events.Clear();
            var task = Task.Run(() => runtime.GetMethod("Fault")!.Invoke(null, []));
            ((IAsyncResult)task).AsyncWaitHandle.WaitOne();
            Require(task.IsFaulted && task.Exception!.Flatten().InnerExceptions.Single() is SR.TargetInvocationException
                { InnerException: TypeInitializationException { InnerException: InvalidOperationException } }, "类初始化异常不可吞掉或改写");
            Require(Events.SequenceEqual(i == 0 ? new[] { 1, 20 } : new[] { 1 }), "失败结果缓存，后续语句不执行");
        }
    }

    private static void Wrapper(CallingConvention convention)
    {
        var argument = new Use(new Variable(convention.IntegerArguments[0], 0), 64);
        var flag = new Variable(Storage.Gpr(8), 1);
        MachineFunction Function(bool wrongArgument = false, bool extraStore = false, int offset = 0xe0, bool inverted = false, int width = 32)
        {
            var entry = new Block(0x1000) { Statements =
            [
                new Store(0x1000, new FrameAddress(-8), new Use(new Variable(Storage.Gpr(30), 0), 64)),
                new Define(0x1004, flag, new Ir.Convert(ConvKind.ZeroExtend, new Load(new Binary(BinOp.Add, argument, Expr.C((ulong)offset, 64), 64), 32), 64)),
                new Branch(0x1008, new Compare(inverted ? Cond.Eq : Cond.Ne, new Use(flag, width), Expr.C(0, width)), 0x1020, 0x1010),
            ] };
            var initialize = new Block(0x1010) { Statements =
            [
                new Call(0x1010, CallKind.Direct, Expr.C(0x4000, 64))
                {
                    Sources = [convention.IntegerArguments[0]], Arguments = [wrongArgument ? Expr.C(0x8000, 64) : argument],
                },
                new Jump(0x1014, 0x1020),
            ] };
            var exit = new Block(0x1020) { Statements = [new Return(0x1020) { Value = argument }] };
            if (extraStore) exit.Statements.Insert(0, new Store(0x101c, argument, Expr.C(1, 32)));
            entry.Successors.AddRange([exit, initialize]); exit.Predecessors.Add(entry); initialize.Predecessors.Add(entry);
            initialize.Successors.Add(exit); exit.Predecessors.Add(initialize);
            return new() { Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1024, BoundaryEvidence.SymbolCandidate, "合成包装"), Blocks = [entry, initialize, exit] };
        }
        bool Match(MachineFunction f) => ClassInitializationWrapper.Matches(f, convention, 0xe0, target => target == 0x4000);
        Require(Match(Function()), "相同类型的已完成分支、初始化调用和私有栈保存构成包装");
        var tail = Function();
        tail.Blocks[1].Statements = [((Call)tail.Blocks[1].Statements[0]) with { Kind = CallKind.Tail }];
        tail.Blocks[1].Successors.Clear(); tail.Blocks[2].Predecessors.Remove(tail.Blocks[1]);
        Require(Match(tail), "快速路径返回、慢路径尾调用的包装仍执行同一类初始化");
        foreach (var negative in new[] { Function(wrongArgument: true), Function(extraStore: true), Function(offset: 0xe4), Function(inverted: true), Function(width: 8) })
            Require(!Match(negative), "返回原参数并不足以证明包装：错误类型、额外副作用、错误标志及倒置分支必须拒绝");
        var unknownLoad = Function();
        unknownLoad.EntryBlock.Statements.Insert(0, new Define(0x0ffc, new Variable(Storage.Gpr(9), 1), new Load(Expr.C(0x8000, 64), 64)));
        Require(!Match(unknownLoad), "不删除额外未知读取");
        var loop = Function();
        loop.Blocks[1].Statements[^1] = new Jump(0x1014, 0x1000);
        loop.Blocks[1].Successors[0] = loop.EntryBlock;
        Require(!Match(loop), "包装不能包含回边");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
