using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Runtime;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class BoxingCheck
{
    public struct Pair { public int Number; public object? Reference; }
    public static readonly List<object?> Logged = [];
    public static bool ThrowOnLog;
    public static void LogError(object? value)
    {
        Logged.Add(value);
        if (ThrowOnLog) throw new InvalidOperationException("日志宿主故障");
    }

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        Require(session.Resolver.Resolve(0x49c8724) is HelperCallee { Helper.Kind: HelperKind.Box }, "真实装箱辅助函数身份");
        var enumType = (DefinitionRef)session.Model.UsageAt(session.Model.Image.RelocatedPointer(0xb737490)!.Value)!.Value;
        Require(enumType.Definition.IsEnum && types.Size(enumType) == 4, "装箱的真实枚举元数据");
        var nullable = new DefinitionRef(types.CorlibDefinition("System.Nullable")!, [types.Int32]);
        var owner = new TypeDef { Index = -1, Assembly = "BoxingChecks.dll", Namespace = "Checks", Name = "Harness", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var pairOwner = new TypeDef { Index = -2, Assembly = "BoxingChecks.dll", Namespace = "Checks", Name = "Pair", Token = 0,
            Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false,
            Size = 16, PackingSize = 0, ClassSizeIsDefault = true };
        pairOwner.Fields = [new() { Index = -1, Owner = pairOwner, Name = "Number", Type = types.Int32, Offset = 0, Attributes = SR.FieldAttributes.Public },
            new() { Index = -2, Owner = pairOwner, Name = "Reference", Type = types.Object, Offset = 8, Attributes = SR.FieldAttributes.Public }];
        var pair = new DefinitionRef(pairOwner, []);
        MethodRef Method(string name, TypeRef result, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result,
            Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
        }, [], []);
        PreparedMethod Prepare(MethodRef method, params Stmt[] statements) => new(method, session.Abi.ClassifyReturn(method.Method.ReturnType, out _),
            Graph(new Block(0x1000) { Statements = [.. statements] }), null, []);
        Use Input(int index, int width = 64) => new(new Variable(Storage.Gpr(index), 0), width);
        var boxed = new Variable(Storage.Gpr(0), 1);
        var frame = new FrameAddress(-16);
        var call = new Call(0x1004, CallKind.Direct, Expr.C(0x49c8724, 64))
        {
            Sources = [Storage.Gpr(0), Storage.Gpr(1)],
            Arguments = [new Load(new Load(Expr.C(0xb737490, 64), 64), 64), frame],
            Results = [Storage.Gpr(0)], Defines = [boxed],
        };
        var returned = new Return(0x100c) { Value = new Use(boxed, 64) };
        var copy = Prepare(Method("Copy", types.Object, enumType), new Store(0x1000, frame, Input(0, 32)), call,
            new Store(0x1008, frame, Expr.C(99, 32)), returned);
        var values = new ValueRecovery(session, copy);
        Require(values.Stack.Problems.Count == 0 && values.HelperValue(call, out _) is BoxValue { Operand.Type: var boxedType } && boxedType == enumType,
            "按元数据推断栈值，保留枚举而非底层整数类型");
        Require(BodyRecovery.Recover(session, Prepare(Method("MissingWrite", types.Object), call, returned)).Body is null, "未初始化栈值不能装箱");
        Require(BodyRecovery.Recover(session, Prepare(Method("Partial", types.Object), new Store(0x1000, frame, Expr.C(1, 16)), call, returned)).Body is null,
            "部分写入不能由 CLR 局部变量的默认零填补");
        Require(values.HelperValue(call with { Arguments = [Expr.C(0, 64), frame] }, out _) is null, "未知 TypeInfo 不能装箱");
        Require(values.HelperValue(call with { Sources = [Storage.Gpr(0)], Arguments = [call.Arguments[0]] }, out _) is null, "缺少值地址必须拒绝");
        var mismatch = Prepare(Method("Mismatch", types.Object, new ByRefRef(types.Int32)), call with { Arguments = [call.Arguments[0], Input(0)] }, returned);
        Require(BodyRecovery.Recover(session, mismatch).Body is null, "同宽整数不能冒充已声明的枚举引用");
        var branch = Graph(new Block(0x1000) { Statements = [new Branch(0x1000, Expr.C(1, 1), 0x2000, 0x3000)] },
            new Block(0x2000) { Statements = [new Store(0x2000, frame, Expr.C(1, 32)), new Jump(0x2004, 0x4000)] },
            new Block(0x3000) { Statements = [new Jump(0x3000, 0x4000)] },
            new Block(0x4000) { Statements = [call with { Address = 0x4000 }, returned with { Address = 0x4004 }] });
        Require(BodyRecovery.Recover(session, copy with { Function = branch }).Body is null, "只有一条路径初始化的装箱必须拒绝");
        Require(types.CanBox(nullable) && types.CanBox(pair) && types.CanBox(types.IntPtr), "nullable、含引用结构体和 IntPtr 是值类型");
        Require(!types.CanBox(types.Object) && !types.CanBox(types.Void) && !types.CanBox(new PointerRef(types.Int32))
            && !types.CanBox(new DefinitionRef(nullable.Definition, [])), "引用、void、裸指针和开放泛型不是已知可装箱值");
        Require(!types.CanBox(types.Corlib("System.TypedReference")), "TypedReference 不能进入对象堆");
        var bufferOwner = new TypeDef { Index = -3, Assembly = "BoxingChecks.dll", Namespace = "Checks", Name = "Buffer", Token = 0,
            Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false,
            Size = 24, PackingSize = 0, ClassSizeIsDefault = true };
        var bufferType = new DefinitionRef(bufferOwner, []);
        var output = Input(8);
        var writes = new[] { 0, 8, 16 }.Select(offset => (Stmt)new Store((ulong)(0x1000 + offset),
            offset == 0 ? output : new Binary(BinOp.Add, output, Expr.C((ulong)offset, 64), 64), Expr.C(0, 64))).ToArray();
        var readBuffer = call with { Address = 0x1020, Arguments = [call.Arguments[0], output] };
        var returnBuffer = new Return(0x1030) { Buffer = output };
        var initialized = Prepare(Method("ReadBuffer", bufferType), [.. writes, readBuffer, returnBuffer]);
        var early = Prepare(Method("EarlyBuffer", bufferType), [readBuffer, .. writes, returnBuffer]);
        Require(new ValueRecovery(session, initialized).BufferProblems.Count == 0
            && new ValueRecovery(session, early).BufferProblems.Any(p => p.Reason.Contains("读取前未完整写入")),
            "装箱读取返回缓冲区时也必须先初始化，后续写入不能补偿早读");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("BoxingChecks", new Version(1, 0)), "BoxingChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(host);
        var enumHost = new TypeDefinition("Checks", "PathKind", TypeAttributes.Public | TypeAttributes.Sealed, module.ImportReference(typeof(Enum)));
        enumHost.Fields.Add(new FieldDefinition("value__", FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName, module.TypeSystem.Int32));
        module.Types.Add(enumHost);
        TypeReference Reference(TypeRef type) => type == enumType ? enumHost : type == nullable ? module.ImportReference(typeof(int?))
            : type == pair ? module.ImportReference(typeof(Pair)) : type is ByRefRef r ? new ByReferenceType(Reference(r.Element))
            : type == types.Object ? module.TypeSystem.Object : type == types.String ? module.TypeSystem.String
            : module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var emitter = new BodyEmitter(types, Reference, f => throw new NotSupportedException(f.ToString()), m => m.Method.Name == "RunClassConstructor"
            ? module.ImportReference(typeof(System.Runtime.CompilerServices.RuntimeHelpers).GetMethod("RunClassConstructor", [typeof(RuntimeTypeHandle)]))
            : throw new NotSupportedException(m.ToString()));
        MethodDefinition EmitBody(ManagedBody body)
        {
            var actual = new MethodDefinition(body.Method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(body.Method.Method.ReturnType));
            foreach (var parameter in body.Method.Method.Parameters) actual.Parameters.Add(new ParameterDefinition(Reference(parameter.Type)));
            var problem = emitter.Emit(body, actual); Require(problem is null, problem ?? actual.Name); host.Methods.Add(actual); return actual;
        }
        MethodDefinition Emit(PreparedMethod prepared)
        {
            var result = BodyRecovery.Recover(session, prepared); Require(result.Body is not null, string.Join("; ", result.Problems));
            return EmitBody(result.Body!);
        }
        Emit(copy);
        Emit(Prepare(Method("Tail", types.Object, enumType), new Store(0x1000, frame, Input(0, 32)), call with { Kind = CallKind.Tail, Results = [], Defines = [] }));
        Emit(Prepare(Method("ByReference", types.Object, new ByRefRef(enumType)), call with { Arguments = [call.Arguments[0], Input(0)] }, returned));
        var unused = Emit(Prepare(Method("Unused", types.Void, enumType), new Store(0x1000, frame, Input(0, 32)), call, new Return(0x1008)));
        Require(unused.Body.Instructions.Count(i => i.OpCode == OpCodes.Box) == 1, "未使用的装箱结果仍在原调用位置输出");
        var referenceCall = call with { Arguments = [new Load(new Load(Expr.C(0xb6e83e0, 64), 64), 64), frame] };
        Emit(Prepare(Method("Reference", types.String, types.String), new Store(0x1000, frame, Input(0)), referenceCall,
            new Store(0x1008, frame, Expr.C(0, 64)), returned));
        foreach (var (name, type) in new (string, TypeRef)[] { ("Int", types.Int32), ("Bool", types.Boolean), ("Float", types.Single),
            ("Double", types.Double), ("Nullable", nullable), ("Pair", pair), ("PointerValue", types.IntPtr) })
        {
            var initialization = Boxing.Initialization(types, type, out var problem); Require(problem is null, problem ?? name);
            EmitBody(new(Method(name, types.Object, type), [new(0x1000, [new ManagedReturn(0x1000,
                new BoxValue(new ArgumentValue(0, "value", type, types.Size(type) * 8), types.Object, initialization))]) ]));
        }
        var bad = new ManagedBody(Method("BadBox", types.Object, types.String), [new(0x1000, [new ManagedReturn(0x1000,
            new BoxValue(new ArgumentValue(0, "value", types.String, 64), types.Object))])]);
        Require(emitter.Emit(bad, new MethodDefinition("BadBox", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Object)) is not null,
            "输出层不能接受伪造的引用类型装箱");
        AddGrid(session, assembly);
        BoxingInitializationCheck.Add(types, assembly);
        var directory = Path.Combine("artifacts", "boxing-source-check", Guid.NewGuid().ToString("N")); Directory.CreateDirectory(directory);
        var path = Path.Combine(directory, assembly.Name.Name + ".dll"); assembly.Write(path);
        CheckSources(path, directory);
        Console.WriteLine("装箱检查通过：元数据类型、完整初始化、值副本、对象身份、nullable、含引用结构体和浮点位型；CIL 与 C# 往返执行");
        Console.WriteLine("真实 Grid2DPosition.ToString 0xa460d10：两次有符号字节装箱，CIL/C# 各穷举 65536 组坐标，格式化使用 CLR");
        Console.WriteLine("装箱初始化检查通过：一次性、失败缓存、初始化后复制，以及 nullable 空值跳过和有值判定顺序");
        RuntimeValueCheck.Native(session);
        return 0;
    }

    public static int Saved(string path)
    {
        var directory = Path.Combine("artifacts", "boxing-source-check", Guid.NewGuid().ToString("N")); Directory.CreateDirectory(directory);
        CheckSources(path, directory);
        Console.WriteLine("已保存装箱检查程序集的 CIL/C# 往返执行通过");
        return 0;
    }

    private static void CheckSources(string path, string directory)
    {
        Execute(SR.Assembly.Load(File.ReadAllBytes(path)));
        var sources = Decompilation.Decompile(path, Path.GetDirectoryName(typeof(BoxingCheck).Assembly.Location)!, _ => true, false, recoveringBodies: true);
        foreach (var source in sources) File.WriteAllText(Path.Combine(directory, source.TypeName + ".cs"), source.Source);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Append(typeof(BoxingCheck).Assembly.Location).Distinct().Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("RecompiledBoxingChecks", sources.Select(s => CSharpSyntaxTree.ParseText(s.Source)), references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        using var compiled = new MemoryStream(); var emitted = compilation.Emit(compiled);
        Require(emitted.Success, string.Join(Environment.NewLine, emitted.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        Execute(SR.Assembly.Load(compiled.ToArray()));
    }

    private static void Execute(SR.Assembly assembly)
    {
        BoxingInitializationCheck.Execute(assembly);
        var host = assembly.GetType("Checks.Harness", true)!;
        object? Invoke(string name, params object?[] args) => host.GetMethod(name)!.Invoke(null, args);
        var enumType = assembly.GetType("Checks.PathKind", true)!;
        foreach (var value in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
            foreach (var name in new[] { "Copy", "Tail", "ByReference" })
            {
                var input = Enum.ToObject(enumType, value); var boxed = Invoke(name, input);
                Require(boxed?.GetType() == enumType && System.Convert.ToInt32(boxed) == value, "装箱复制原值且保持枚举身份");
                Require(!ReferenceEquals(boxed, input) && !ReferenceEquals(boxed, Invoke(name, input)), "装箱不是输入对象别名，每次调用产生独立对象");
            }
        var shared = new string(['s', 'a', 'm', 'e']);
        Require(ReferenceEquals(Invoke("Reference", shared), shared) && Invoke("Reference", [null]) is null, "引用类型辅助分支保持原对象身份和空值");
        foreach (var value in new[] { int.MinValue, 0, int.MaxValue })
            Require(Invoke("Int", value) is int actual && actual == value && Invoke("Nullable", value) is int n && n == value, "整数和有值 nullable 装箱为内部整数");
        Require(Invoke("Nullable", [null]) is null && Invoke("Bool", true) is true && Invoke("Bool", false) is false, "nullable 空值与布尔值");
        foreach (var bits in new uint[] { 0, 1, 0x80000000, 0x7f800000, 0x7fc12345 })
            Require(unchecked((uint)BitConverter.SingleToInt32Bits((float)Invoke("Float", BitConverter.Int32BitsToSingle(unchecked((int)bits)))!)) == bits,
                "单精度负零、无穷与 NaN 位型保持");
        foreach (var bits in new ulong[] { 0, 1, 0x8000000000000000, 0x7ff0000000000000, 0x7ff8123456789abc })
            Require(unchecked((ulong)BitConverter.DoubleToInt64Bits((double)Invoke("Double", BitConverter.Int64BitsToDouble(unchecked((long)bits)))!)) == bits,
                "双精度负零、无穷与 NaN 位型保持");
        var reference = new object(); var pair = new Pair { Number = 17, Reference = reference }; var copied = (Pair)Invoke("Pair", pair)!;
        pair.Number = 99; pair.Reference = null;
        Require(copied.Number == 17 && ReferenceEquals(copied.Reference, reference), "含引用结构体按值复制，内部对象引用保持身份");
        Require(Invoke("PointerValue", new IntPtr(-17)) is IntPtr pointer && pointer == new IntPtr(-17), "IntPtr 是可装箱的托管值，区别于裸指针");
        var grid = assembly.GetType("Checks.Grid", true)!;
        var xField = grid.GetField("X")!; var yField = grid.GetField("Y")!; var text = grid.GetMethod("ToString", Type.EmptyTypes)!;
        var position = Activator.CreateInstance(grid)!;
        for (var x = -128; x <= 127; x++)
            for (var y = -128; y <= 127; y++)
            {
                xField.SetValue(position, (sbyte)x); yField.SetValue(position, (sbyte)y);
                Require((string)text.Invoke(position, [])! == $"({x},{y})", "原生无符号读取后按元数据装箱为 sbyte，保留负数格式化");
            }
    }

    private static void AddGrid(RecoverySession session, AssemblyDefinition assembly)
    {
        var source = session.Model.Code[0xa460d10].Single().Method;
        Require(source.ToString() == "Sekai.Mysekai.HUD.Grid2DPosition.ToString", "真实窄整数方法身份");
        var types = session.Types; var module = assembly.MainModule;
        var owner = source.DeclaringType;
        var host = new TypeDefinition("Checks", "Grid", TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.ImportReference(typeof(ValueType))); module.Types.Add(host);
        var fields = new Dictionary<FieldDef, FieldReference>();
        foreach (var field in source.Method.Owner.Fields.Where(f => !f.IsStatic))
        {
            Require(field.Type == types.SByte && field.Offset == (field.Name == "X" ? 0 : 1), "两个字节字段的真实布局");
            var actual = new FieldDefinition(field.Name, FieldAttributes.Public | FieldAttributes.InitOnly, module.TypeSystem.SByte);
            host.Fields.Add(actual); fields.Add(field, actual);
        }
        TypeReference Reference(TypeRef type) => type == owner ? host : type is ByRefRef r ? new ByReferenceType(Reference(r.Element))
            : type == types.Object ? module.TypeSystem.Object : type == types.String ? module.TypeSystem.String
            : module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var emitter = new BodyEmitter(types, Reference, f => fields[f.Field], m => m.Method.Address == 0xa1c4500
            && m.Method.Owner.FullName == "System.String" && m.Method.Name == "Format"
            ? module.ImportReference(typeof(string).GetMethod(nameof(string.Format), [typeof(string), typeof(object), typeof(object)]))
            : throw new NotSupportedException(m.ToString()));
        var method = new MethodDefinition("ToString", MethodAttributes.Public | MethodAttributes.Virtual | MethodAttributes.HideBySig, module.TypeSystem.String);
        var recovered = BodyRecovery.Recover(session, session.Analyze(source, source.Method.Address));
        Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
        var problem = emitter.Emit(recovered.Body!, method); Require(problem is null, problem ?? source.ToString()); host.Methods.Add(method);
    }

    private static MachineFunction Graph(params Block[] blocks)
    {
        foreach (var block in blocks)
            foreach (var target in block.Statements.LastOrDefault() switch { Branch b => new[] { b.Target, b.Fallthrough }, Jump j => [j.Target], _ => Array.Empty<ulong>() })
            {
                var next = blocks.Single(b => b.Start == target); block.Successors.Add(next); next.Predecessors.Add(block);
            }
        var function = new MachineFunction { Entry = blocks[0].Start, Range = new FunctionRange(0x1000, 0x5000, BoundaryEvidence.SymbolCandidate, "装箱检查"), Blocks = [.. blocks] };
        function.Renumber(); return function;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
