using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

/// <summary>实际加载生成的 CIL 执行合成输入；验证输出器语义，不替代真实游戏方法验收。</summary>
internal static class BodyEmissionCheck
{
    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("RecoveredBodyChecks", new Version(1, 0)), "RecoveredBodyChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var harness = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(harness);
        var owner = new TypeDef { Index = -1, Assembly = "Checks.dll", Namespace = "Checks", Name = "Harness", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var field = new FieldDef { Index = -1, Owner = owner, Name = "Value", Type = types.Int32, Offset = 16, Token = 0, Attributes = SR.FieldAttributes.Public };
        owner.Fields = [field];
        var actualField = new FieldDefinition("Value", FieldAttributes.Public, module.TypeSystem.Int32);
        harness.Fields.Add(actualField);
        var owners = new HashSet<TypeDef> { owner };
        var fields = new Dictionary<FieldDef, FieldDefinition> { [field] = actualField };
        var methods = new Dictionary<MethodDef, MethodDefinition>();
        TypeReference Reference(TypeRef type)
        {
            if (type is DefinitionRef d && owners.Contains(d.Definition)) return harness;
            if (type is ByRefRef b) return new ByReferenceType(Reference(b.Element));
            var name = ManagedTypes.PrimitiveName(type) ?? throw new InvalidOperationException(type.ToString());
            return module.ImportReference(Type.GetType("System." + name, throwOnError: true)!);
        }
        var emitter = new BodyEmitter(types, Reference, f => fields[f.Field], m => methods[m.Method]);
        MethodRef Method(string name, TypeRef result, bool instance, params TypeRef[] parameters)
        {
            var definition = new MethodDef { Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1,
                Attributes = SR.MethodAttributes.Public | (instance ? 0 : SR.MethodAttributes.Static), ImplAttributes = SR.MethodImplAttributes.IL,
                ReturnType = result, Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, SR.ParameterAttributes.None, null, false)).ToArray() };
            var actual = new MethodDefinition(name, MethodAttributes.Public | (instance ? 0 : MethodAttributes.Static), Reference(result));
            foreach (var parameter in parameters) actual.Parameters.Add(new ParameterDefinition(Reference(parameter)));
            harness.Methods.Add(actual); methods.Add(definition, actual);
            return new(definition, [], []);
        }
        void Emit(ManagedBody recovered)
        {
            var problem = emitter.Emit(recovered, methods[recovered.Method.Method]);
            Require(problem is null, problem ?? "");
        }
        ArgumentValue Arg(TypeRef type, int index = 0) => new(index, "p" + index, type, types.Size(type) * 8);
        ConstantValue C(ulong value, TypeRef type) => new(value, type, types.Size(type) * 8);
        LocalValue L(int index, TypeRef type) => new(new Variable(Storage.Gpr(index), 1), type, types.Size(type) * 8);
        void Expression(string name, TypeRef result, ManagedValue expression, params TypeRef[] parameters) =>
            Emit(new(Method(name, result, false, parameters), [new ManagedBlock(0x1000, [new ManagedReturn(0x1000, expression)])]));

        Expression("Zero", types.UInt64, new ConversionValue(ConvKind.ZeroExtend, Arg(types.Int32), types.UInt64, 64), types.Int32);
        Expression("Sign", types.Int64, new ConversionValue(ConvKind.SignExtend, Arg(types.UInt32), types.Int64, 64), types.UInt32);
        Expression("ByteAdd", types.Byte, new BinaryValue(BinOp.Add, Arg(types.Byte), C(250, types.Byte), types.Byte, 8), types.Byte);
        Expression("Shift", types.Int32, new BinaryValue(BinOp.AShr, Arg(types.UInt32), Arg(types.UInt32, 1), types.Int32, 32), types.UInt32, types.UInt32);
        Expression("SignedLess", types.Boolean, new ComparisonValue(Cond.Slt, Arg(types.UInt32), C(0, types.UInt32), types.Boolean), types.UInt32);
        Expression("FloatBits", types.Single, new ConversionValue(ConvKind.Bitcast, Arg(types.UInt32), types.Single, 32), types.UInt32);
        Expression("IntegerBits", types.UInt32, new ConversionValue(ConvKind.Bitcast, Arg(types.Single), types.UInt32, 32), types.Single);
        uint[] constant32 = [0, 1, 0x80000000, 0x3f800000, 0x7f800000, 0x7f801234, 0x7fc01234, 0xffc05678];
        ulong[] constant64 = [0, 1, 0x8000000000000000, 0x3ff0000000000000, 0x7ff0000000000000, 0x7ff0000000001234, 0x7ff8000000001234, 0xfff8000000005678];
        foreach (var bits in constant32)
        {
            Expression("ConstantFloat" + bits, types.Single, new ConversionValue(ConvKind.Bitcast, C(bits, types.UInt32), types.Single, 32));
            Expression("ConstantUInt" + bits, types.UInt32, new ConversionValue(ConvKind.Bitcast, C(bits, types.Single), types.UInt32, 32));
        }
        foreach (var bits in constant64)
        {
            Expression("ConstantDouble" + bits, types.Double, new ConversionValue(ConvKind.Bitcast, C(bits, types.UInt64), types.Double, 64));
            Expression("ConstantULong" + bits, types.UInt64, new ConversionValue(ConvKind.Bitcast, C(bits, types.Double), types.UInt64, 64));
        }
        foreach (var condition in new[] { Cond.FEq, Cond.FUne, Cond.FLt, Cond.FLe, Cond.FGt, Cond.FGe, Cond.FUlt, Cond.FUle, Cond.FUgt, Cond.FUge })
            Expression(condition.ToString(), types.Boolean, new ComparisonValue(condition, Arg(types.Single), Arg(types.Single, 1), types.Boolean), types.Single, types.Single);

        // 两条回边赋值交叉引用旧值，必须先读完再写，且按真正走过的边执行。
        var x = L(2, types.UInt64); var y = L(3, types.UInt64); var n = L(4, types.UInt64);
        Emit(new(Method("SwapLoop", types.UInt64, false, types.UInt64),
        [
            new ManagedBlock(0x1000, [new ManagedJump(0x1000, new ManagedEdge(0x2000, [new(x, C(1, types.UInt64)), new(y, C(2, types.UInt64)), new(n, Arg(types.UInt64))]))]),
            new ManagedBlock(0x2000, [new ManagedBranch(0x2000, new ComparisonValue(Cond.Ne, n, C(0, types.UInt64), types.Boolean),
                new ManagedEdge(0x3000, []), new ManagedEdge(0x4000, []))]),
            new ManagedBlock(0x3000, [new ManagedJump(0x3000, new ManagedEdge(0x2000,
                [new(x, y), new(y, x), new(n, new BinaryValue(BinOp.Sub, n, C(1, types.UInt64), types.UInt64, 64))]))]),
            new ManagedBlock(0x4000, [new ManagedReturn(0x4000, new BinaryValue(BinOp.Add,
                new BinaryValue(BinOp.Mul, x, C(10, types.UInt64), types.UInt64, 64), y, types.UInt64, 64))]),
        ]));

        // 从机器 SSA 走完整恢复路径；字段写入不得改变此前读取的值。
        var fieldMethod = Method("ReadThenWrite", types.Int32, true);
        var address = new Binary(BinOp.Add, new Use(new Variable(Storage.Gpr(0), 0), 64), Expr.C(16, 64), 64);
        var saved = new Variable(Storage.Gpr(2), 1);
        var function = new MachineFunction { Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1010, BoundaryEvidence.SymbolCandidate, "合成检查"),
            Blocks = [new Block(0x1000) { Statements = [new Define(0x1000, saved, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, new Load(address, 32), 64)),
                new Store(0x1004, address, Expr.C(9, 32)), new Return(0x1008) { Value = new Use(saved, 32) }] }] };
        var recovered = BodyRecovery.Recover(session, new(fieldMethod, session.Abi.ClassifyReturn(types.Int32, out _), function, null, []));
        Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
        Emit(recovered.Body!);
        var caller = Method("Call", types.Int32, true);
        Emit(new(caller, [new ManagedBlock(0x1000, [new ManagedCall(0x1000,
            new ManagedInvocation(fieldMethod, new ArgumentValue(-1, "this", caller.DeclaringType, 64), []), L(5, types.Int32), false),
            new ManagedReturn(0x1004, L(5, types.Int32))])]));

        var unsupported = Method("Unsupported", types.Int32, false, types.Int32);
        var original = methods[unsupported.Method].Body;
        Require(emitter.Emit(new(unsupported, [new ManagedBlock(0x1000, [new ManagedReturn(0x1000,
            new BinaryValue(BinOp.SDiv, Arg(types.Int32), C(0, types.Int32), types.Int32, 32))])]), methods[unsupported.Method]) is not null
            && ReferenceEquals(original, methods[unsupported.Method].Body), "不支持的除法不得写成 CLR 除法或替换原方法体");
        var il = original.GetILProcessor(); il.Emit(OpCodes.Ldc_I4_0); il.Emit(OpCodes.Ret);

        var constructor = Method(".ctor", types.Void, true);
        methods[constructor.Method].Attributes |= MethodAttributes.SpecialName | MethodAttributes.RTSpecialName;
        Require(emitter.Emit(new(constructor, [new ManagedBlock(0x1000, [new ManagedReturn(0x1000, null)])]), methods[constructor.Method]) is not null,
            "缺少基类初始化证据的构造函数不得输出裸 ret");
        harness.Methods.Remove(methods[constructor.Method]);

        var privateField = session.Model.Fields.First(f => !f.IsStatic && f.Type == types.Int32
            && (f.Attributes & SR.FieldAttributes.FieldAccessMask) == SR.FieldAttributes.Private);
        var inaccessible = Method("PrivateRead", types.Int32, true);
        var inaccessibleBody = new ManagedBody(inaccessible, [new ManagedBlock(0x1000, [new ManagedReturn(0x1000,
            new FieldValue(new ArgumentValue(-1, "this", new DefinitionRef(privateField.Owner, []), 64),
                new FieldRef(privateField, new DefinitionRef(privateField.Owner, [])), types.Int32, 32))])]);
        Require(emitter.Emit(inaccessibleBody, methods[inaccessible.Method])?.StartsWith("内联字段访问权限尚未恢复") == true,
            "跨类内联的私有字段不能输出为直接访问");
        harness.Methods.Remove(methods[inaccessible.Method]);

        // 固定真实二进制 case：ldr/str w0/w1,[x0,#0x14]; ret。仅替换测试宿主，不替换恢复的语句。
        foreach (var (va, name, result, parameters) in new[]
        {
            (0x55d261cUL, "NativeGet", (TypeRef)types.Int32, Array.Empty<TypeRef>()),
            (0x55d2624UL, "NativeSet", (TypeRef)types.Void, new TypeRef[] { types.Int32 }),
        })
        {
            var nativeMethod = session.Model.Code[va].Single().Method;
            Require(nativeMethod.Method.Owner.FullName == "Sekai.Mysekai.DebugCharacterSpawnEventData", "真实 case 的元数据身份");
            var actual = Method(name, result, true, parameters);
            methods.Add(nativeMethod.Method, methods[actual.Method]);
            owners.Add(nativeMethod.Method.Owner);
            var nativeField = nativeMethod.Method.Owner.Fields.Single(f => f.Offset == 0x14 && f.Type == types.Int32);
            fields[nativeField] = actualField;
            var nativeBody = BodyRecovery.Recover(session, session.Analyze(nativeMethod, va));
            Require(nativeBody.Body is not null, string.Join("; ", nativeBody.Problems));
            Emit(nativeBody.Body!);
        }

        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
        object Run(string name, params object[] args) => runtime.GetMethod(name)!.Invoke(null, args)!;
        foreach (var input in new[] { 0, 1, -1, int.MinValue, int.MaxValue })
        {
            Require((ulong)Run("Zero", input) == unchecked((uint)input), "32 位零扩展");
            Require((long)Run("Sign", unchecked((uint)input)) == input, "32 位符号扩展");
            Require((bool)Run("SignedLess", unchecked((uint)input)) == (input < 0), "有符号比较");
            foreach (var shift in new uint[] { 0, 1, 31, 32, 63, 255 })
                Require((int)Run("Shift", unchecked((uint)input), shift) == (input >> (int)shift), "算术右移与位宽取模");
        }
        for (var i = 0; i < 256; i++) Require((byte)Run("ByteAdd", (byte)i) == unchecked((byte)(i + 250)), "窄整数溢出截断");
        foreach (var bits in new uint[] { 0, 0x80000000, 0x3f800000, 0x7f800000, 0x7fc01234 })
        {
            var floating = (float)Run("FloatBits", bits);
            Require(unchecked((uint)BitConverter.SingleToInt32Bits(floating)) == bits, "整数到浮点位型保留");
            Require((uint)Run("IntegerBits", floating) == bits, "浮点到整数位型保留");
        }
        void CheckConstants(Type actual)
        {
            object Constant(string name) => actual.GetMethod(name)!.Invoke(null, [])!;
            foreach (var bits in constant32)
            {
                Require(unchecked((uint)BitConverter.SingleToInt32Bits((float)Constant("ConstantFloat" + bits))) == bits, "常量整数到单精度位型保留 " + bits);
                Require((uint)Constant("ConstantUInt" + bits) == bits, "常量单精度到整数位型保留 " + bits);
            }
            foreach (var bits in constant64)
            {
                Require(unchecked((ulong)BitConverter.DoubleToInt64Bits((double)Constant("ConstantDouble" + bits))) == bits, "常量整数到双精度位型保留 " + bits);
                Require((ulong)Constant("ConstantULong" + bits) == bits, "常量双精度到整数位型保留 " + bits);
            }
        }
        CheckConstants(runtime);
        foreach (var left in new[] { -1f, 0f, 1f, float.NaN })
        foreach (var right in new[] { -1f, 0f, 1f, float.NaN })
        {
            var unordered = float.IsNaN(left) || float.IsNaN(right);
            foreach (var (condition, expected) in new[] { (Cond.FEq, left == right), (Cond.FUne, left != right), (Cond.FLt, left < right),
                (Cond.FLe, left <= right), (Cond.FGt, left > right), (Cond.FGe, left >= right), (Cond.FUlt, unordered || left < right),
                (Cond.FUle, unordered || left <= right), (Cond.FUgt, unordered || left > right), (Cond.FUge, unordered || left >= right) })
                Require((bool)Run(condition.ToString(), left, right) == expected, "浮点比较 " + condition);
        }
        for (ulong count = 0; count < 10; count++) Require((ulong)Run("SwapLoop", count) == (count % 2 == 0 ? 12UL : 21UL), "循环边同时赋值");
        var instance = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(runtime);
        runtime.GetField("Value")!.SetValue(instance, 41);
        Require((int)runtime.GetMethod("ReadThenWrite")!.Invoke(instance, [])! == 41 && (int)runtime.GetField("Value")!.GetValue(instance)! == 9, "字段读取时机");
        runtime.GetField("Value")!.SetValue(instance, 57);
        Require((int)runtime.GetMethod("Call")!.Invoke(instance, [])! == 57, "托管调用结果");
        foreach (var value in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            runtime.GetMethod("NativeSet")!.Invoke(instance, [value]);
            Require((int)runtime.GetMethod("NativeGet")!.Invoke(instance, [])! == value && (int)runtime.GetField("Value")!.GetValue(instance)! == value,
                "真实 getter/setter 的字段读写");
        }
        Console.WriteLine("CIL 执行检查通过：宽度、符号、移位、浮点位型/NaN、循环边赋值、字段顺序和调用");
        Console.WriteLine("真实 case 0x55d261c/0x55d2624 的恢复方法体在替代宿主中执行通过；未验证游戏运行时");
        CheckConstants(SourceRoundTrip(assembly));
        Console.WriteLine("常量位型的 C# 重新编译执行通过：单精度、双精度、负零、极小值与 NaN 载荷");
        return 0;
    }

    private static Type SourceRoundTrip(AssemblyDefinition assembly)
    {
        var directory = Path.Combine("artifacts", "body-source-check", Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        var path = Path.Combine(directory, assembly.Name.Name + ".dll");
        assembly.Write(path);
        var sources = Decompilation.Decompile(path, directory, _ => true, assemblyAttributes: false, recoveringBodies: true);
        File.WriteAllText(Path.Combine(directory, "Recovered.cs"), string.Join(Environment.NewLine, sources.Select(s => s.Source)));
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Select(p => MetadataReference.CreateFromFile(p));
        var compilation = CSharpCompilation.Create("RecompiledBodyChecks", sources.Select(s => CSharpSyntaxTree.ParseText(s.Source)), references,
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        using var stream = new MemoryStream();
        var result = compilation.Emit(stream);
        Require(result.Success, string.Join(Environment.NewLine, result.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
        return SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
