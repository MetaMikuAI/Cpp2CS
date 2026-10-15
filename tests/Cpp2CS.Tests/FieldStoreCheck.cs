using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;
using Convert = System.Convert;

namespace Cpp2CS.Tests;

public static class FieldStoreCheck
{
    public sealed class Flags { public bool First; public bool Second; public ushort Guard; }
    public sealed class Numbers { public byte Low; public byte High; public short Signed; public float Real; public int Guard; }
    public struct Pair { public short Left; public short Right; }
    public struct Nested { public Pair Pair; public short Next; public short Guard; }
    public delegate void NestedWriter(ref Nested value, uint bits);

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        Synthetic(session);
        Native(session);
        return 0;
    }

    private static void Synthetic(RecoverySession session)
    {
        var types = session.Types;
        TypeDef Type(string name, bool value = false, int size = 0) => new()
        {
            Index = -1, Assembly = "FieldStoreChecks.dll", Namespace = "Checks", Name = name, Token = 0,
            Attributes = SR.TypeAttributes.Public | (value ? SR.TypeAttributes.SequentialLayout : 0),
            IsValueType = value, IsEnum = false, Size = size, ClassSizeIsDefault = true, BaseType = value ? null : types.Object,
        };
        FieldDef Field(TypeDef owner, string name, TypeRef type, int offset) => new()
        { Index = -1, Owner = owner, Name = name, Type = type, Offset = offset, Attributes = SR.FieldAttributes.Public };
        var flags = Type("Flags"); var flagsType = new DefinitionRef(flags, []);
        flags.Fields = [Field(flags, "First", types.Boolean, 16), Field(flags, "Second", types.Boolean, 17), Field(flags, "Guard", types.UInt16, 18)];
        var numbers = Type("Numbers"); var numbersType = new DefinitionRef(numbers, []);
        numbers.Fields = [Field(numbers, "Low", types.Byte, 16), Field(numbers, "High", types.Byte, 17), Field(numbers, "Signed", types.Int16, 18),
            Field(numbers, "Real", types.Single, 20), Field(numbers, "Guard", types.Int32, 24)];
        var pair = Type("Pair", true, 4); var pairType = new DefinitionRef(pair, []);
        pair.Fields = [Field(pair, "Left", types.Int16, 0), Field(pair, "Right", types.Int16, 2)];
        var nested = Type("Nested", true, 8); var nestedType = new DefinitionRef(nested, []);
        nested.Fields = [Field(nested, "Pair", pairType, 0), Field(nested, "Next", types.Int16, 4), Field(nested, "Guard", types.Int16, 6)];
        var host = Type("Harness");
        MethodRef Method(string name, TypeRef receiver, TypeRef input) => new(new MethodDef
        {
            Index = -1, Owner = host, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = types.Void,
            Parameters = [new("value", receiver, 0, null, false), new("bits", input, 0, null, false)],
        }, [], []);
        var self = new Use(new Variable(Storage.Gpr(0), 0), 64);
        Expr At(int offset) => new Binary(BinOp.Add, self, Expr.C((ulong)offset, 64), 64);
        ManagedBody? Recover(MethodRef method, int offset, Expr value)
        {
            var function = EdgeConstantsCheck.Graph(new Block(0x1000)
            { Statements = [new Store(0x1000, At(offset), value), new Return(0x1004)] });
            return BodyRecovery.Recover(session, new(method, null, function, null, [])).Body;
        }
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("FieldStoreChecks", new Version(1, 0)), "FieldStoreChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var harness = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(harness);
        var hosts = new Dictionary<TypeRef, Type> { [flagsType] = typeof(Flags), [numbersType] = typeof(Numbers), [pairType] = typeof(Pair), [nestedType] = typeof(Nested) };
        TypeReference Reference(TypeRef type) => type is ByRefRef byRef ? new ByReferenceType(Reference(byRef.Element))
            : hosts.TryGetValue(type, out var runtime) ? module.ImportReference(runtime)
            : module.ImportReference(System.Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var fields = new[] { flags, numbers, pair, nested }.SelectMany(t => t.Fields)
            .ToDictionary(f => f, f => module.ImportReference(hosts[new DefinitionRef(f.Owner, [])].GetField(f.Name)));
        var emitter = new BodyEmitter(types, Reference, f => fields[f.Field], m => throw new NotSupportedException(m.ToString()));
        void Emit(MethodRef method, int offset, Expr value)
        {
            var body = Recover(method, offset, value); Require(body is not null, method.ToString());
            var target = new MethodDefinition(method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Void);
            foreach (var p in method.Method.Parameters) target.Parameters.Add(new ParameterDefinition(Reference(p.Type)));
            harness.Methods.Add(target); var problem = emitter.Emit(body!, target); Require(problem is null, problem ?? method.ToString());
        }
        foreach (var bits in new ulong[] { 0, 1, 0x100, 0x101 }) Emit(Method("Flags" + bits, flagsType, types.UInt16), 16, Expr.C(bits, 16));
        Emit(Method("Numbers", numbersType, types.UInt64), 16, new Use(new Variable(Storage.Gpr(1), 0), 64));
        Emit(Method("ConstantNaN", numbersType, types.UInt64), 16, Expr.C(0x7f8012348123fedc, 64));
        Emit(Method("ConstantNegativeZero", numbersType, types.UInt64), 16, Expr.C(0x8000000000000000, 64));
        Emit(Method("Alias", numbersType, types.UInt32), 16, new Binary(BinOp.Mul,
            new Ir.Convert(ConvKind.ZeroExtend, new Load(At(16), 8), 32), Expr.C(0x10002, 32), 32));
        Emit(Method("Nested", new ByRefRef(nestedType), types.UInt32), 2, new Use(new Variable(Storage.Gpr(1), 0), 32));
        Require(Recover(Method("BadBool", flagsType, types.UInt16), 16, Expr.C(0x201, 16)) is null, "非规范 bool 字节不能规范化后伪装为等价");
        Require(Recover(Method("UnknownBool", flagsType, types.UInt16), 16, new Use(new Variable(Storage.Gpr(1), 0), 16)) is null, "未知 bool 位型不拆分");
        Require(Recover(Method("Partial", numbersType, types.UInt16), 17, Expr.C(1, 16)) is null, "不能切开相邻的 short");
        foreach (var variant in new[] { "Gap", "Overlap", "Reference", "Unknown" })
        {
            var invalid = Type(variant); var invalidType = new DefinitionRef(invalid, []);
            invalid.Fields = variant switch
            {
                "Gap" => [Field(invalid, "a", types.Byte, 16), Field(invalid, "b", types.Int16, 18)],
                "Overlap" => [Field(invalid, "a", types.Int32, 16), Field(invalid, "b", types.Int16, 18)],
                "Reference" => [Field(invalid, "a", types.Object, 16), Field(invalid, "b", types.Byte, 24)],
                _ => [Field(invalid, "a", types.Int16, 16), Field(invalid, "b", types.Int16, 18), Field(invalid, "unknown", types.Byte, -1)],
            };
            Require(types.FieldSpan(invalidType, 16, 4) is null, variant + " 布局拒绝拆分");
        }
        using var stream = new MemoryStream(); assembly.Write(stream); Execute(SR.Assembly.Load(stream.ToArray()));
        ObjectAllocationCheck.Source(assembly, Execute, "field-store-source-check");
        Console.WriteLine("合并字段写入 CIL/C# 执行通过：bool、整数、浮点位型、源值与目标别名、嵌套结构体引用；填充、重叠、引用、未知偏移和部分标量拒绝");
    }

    private static void Execute(SR.Assembly assembly)
    {
        var host = assembly.GetType("Checks.Harness", true)!;
        var flags = new Flags { Guard = 0xbeef };
        foreach (var bits in new ulong[] { 0, 1, 0x100, 0x101 })
        {
            flags.First = (bits & 1) == 0; flags.Second = (bits & 0x100) == 0;
            host.GetMethod("Flags" + bits)!.Invoke(null, [flags, (ushort)0]);
            Require(flags.First == ((bits & 1) != 0) && flags.Second == ((bits & 0x100) != 0) && flags.Guard == 0xbeef, "布尔字段与范围外字段");
        }
        var numbers = new Numbers { Guard = 0x12345678 };
        var write = (Action<Numbers, ulong>)host.GetMethod("Numbers")!.CreateDelegate(typeof(Action<Numbers, ulong>));
        foreach (var high in new uint[] { 0, 1, 0x80000000, 0x7f800000, 0xff800000, 0x7fc01234, 0x7f801234 })
        foreach (var low in new uint[] { 0, 0x12345678, 0x8000ffff, uint.MaxValue })
        {
            write(numbers, ((ulong)high << 32) | low);
            Require(numbers.Low == (byte)low && numbers.High == (byte)(low >> 8) && numbers.Signed == unchecked((short)(low >> 16))
                && BitConverter.SingleToUInt32Bits(numbers.Real) == high && numbers.Guard == 0x12345678, "整数符号和浮点原始位型");
        }
        numbers.Low = 3; numbers.Real = 37;
        host.GetMethod("Alias")!.Invoke(null, [numbers, 0u]);
        Require(numbers.Low == 6 && numbers.High == 0 && numbers.Signed == 3 && numbers.Real == 37, "写前读取完整源值，不在后续字段写入时重新读取");
        host.GetMethod("ConstantNaN")!.Invoke(null, [numbers, 0UL]);
        Require(BitConverter.SingleToUInt32Bits(numbers.Real) == 0x7f801234 && numbers.Low == 0xdc && numbers.High == 0xfe
            && numbers.Signed == unchecked((short)0x8123), "合并常量中的 NaN 载荷和整数位型");
        host.GetMethod("ConstantNegativeZero")!.Invoke(null, [numbers, 0UL]);
        Require(BitConverter.SingleToUInt32Bits(numbers.Real) == 0x80000000 && numbers.Low == 0 && numbers.High == 0 && numbers.Signed == 0,
            "合并常量中的负零位型");
        var nested = new Nested { Pair = new() { Left = 123, Right = 5 }, Next = 6, Guard = 456 };
        var setNested = (NestedWriter)host.GetMethod("Nested")!.CreateDelegate(typeof(NestedWriter));
        setNested(ref nested, 0x8123fedc);
        Require(nested.Pair.Left == 123 && nested.Pair.Right == unchecked((short)0xfedc) && nested.Next == unchecked((short)0x8123) && nested.Guard == 456,
            "跨嵌套边界写入保持原结构体引用及范围外字段");
        var failed = Task.Run(() => write(null!, 0)); Task.WhenAny(failed).GetAwaiter().GetResult();
        Require(failed.Exception?.InnerException is NullReferenceException, "空接收者仍抛出异常");
    }

    private static void Native(RecoverySession session)
    {
        var types = session.Types;
        var names = new[] { "PassDepthSettings", "PassBlendSettings", "PassStencilSettings", "PassRenderingSettings", "MaterialRenderQueueSettings", "MaterialRenderingSettings" };
        var definitions = names.Select(name => session.Model.Types.Single(t => t.FullName == "Sekai.Mysekai.Data." + name)).ToArray();
        var methods = definitions.Select(t => new MethodRef(t.Methods.Single(m => m.Name == ".ctor"), [], [])).ToArray();
        var bodies = methods.Select(m => BodyRecovery.Recover(session, session.Analyze(m, m.Method.Address))).ToArray();
        for (var i = 0; i < bodies.Length; i++) Require(bodies[i].Body is not null, methods[i] + ": " + string.Join("; ", bodies[i].Problems));
        var depth = definitions[0];
        Require(depth.Fields.Single(f => f.Name == "isActiveZWrite") is { Offset: 16 } first && first.Type == types.Boolean
            && depth.Fields.Single(f => f.Name == "isActiveZTest") is { Offset: 17 } second && second.Type == types.Boolean, "原生 0x101 写入对应两个相邻 bool");
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeFieldStoreChecks", new Version(1, 0)), "NativeFieldStoreChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var hosts = definitions.ToDictionary(t => t, t => new TypeDefinition("Checks", t.Name, TypeAttributes.Public, module.TypeSystem.Object));
        foreach (var host in hosts.Values) module.Types.Add(host);
        var enums = new Dictionary<TypeRef, TypeDefinition>();
        TypeReference Reference(TypeRef type)
        {
            if (type == types.String) return module.TypeSystem.String;
            if (type == types.Object) return module.TypeSystem.Object;
            if (type is ArrayRef array) return new ArrayType(Reference(array.Element));
            if (type is DefinitionRef d && hosts.TryGetValue(d.Definition, out var host)) return host;
            if (type is DefinitionRef { Definition.IsEnum: true } enumeration)
            {
                if (enums.TryGetValue(type, out var cached)) return cached;
                var mapped = new TypeDefinition("Checks", enumeration.Definition.Name, TypeAttributes.Public | TypeAttributes.Sealed, module.ImportReference(typeof(Enum)));
                module.Types.Add(mapped); enums.Add(type, mapped);
                mapped.Fields.Add(new FieldDefinition("value__", FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName, Reference(types.Underlying(type))));
                foreach (var literal in enumeration.Definition.Fields.Where(f => f.IsStatic && (f.Attributes & SR.FieldAttributes.Literal) != 0))
                    mapped.Fields.Add(new FieldDefinition(literal.Name, FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault, mapped) { Constant = literal.Constant });
                return mapped;
            }
            if (ManagedTypes.PrimitiveName(type) is not { } primitive) throw new NotSupportedException(type.ToString());
            return module.ImportReference(System.Type.GetType("System." + primitive, true)!);
        }
        var fields = new Dictionary<FieldDef, FieldDefinition>();
        foreach (var definition in definitions)
        foreach (var field in definition.Fields.Where(f => !f.IsStatic))
        {
            var mapped = new FieldDefinition(field.Name, FieldAttributes.Public, Reference(field.Type));
            hosts[definition].Fields.Add(mapped); fields.Add(field, mapped);
        }
        var constructors = new Dictionary<MethodDef, MethodDefinition>();
        foreach (var native in methods)
        {
            var ctor = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
            hosts[native.Method.Owner].Methods.Add(ctor); constructors.Add(native.Method, ctor);
        }
        var emitter = new BodyEmitter(types, Reference, f => fields[f.Field], m => constructors.TryGetValue(m.Method, out var ctor) ? ctor
            : m.Method.Owner == types.Object.Definition && m.Method.Name == ".ctor" ? module.ImportReference(typeof(object).GetConstructor(System.Type.EmptyTypes))
            : throw new NotSupportedException(m.ToString()));
        foreach (var body in bodies.Select(b => b.Body!))
        {
            var problem = emitter.Emit(body, constructors[body.Method.Method]); Require(problem is null, problem ?? body.Method.ToString());
        }
        using var stream = new MemoryStream(); assembly.Write(stream); ExecuteNative(SR.Assembly.Load(stream.ToArray()), outer: true);
        // 外层数组字段初始化尚有 C# 构造语法诊断；内层完整构造链单独检查源码往返。
        module.Types.Remove(hosts[definitions[^1]]);
        ObjectAllocationCheck.Source(assembly, a => ExecuteNative(a, outer: false), "field-store-source-check");
        Console.WriteLine("真实 PassDepthSettings、PassRenderingSettings 及构造依赖的 CIL/C# 执行通过；MaterialRenderingSettings 完整构造 CIL 执行通过，外层 C# 尚未通过");
    }

    private static void ExecuteNative(SR.Assembly assembly, bool outer)
    {
        object New(string name) => Activator.CreateInstance(assembly.GetType("Checks." + name, true)!)!;
        object? Field(object value, string name) => value.GetType().GetField(name)!.GetValue(value);
        void Pass(object value)
        {
            Require(Field(value, "name") is "BasePass" && (int)Field(value, "colorMask")! == 15, "真实通道名称和颜色掩码初始化");
            var blend = Field(value, "blendSettings")!; var stencil = Field(value, "stencilSettings")!; var depth = Field(value, "depthSettings")!;
            Require(Convert.ToInt32(Field(blend, "srcBlend")) == 1 && Convert.ToInt32(Field(blend, "dstBlend")) == 0, "混合字段初始化");
            Require(stencil.GetType().GetFields().All(f => Convert.ToInt32(f.GetValue(stencil)) == 0), "模板字段清零");
            Require((bool)Field(depth, "isActiveZWrite")! && (bool)Field(depth, "isActiveZTest")! && (bool)Field(depth, "zWrite")!
                && Convert.ToInt32(Field(depth, "zTest")) == 4, "深度设置的 bool 和枚举初始化");
        }
        var first = New("PassRenderingSettings"); var second = New("PassRenderingSettings"); Pass(first); Pass(second);
        foreach (var name in new[] { "blendSettings", "stencilSettings", "depthSettings" })
            Require(!ReferenceEquals(Field(first, name), Field(second, name)), "重复构造不能共享可变字段对象");
        if (!outer) return;
        var settings = New("MaterialRenderingSettings");
        Require((int)Field(Field(settings, "renderQueueSettings")!, "renderQueue")! == 2000, "外层队列默认值");
        var array = (Array)Field(settings, "passRenderSettingsArray")!;
        Require(array.Length == 1, "外层数组长度"); Pass(array.GetValue(0)!);
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
