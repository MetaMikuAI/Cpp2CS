using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using Mono.Cecil.Cil;
using System.Text.Json;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class ConditionalValueCheck
{
    public struct FloatInt { public float Real; public int Signed; }
    public struct Vector { public int X; public int Y; public int Z; }
    public struct Position { public bool Invalid; public sbyte X; public sbyte Y; public sbyte Z; }
    public delegate Position Snapshot(ref Position source, Position replacement);
    private static (int X, int Y, int Z) observed;
    private static int calls;
    public static void Observe(int x, int y, int z) { observed = (x, y, z); calls++; }

    public static int Run(string binary, string metadata, string oracle)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        Synthetic(session);
        Native(session, oracle);
        return 0;
    }

    private static void Synthetic(RecoverySession session)
    {
        var types = session.Types;
        TypeDef Type(string name, bool value = false, int size = 0) => new()
        {
            Index = -1, Assembly = "ConditionalChecks.dll", Namespace = "Checks", Name = name, Token = 0,
            Attributes = SR.TypeAttributes.Public | (value ? SR.TypeAttributes.SequentialLayout : 0),
            IsValueType = value, IsEnum = false, Size = size, ClassSizeIsDefault = true, BaseType = value ? null : types.Object,
        };
        FieldDef Field(TypeDef owner, string name, TypeRef type, int offset, SR.FieldAttributes attributes = SR.FieldAttributes.Public) => new()
        { Index = -1, Owner = owner, Name = name, Type = type, Offset = offset, Attributes = attributes };
        var owner = Type("Harness"); var pair = Type("FloatInt", true, 8); var pairType = new DefinitionRef(pair, []);
        pair.Fields = [Field(pair, "Real", types.Single, 0), Field(pair, "Signed", types.Int32, 4)];
        var position = Type("Position", true, 4); var positionType = new DefinitionRef(position, []);
        position.Fields = new[] { "Invalid", "X", "Y", "Z" }.Select((name, i) => Field(position, name, i == 0 ? types.Boolean : types.SByte, i, SR.FieldAttributes.Private)).ToArray();
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("ConditionalChecks", new Version(1, 0)), "ConditionalChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var target = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(target);
        TypeReference Reference(TypeRef type) => type is ByRefRef reference ? new ByReferenceType(Reference(reference.Element))
            : type == pairType ? module.ImportReference(typeof(FloatInt)) : type == positionType ? module.ImportReference(typeof(Position))
            : type == types.String ? module.TypeSystem.String : type == types.Object ? module.TypeSystem.Object
            : module.ImportReference(System.Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var emitter = new BodyEmitter(types, Reference, f => module.ImportReference((f.Field.Owner == pair ? typeof(FloatInt) : typeof(Position)).GetField(f.Field.Name)), m => throw new NotSupportedException(m.ToString()));
        void Check(string name, TypeRef result, TypeRef[] parameters, Expr expression, bool accepted = true, params Stmt[] prefix)
        {
            var method = new MethodRef(new MethodDef
            {
                Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1,
                Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result,
                Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
            }, [], []);
            var function = EdgeConstantsCheck.Graph(new Block(0x1000) { Statements = [.. prefix, new Return(0x1010) { Value = expression }] });
            var body = BodyRecovery.Recover(session, new(method, session.Abi.ClassifyReturn(result, out _), function, null, []));
            Require((body.Body is not null) == accepted, name + ": " + string.Join("; ", body.Problems));
            if (body.Body is null) return;
            var mapped = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, Reference(result));
            foreach (var parameter in parameters) mapped.Parameters.Add(new ParameterDefinition(Reference(parameter)));
            target.Methods.Add(mapped); var problem = emitter.Emit(body.Body, mapped); Require(problem is null, problem ?? name);
        }
        Use Arg(int register, int width) => new(new Variable(Storage.Gpr(register), 0), width);
        Expr When(int register) => new Compare(Cond.Ne, Arg(register, 32), Expr.C(0, 32));
        Check("Signed", types.Int32, [types.Int32, types.UInt32, types.Int32], new Select(When(2), Arg(0, 32), Arg(1, 32), 32));
        Check("Wide", types.Int64, [types.Int64, types.UInt64, types.Int32], new Select(When(2), Arg(0, 64), Arg(1, 64), 64));
        Check("FloatingBits", types.Single, [types.Single, types.UInt32, types.Int32],
            new Select(When(1), new Use(new Variable(Storage.Vec(0), 0), 32), Arg(0, 32), 32));
        Check("Nullable", types.String, [types.String, types.Int32], new Select(When(1), Arg(0, 64), Expr.C(0, 64), 64));
        Check("Common", types.Object, [types.String, types.Object, types.Int32], new Select(When(2), Arg(0, 64), Arg(1, 64), 64));
        var zero = new Variable(Storage.Gpr(8), 1);
        Check("ZeroLocal", types.String, [types.String, types.Int32], new Select(When(1), new Use(zero, 64), Arg(0, 64), 64), true,
            new Define(0x1000, zero, Expr.C(0, 64)));
        Check("NonzeroReference", types.String, [types.String, types.Int32], new Select(When(1), Arg(0, 64), Expr.C(1, 64), 64), false);
        Check("UnknownReference", types.String, [types.String, types.Int32], new Select(When(1), Arg(0, 64), new Unknown("unknown", 64), 64), false);
        Check("WidthMismatch", types.UInt64, [types.Int32, types.UInt64, types.Int32], new Select(When(2), Arg(0, 32), Arg(1, 64), 64), false);
        Check("BadCondition", types.Int32, [types.Int32], new Select(Arg(0, 32), Expr.C(1, 32), Expr.C(0, 32), 32), false);
        Check("Pack", types.UInt64, [pairType], new Ir.Convert(ConvKind.Bitcast, Arg(0, 64), 64));
        var saved = new Variable(Storage.Gpr(9), 1);
        Check("Snapshot", positionType, [new ByRefRef(positionType), positionType], new Use(saved, 32), true,
            new Define(0x1000, saved, new Ir.Convert(ConvKind.ZeroExtend, new Load(Arg(0, 64), 32), 64)),
            new Store(0x1004, Arg(0, 64), Arg(1, 32)));
        Check("PartialReturn", positionType, [new ByRefRef(positionType)], new Use(saved, 32), false,
            new Define(0x1000, saved, new Ir.Convert(ConvKind.ZeroExtend, new Load(Arg(0, 64), 16), 64)));
        foreach (var variant in new[] { "Padding", "Overlap", "Reference", "Unknown" })
        {
            var invalid = Type(variant, true, 8); var invalidType = new DefinitionRef(invalid, []);
            invalid.Fields = variant switch
            {
                "Padding" => [Field(invalid, "a", types.Int16, 0), Field(invalid, "b", types.Int32, 4)],
                "Overlap" => [Field(invalid, "a", types.Int64, 0), Field(invalid, "b", types.Int32, 4)],
                "Reference" => [Field(invalid, "a", types.Object, 0)],
                _ => [Field(invalid, "a", types.Int64, 0), Field(invalid, "b", types.Byte, -1)],
            };
            Check(variant, types.UInt64, [invalidType], new Ir.Convert(ConvKind.Bitcast, Arg(0, 64), 64), false);
        }
        using var stream = new MemoryStream(); assembly.Write(stream); ExecuteSynthetic(SR.Assembly.Load(stream.ToArray()));
        ObjectAllocationCheck.Source(assembly, ExecuteSynthetic, "conditional-values-source-check");
        Console.WriteLine("条件值 CIL/C# 通过：整数符号、浮点原始位型、零引用与公共基类；结构体按完整字段打包，拒绝填充、重叠、引用、未知字段和条件位宽错误");
    }

    private static void ExecuteSynthetic(SR.Assembly assembly)
    {
        var host = assembly.GetType("Checks.Harness", true)!;
        object? Run(string name, params object?[] args) => host.GetMethod(name)!.Invoke(null, args);
        foreach (var value in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        foreach (var choice in new[] { 0, 1 })
        {
            Require((int)Run("Signed", value, (uint)~value, choice)! == (choice != 0 ? value : ~value), "32 位条件值不改变符号位");
            var wide = ((long)value << 32) | 0x81234567;
            Require((long)Run("Wide", wide, (ulong)~wide, choice)! == (choice != 0 ? wide : ~wide), "64 位条件值保持全部位");
        }
        foreach (var bits in new uint[] { 0, 1, 0x80000000, 0x7f800000, 0xff800000, 0x7fc01234, 0xff801234 })
        {
            var value = BitConverter.UInt32BitsToSingle(bits);
            Require(BitConverter.SingleToUInt32Bits((float)Run("FloatingBits", value, ~bits, 1)!) == bits, "选中的浮点不丢负零或 NaN 载荷");
            Require(BitConverter.SingleToUInt32Bits((float)Run("FloatingBits", value, ~bits, 0)!) == ~bits, "整数分支按原位型解释为浮点");
            foreach (var signed in new[] { int.MinValue, -1, 0, int.MaxValue })
                Require((ulong)Run("Pack", new FloatInt { Real = value, Signed = signed })! == ((ulong)(uint)signed << 32 | bits), "结构体打包保持浮点载荷及整数符号位");
        }
        var text = new string('x', 3); var other = new object();
        Require(ReferenceEquals(Run("Nullable", text, 1), text) && Run("Nullable", text, 0) is null, "常量零恢复为 null");
        Require(Run("ZeroLocal", text, 1) is null && ReferenceEquals(Run("ZeroLocal", text, 0), text), "已证明的局部零恢复为 null");
        Require(ReferenceEquals(Run("Common", text, other, 1), text) && ReferenceEquals(Run("Common", text, other, 0), other), "公共基类条件值保持对象身份");
        var snapshot = (Snapshot)host.GetMethod("Snapshot")!.CreateDelegate(typeof(Snapshot));
        var source = new Position { Invalid = true, X = -128, Y = 17, Z = 127 };
        var old = snapshot(ref source, new Position { X = 1, Y = -2, Z = 3 });
        Require(old.Invalid && old.X == -128 && old.Y == 17 && old.Z == 127 && !source.Invalid && source.X == 1 && source.Y == -2 && source.Z == 3,
            "完整返回保留原读取时机，不拆开私有字段，也不把读取推迟到源值被覆盖后");
    }

    private static void Native(RecoverySession session, string oracle)
    {
        const ulong address = 0x58688ac;
        var method = session.Model.Code[address].Single().Method;
        var constructor = session.Model.Code[0xa45f880].Single().Method;
        Require(method.ToString() == "Sekai.Mysekai.GridAreaData.GetSquareMin" && constructor.ToString() == "Sekai.Mysekai.GridPosition..ctor", "真实方法身份");
        var vector = (DefinitionRef)method.Method.Parameters.Single().Type; var position = (DefinitionRef)method.Method.ReturnType;
        Require(constructor.DeclaringType == position && constructor.Method.Parameters.Select(p => p.Type).SequenceEqual(Enumerable.Repeat(session.Types.Int32, 3)), "坐标构造签名");
        var vectorFields = vector.Definition.Fields.Where(f => !f.IsStatic).OrderBy(f => f.Offset).ToArray();
        var positionFields = position.Definition.Fields.Where(f => !f.IsStatic).OrderBy(f => f.Offset).ToArray();
        Require(vectorFields.Select(f => f.Offset).SequenceEqual([0, 4, 8]) && vectorFields.All(f => f.Type == session.Types.Int32), "Vector3Int 的三个完整字段");
        Require(positionFields.Select(f => f.Offset).SequenceEqual([0, 1, 2, 3]) && positionFields[0].Type == session.Types.Boolean
            && positionFields.Skip(1).All(f => f.Type == session.Types.SByte), "GridPosition 的 bool 与三个 sbyte 字段");
        var recovered = new[] { method, constructor }.Select(m => BodyRecovery.Recover(session, session.Analyze(m, m.Method.Address))).ToArray();
        foreach (var body in recovered) Require(body.Body is not null, string.Join("; ", body.Problems));
        var bodies = recovered.SelectMany(r => r.Body!.Accessors.Select(a => a.Proof.Body).Concat(r.Body.Constructors.Select(c => c.Body)).Append(r.Body))
            .DistinctBy(b => b.Method).ToArray();
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeConditionalChecks", new Version(1, 0)), "NativeConditionalChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var target = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(target);
        TypeReference Reference(TypeRef type) => type is ByRefRef reference ? new ByReferenceType(Reference(reference.Element))
            : type == vector ? module.ImportReference(typeof(Vector)) : type == position ? module.ImportReference(typeof(Position))
            : type == method.DeclaringType ? module.TypeSystem.Object : type == session.Types.RuntimeTypeHandle ? module.ImportReference(typeof(RuntimeTypeHandle))
            : module.ImportReference(System.Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var fields = vectorFields.Select((f, i) => (f, host: typeof(Vector).GetField(new[] { "X", "Y", "Z" }[i])))
            .Concat(positionFields.Select((f, i) => (f, host: typeof(Position).GetField(new[] { "Invalid", "X", "Y", "Z" }[i]))))
            .ToDictionary(p => p.f, p => module.ImportReference(p.host));
        var mapped = new Dictionary<MethodDef, MethodDefinition>();
        foreach (var original in bodies.Select(b => b.Method))
        {
            var actual = new MethodDefinition(original == constructor ? "Initialize" : original.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(original.Method.ReturnType));
            actual.Parameters.Add(new ParameterDefinition(Reference(original.Method.Owner.IsValueType ? new ByRefRef(original.DeclaringType) : original.DeclaringType)));
            foreach (var parameter in original.Method.Parameters) actual.Parameters.Add(new ParameterDefinition(Reference(parameter.Type)));
            target.Methods.Add(actual); mapped.Add(original.Method, actual);
        }
        var initializer = ClassInitialization.Invocation(session.Types, position, out _)!.Method;
        var emitter = new BodyEmitter(session.Types, Reference, f => fields[f.Field], m => mapped.TryGetValue(m.Method, out var actual) ? actual
            : m == initializer ? module.ImportReference(typeof(System.Runtime.CompilerServices.RuntimeHelpers).GetMethod("RunClassConstructor", [typeof(RuntimeTypeHandle)]))
            : throw new NotSupportedException(m.ToString()));
        foreach (var body in bodies)
        {
            var actual = mapped[body.Method.Method];
            var problem = emitter.Emit(body, actual); Require(problem is null, problem ?? body.Method.ToString());
            // 静态宿主的首参数表示 this；显式参数顺延，ldarg.0 的 this 保持不变。
            foreach (var instruction in actual.Body.Instructions)
                if (instruction.Operand is ParameterDefinition parameter) instruction.Operand = actual.Parameters[parameter.Index + 1];
        }
        // 构造入口只记录实参，后续指令仍是完整恢复体。
        var init = mapped[constructor.Method]; var il = init.Body.GetILProcessor(); var first = init.Body.Instructions[0];
        foreach (var parameter in init.Parameters.Skip(1)) il.InsertBefore(first, il.Create(OpCodes.Ldarg, parameter));
        il.InsertBefore(first, il.Create(OpCodes.Call, module.ImportReference(typeof(ConditionalValueCheck).GetMethod(nameof(Observe)))));
        using var document = JsonDocument.Parse(File.ReadAllText(oracle));
        Require(document.RootElement.GetProperty("binarySha256").GetString() == session.Model.Image.Sha256
            && document.RootElement.GetProperty("start").GetUInt64() == address && document.RootElement.GetProperty("stop").GetUInt64() == 0x5868900, "Unicorn 参照对应当前二进制和完整计算段");
        var cases = document.RootElement.GetProperty("cases").EnumerateArray().Select(row =>
            (Input: row.GetProperty("input").EnumerateArray().Select(v => v.GetInt32()).ToArray(), Args: row.GetProperty("arguments").EnumerateArray().Select(v => v.GetInt32()).ToArray())).ToArray();
        Require(cases.Length == 1361, "边界组合与固定随机输入的完整参照集");
        void Execute(SR.Assembly output)
        {
            var run = (Func<object?, Vector, Position>)output.GetType("Checks.Harness", true)!.GetMethod("GetSquareMin")!.CreateDelegate(typeof(Func<object?, Vector, Position>));
            foreach (var (input, args) in cases)
            {
                var before = calls; var result = run(null, new Vector { X = input[0], Y = input[1], Z = input[2] });
                Require(calls == before + 1 && observed == (args[0], args[1], args[2]),
                    $"真实计算段与 Unicorn 实参不符: input={string.Join(',', input)}, expected={string.Join(',', args)}, actual={observed}, calls={calls - before}");
                Require(!result.Invalid && result.X == unchecked((sbyte)args[0]) && result.Y == unchecked((sbyte)args[1]) && result.Z == unchecked((sbyte)args[2]), "真实构造体与寄存器返回保持四字节坐标");
            }
        }
        using var stream = new MemoryStream(); assembly.Write(stream); Execute(SR.Assembly.Load(stream.ToArray()));
        ObjectAllocationCheck.Source(assembly, Execute, "conditional-values-source-check");
        Console.WriteLine($"真实 GetSquareMin 与 GridPosition 构造 CIL/C# 各通过 {cases.Length} 个 Unicorn 计算段参照；构造全部实参、返回位型一致，未加载 Unity");
    }

    private static void Require(bool condition, string message) { if (!condition) throw new InvalidOperationException(message); }
}
