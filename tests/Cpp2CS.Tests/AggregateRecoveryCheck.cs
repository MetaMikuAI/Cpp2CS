using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class AggregateRecoveryCheck
{
    public struct Float3 { public float X; public float Y; public float Z; }
    public struct Mixed { public double A; public int B; public int C; }
    public struct References { public object? A; public object? B; }
    private static int calls;
    private static Float3 received;
    public static Float3 Produce() { calls++; return new() { X = 1.25f, Y = -2.5f, Z = 7 }; }
    public static Float3 Forward(Float3 value) { calls++; received = value; return value; }

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        var aggregates = new AggregateValues(types);
        TypeDef Definition(string name, int size) => new() { Index = -1, Assembly = "AggregateChecks.dll", Namespace = "Checks", Name = name,
            Token = 0, Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false, Size = size };
        DefinitionRef Struct(string name, int size, params (string Name, TypeRef Type, int Offset)[] fields)
        {
            var definition = Definition(name, size);
            definition.Fields = fields.Select(f => new FieldDef { Index = -1, Owner = definition, Name = f.Name, Type = f.Type, Offset = f.Offset,
                Token = 0, Attributes = SR.FieldAttributes.Public }).ToArray();
            return new(definition, []);
        }
        var float3 = Struct(nameof(Float3), 12, ("X", types.Single, 0), ("Y", types.Single, 4), ("Z", types.Single, 8));
        var mixed = Struct(nameof(Mixed), 16, ("A", types.Double, 0), ("B", types.Int32, 8), ("C", types.Int32, 12));
        var references = Struct(nameof(References), 16, ("A", types.Object, 0), ("B", types.Object, 8));
        var padded = Struct("Padded", 8, ("A", types.Byte, 0), ("B", types.Int32, 4));
        var overlap = Struct("Overlap", 8, ("A", types.Int64, 0), ("B", types.Int32, 4));
        var nested = Struct("Nested", 16, ("A", float3, 0), ("B", types.Int32, 12));
        var zero = new ConstantValue(0, types.UInt64, 64);
        Require(aggregates.Assemble(mixed, [(0, zero)]) is null, "缺少字段分量必须失败");
        Require(aggregates.Assemble(mixed, [(0, zero), (4, zero), (8, zero)]) is null, "重叠分量必须失败");
        Require(aggregates.Assemble(overlap, [(0, zero)]) is null, "联合布局不能按独立字段组装");
        Require(aggregates.Assemble(references, [(0, new ConstantValue(1, types.UInt64, 64)), (8, zero)]) is null, "整数不能冒充引用");
        Require(aggregates.Assemble(references, [(0, zero), (8, zero)]) is DefaultValue, "已证明的零可成为 null");
        Require(aggregates.Project(new ArgumentValue(0, "p", padded, 64), 1, 16) is null, "填充字节没有托管值");
        Require(aggregates.Assemble(nested, [(0, new ConstantValue(1, types.UInt64, 64)), (8, zero)]) is AggregateValue { Members.Count: 4 }, "嵌套字段按具体布局组装");
        Require(!types.IsAssignable(types.Int32, types.Object), "数值到 object 需要显式装箱");

        var owner = Definition("Harness", 1);
        MethodRef Method(string name, TypeRef result, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result,
            Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
        }, [], []);
        ManagedBody Recover(MethodRef method, params Stmt[] statements)
        {
            var function = new MachineFunction { Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1100, BoundaryEvidence.SymbolCandidate, "聚合检查"),
                Blocks = [new Block(0x1000) { Statements = [.. statements] }] };
            function.Renumber();
            var result = BodyRecovery.Recover(session, new PreparedMethod(method, session.Abi.ClassifyReturn(method.Method.ReturnType, out _), function, null, []), false);
            Require(result.Body is not null, method + ": " + string.Join("; ", result.Problems));
            return result.Body!;
        }
        ManagedBody Echo(string name, TypeRef type)
        {
            var method = Method(name, type, type);
            var shape = session.Abi.Classify(method, out _)!.Parameters[0];
            return Recover(method, new Return(0x1000) { Pieces = shape.Pieces.Select(p => new ReturnPiece(p.Offset, new Use(new Variable(p.Register, 0), p.Width))).ToArray() });
        }

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("AggregateChecks", new Version(1, 0)), "AggregateChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var harness = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(harness);
        var mapped = new Dictionary<TypeRef, Type> { [float3] = typeof(Float3), [mixed] = typeof(Mixed), [references] = typeof(References) };
        TypeReference Reference(TypeRef type) => module.ImportReference(mapped.TryGetValue(type, out var runtimeType) ? runtimeType : type == types.Object ? typeof(object)
            : Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        FieldReference Field(FieldRef field) => module.ImportReference(mapped[field.DeclaringType].GetField(field.Field.Name));
        var target = session.Model.Code.First(p => p.Value.Count == 1 && p.Value[0].Method.Method is { IsStatic: true, Parameters.Count: 0 } m
            && m.ReturnType.ToString() == "UnityEngine.Vector3" && m.GenericParameters.Count == 0 && m.Owner.GenericParameters.Count == 0);
        var targetMethod = target.Value[0].Method;
        var nativeVector = targetMethod.Method.ReturnType;
        var forwardTarget = session.Model.Code.First(p => p.Value.Count == 1 && p.Value[0].Method.Method is { IsStatic: true, Parameters.Count: 1 } m
            && m.ReturnType == nativeVector && m.Parameters[0].Type == nativeVector && m.Owner == ((DefinitionRef)nativeVector).Definition
            && (m.Attributes & SR.MethodAttributes.MemberAccessMask) == SR.MethodAttributes.Public);
        var forwardMethod = forwardTarget.Value[0].Method;
        mapped.Add(nativeVector, typeof(Float3));
        FieldReference MappedField(FieldRef field) => field.DeclaringType == nativeVector
            ? module.ImportReference(typeof(Float3).GetField(field.Field.Name.ToUpperInvariant())) : Field(field);
        var emitter = new BodyEmitter(types, Reference, MappedField,
            m => m.Method == targetMethod.Method ? module.ImportReference(typeof(AggregateRecoveryCheck).GetMethod(nameof(Produce)))
                : m.Method == forwardMethod.Method ? module.ImportReference(typeof(AggregateRecoveryCheck).GetMethod(nameof(Forward))) : throw new NotSupportedException(m.ToString()));
        void Emit(ManagedBody recovered)
        {
            var method = new MethodDefinition(recovered.Method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(recovered.Method.Method.ReturnType));
            foreach (var p in recovered.Method.Method.Parameters) method.Parameters.Add(new ParameterDefinition(Reference(p.Type)));
            harness.Methods.Add(method);
            var problem = emitter.Emit(recovered, method);
            Require(problem is null, method.Name + " CIL: " + problem);
        }
        Emit(Echo("FloatEcho", float3));
        Emit(Echo("MixedEcho", mixed));
        Emit(Echo("ReferenceEcho", references));
        var resultShape = session.Abi.Classify(targetMethod, out _)!.Return!;
        Require(resultShape.Pieces.Length == 3, "真实 Vector3 返回签名");
        var call = new Call(0x1004, CallKind.Direct, Expr.C(target.Key, 64))
        {
            Results = resultShape.Pieces.Select(p => p.Register).ToArray(), Defines = resultShape.Pieces.Select(p => new Variable(p.Register, 1)).ToArray(),
        };
        var called = Recover(Method("Called", nativeVector), new Define(0x1000, new Variable(Storage.Temp(0), 1), Expr.C(17, 32)), call,
            new Return(0x1008) { Pieces = resultShape.Pieces.Select((p, i) => new ReturnPiece(p.Offset, new Use(call.Defines[i], p.Width))).ToArray() });
        Require(called.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Result!.Variable.Storage != Storage.Temp(0), "整值返回局部变量不能占用原生临时变量");
        Emit(called);
        var forwardingShape = session.Abi.Classify(forwardMethod, out _)!.Parameters[0];
        var forwardedCall = call with
        {
            Target = Expr.C(forwardTarget.Key, 64), Sources = forwardingShape.Pieces.Select(p => p.Register).ToArray(),
            Arguments = forwardingShape.Pieces.Select(p => (Expr)new Use(new Variable(p.Register, 0), p.Width)).ToArray(),
        };
        Emit(Recover(Method("Forwarded", nativeVector, float3), forwardedCall,
            new Return(0x1008) { Pieces = resultShape.Pieces.Select((p, i) => new ReturnPiece(p.Offset, new Use(call.Defines[i], p.Width))).ToArray() }));
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
        foreach (var bits in new[] { 0, int.MinValue, 0x7f800000, unchecked((int)0xff800000), 0x7fc12345, 1, 0x3f800000 })
        {
            var input = new Float3 { X = BitConverter.Int32BitsToSingle(bits), Y = -3.25f, Z = BitConverter.Int32BitsToSingle(~bits) };
            var output = (Float3)runtime.GetMethod("FloatEcho")!.Invoke(null, [input])!;
            Require(BitConverter.SingleToInt32Bits(output.X) == bits && BitConverter.SingleToInt32Bits(output.Z) == ~bits && output.Y == input.Y, "HFA 位型往返");
            var before = calls;
            var forwarded = (Float3)runtime.GetMethod("Forwarded")!.Invoke(null, [input])!;
            Require(calls == before + 1 && BitConverter.SingleToInt32Bits(received.X) == bits && BitConverter.SingleToInt32Bits(received.Z) == ~bits
                && BitConverter.SingleToInt32Bits(forwarded.X) == bits && BitConverter.SingleToInt32Bits(forwarded.Z) == ~bits, "多寄存器调用参数和返回保持位型");
        }
        foreach (var bits in new[] { 0L, long.MinValue, 0x7ff0000000000000, 0x7ff8000000001234, 1L })
        foreach (var integer in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            var input = new Mixed { A = BitConverter.Int64BitsToDouble(bits), B = integer, C = ~integer };
            var output = (Mixed)runtime.GetMethod("MixedEcho")!.Invoke(null, [input])!;
            Require(BitConverter.DoubleToInt64Bits(output.A) == bits && output.B == input.B && output.C == input.C, "GPR 浮点及打包整数往返");
        }
        foreach (var first in new object?[] { null, new object() })
        foreach (var second in new object?[] { null, first, new object() })
        {
            var output = (References)runtime.GetMethod("ReferenceEcho")!.Invoke(null, [new References { A = first, B = second }])!;
            Require(ReferenceEquals(output.A, first) && ReferenceEquals(output.B, second), "引用身份保持");
        }
        calls = 0;
        var returned = (Float3)runtime.GetMethod("Called")!.Invoke(null, null)!;
        Require(calls == 1 && returned.X == 1.25f && returned.Y == -2.5f && returned.Z == 7, "多分量返回只执行一次调用");
        Console.WriteLine("聚合执行检查通过：HFA、打包整数、浮点位型、引用身份、调用参数和单次返回、临时变量冲突及无效布局拒绝");
        Native(session);
        return 0;
    }

    private static void Native(RecoverySession session)
    {
        var methods = new ulong[] { 0x58f557c, 0x58f5588, 0x59015f0 }.Select(a => (Address: a, Method: session.Model.Code[a].Single().Method)).ToArray();
        Require(methods[0].Method.ToString() == "Sekai.Mysekai.StaminaData.get_Zero" && methods[1].Method.ToString() == "Sekai.Mysekai.StaminaData.op_Addition"
            && methods[2].Method.ToString() == "Sekai.Mysekai.StaminaData.op_Subtraction", "真实聚合方法身份");
        var type = methods[0].Method.DeclaringType;
        var fields = session.Types.Fields(type)!;
        Require(fields.Count == 3 && fields.All(f => f.Type == session.Types.Int32) && fields.Select(f => f.Offset).SequenceEqual(new[] { 0, 4, 8 }), "StaminaData 布局");
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeAggregateChecks", new Version(1, 0)), "NativeAggregateChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "StaminaData", TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout, module.ImportReference(typeof(ValueType)));
        module.Types.Add(host);
        var mappedFields = fields.ToDictionary(f => f.Field.Field, f => new FieldDefinition(f.Field.Field.Name, FieldAttributes.Public, module.TypeSystem.Int32));
        foreach (var field in mappedFields.Values) host.Fields.Add(field);
        TypeReference Reference(TypeRef t) => t == type ? host : module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(t), true)!);
        var emitter = new BodyEmitter(session.Types, Reference, f => mappedFields[f.Field], m => throw new NotSupportedException(m.ToString()));
        foreach (var (address, method) in methods)
        {
            var prepared = session.Analyze(method, address);
            var recovered = BodyRecovery.Recover(session, prepared);
            Require(recovered.Body is not null, method + ": " + string.Join("; ", recovered.Problems));
            var destination = new MethodDefinition(method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, host);
            foreach (var parameter in method.Method.Parameters) destination.Parameters.Add(new ParameterDefinition(Reference(parameter.Type)));
            host.Methods.Add(destination);
            Require(emitter.Emit(recovered.Body!, destination) is null, method + " CIL");
        }
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.StaminaData", true)!;
        var actualFields = fields.Select(f => runtime.GetField(f.Field.Field.Name)!).ToArray();
        object Make(int[] values)
        {
            var value = Activator.CreateInstance(runtime)!;
            for (var i = 0; i < 3; i++) actualFields[i].SetValue(value, values[i]);
            return value;
        }
        var zero = runtime.GetMethod("get_Zero")!.Invoke(null, null)!;
        Require(actualFields.All(f => (int)f.GetValue(zero)! == 0), "真实 Zero 的三字段返回");
        foreach (var a in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        foreach (var b in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            var left = new[] { a, ~a, b };
            var right = new[] { b, a, ~b };
            var result = runtime.GetMethod("op_Addition")!.Invoke(null, [Make(left), Make(right)])!;
            for (var i = 0; i < 3; i++) Require((int)actualFields[i].GetValue(result)! == unchecked(left[i] + right[i]), "真实 Addition 字段及溢出边界");
            var difference = runtime.GetMethod("op_Subtraction")!.Invoke(null, [Make(left), Make(right)])!;
            for (var i = 0; i < 3; i++) Require((int)actualFields[i].GetValue(difference)! == unchecked(left[i] - right[i]), "真实 Subtraction 字段及溢出边界");
        }
        Console.WriteLine("真实 StaminaData.get_Zero / op_Addition / op_Subtraction 恢复方法体执行通过：三字段、双寄存器参数与返回、加减各 25 组整数边界；替代类型布局，无外部调用，未验证游戏运行时");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
