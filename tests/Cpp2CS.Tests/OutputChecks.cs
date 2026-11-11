using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using Mono.Cecil.Cil;
using R = System.Reflection;

namespace Cpp2CS.Tests;

internal static class OutputChecks
{
    public const string Command = "output";

    public static int Run()
    {
        var checks = new Assertions();
        foreach (var pointerSize in new[] { 4, 8 }) Check(checks, pointerSize);
        return checks.Finish("Output");
    }

    private static void Check(Assertions checks, int pointerSize)
    {
        var definitions = new List<TypeDef>();
        TypeDef Define(string name, bool value = false, string assembly = "mscorlib.dll")
        {
            var d = new TypeDef { Index = definitions.Count, Assembly = assembly, Namespace = "System", Name = name,
                Token = 0, Attributes = R.TypeAttributes.Public, IsValueType = value, IsEnum = false };
            definitions.Add(d);
            return d;
        }
        var obj = Define("Object");
        var valueType = Define("ValueType");
        valueType.BaseType = new DefinitionRef(obj, []);
        foreach (var name in new[] { "Void", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference" })
            Define(name, true).BaseType = new DefinitionRef(valueType, []);
        Define("String").BaseType = new DefinitionRef(obj, []);
        Define("Exception").BaseType = new DefinitionRef(obj, []);
        var owner = Define("Container", assembly: "OutputChecks.dll");
        owner.BaseType = new DefinitionRef(obj, []);
        var methods = new List<MethodDef>();
        var fields = new List<FieldDef>();
        var assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
            AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray();
        var model = new ProgramModel { MetadataVersion = 31, Assemblies = assemblies, Types = definitions,
            Methods = methods, Fields = fields, RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [] };
        var types = new ManagedTypes(model, new Layouts(pointerSize), pointerSize);
        var width = pointerSize * 8;
        var ownerRef = new DefinitionRef(owner, []);
        MethodDef Method(string name, TypeRef returns, bool instance = false, bool virtualCall = false, params TypeRef[] parameters)
        {
            var m = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = 0,
                Attributes = R.MethodAttributes.Public | (instance ? 0 : R.MethodAttributes.Static)
                    | (virtualCall ? R.MethodAttributes.Virtual | R.MethodAttributes.NewSlot : 0),
                ImplAttributes = 0, Slot = -1, ReturnType = returns,
                Parameters = parameters.Select((t, i) => new ParameterDef($"p{i}", t, 0, null, false)).ToArray() };
            methods.Add(m); owner.Methods = methods.Where(m => m.Owner == owner).ToArray(); return m;
        }
        FieldDef Field(string name, bool isStatic)
        {
            var f = new FieldDef { Index = fields.Count, Owner = owner, Name = name, Type = types.Int32,
                Attributes = R.FieldAttributes.Public | (isStatic ? R.FieldAttributes.Static : 0), Offset = 0 };
            fields.Add(f); owner.Fields = fields.ToArray(); return f;
        }
        var field = Field("Item", false);
        var staticField = Field("Count", true);
        var instance = Method("Read", types.Int32, true);
        var virtualMethod = Method("VirtualRead", types.Int32, true, true);
        var identity = Method("Identity", types.Int32, parameters: [types.Int32]);
        var arithmetic = Method("Arithmetic", types.Int32, parameters: [types.Int32, types.Int32]);
        var loop = Method("Loop", types.Int32, parameters: [types.Int32]);
        var accesses = Method("Accesses", types.Int32, parameters: [ownerRef]);
        var boxing = Method("Boxing", types.Int32, parameters: [types.Int32]);
        var arrays = Method("Arrays", types.Int32);
        var finalizing = Method("Finalizing", types.Int32);
        var holeMethod = Method("Missing", types.Int32);
        var pendingMethod = Method("Pending", types.Int32, parameters: [ownerRef]);
        var floating = Method("Floating", types.Boolean, parameters: [types.Double, types.Double]);
        ConstantValue C(ulong n) => new(n, types.Int32, 32);
        ArgumentValue A(int i, TypeRef? t = null) => new(i, t ?? types.Int32, t is null ? 32 : width);
        LocalValue L(int i, TypeRef? t = null) => new(new(i), t ?? types.Int32, t is null ? 32 : width);
        ManagedBlock B(ulong id, params ManagedStatement[] statements) => new(id, statements);
        ManagedReturn Ret(ManagedValue v) => new(0, v);
        ManagedBody Body(MethodDef m, params ManagedBlock[] blocks) => new(MethodRef.Open(m), blocks);
        var local = L(0);
        var receiver = A(0, ownerRef);
        var item = new FieldValue(receiver, new(field, ownerRef), types.Int32, 32);
        var count = new StaticFieldValue(new(staticField, ownerRef), types.Int32, 32);
        var boxed = L(1, types.Object);
        var arrayType = new ArrayRef(types.Int32, 1);
        var array = L(2, arrayType);
        var element = new ArrayElementValue(array, C(0), types.Int32, 32);
        var bodies = new List<ManagedBody>
        {
            Body(instance, B(0, Ret(C(3)))), Body(virtualMethod, B(0, Ret(C(4)))), Body(identity, B(0, Ret(A(0)))),
            Body(arithmetic, B(0, new ManagedAssignment(0, local, new BinaryValue(BinaryOperator.Add, A(0), A(1), types.Int32, 32)),
                Ret(new BinaryValue(BinaryOperator.SignedDivide, local, A(1), types.Int32, 32)))),
            Body(loop, B(0, new ManagedAssignment(0, local, C(0)), new ManagedJump(0, new(1, []))),
                B(1, new ManagedBranch(1, new ComparisonValue(ComparisonKind.SignedLess, local, A(0), types.Boolean), new(2, []), new(3, []))),
                B(2, new ManagedAssignment(2, local, new BinaryValue(BinaryOperator.Add, local, C(1), types.Int32, 32)), new ManagedJump(2, new(1, []))), B(3, Ret(local))),
            Body(accesses, B(0, new ManagedStore(0, item, C(7)), new ManagedStore(0, count, item),
                new ManagedCall(0, new(MethodRef.Open(identity), null, [count], false), local),
                new ManagedCall(0, new(MethodRef.Open(instance), receiver, [], false), local),
                new ManagedCall(0, new(MethodRef.Open(virtualMethod), receiver, [], true), local), Ret(local))),
            Body(boxing, B(0, new ManagedAssignment(0, boxed, new BoxValue(A(0), types.Int32, types.Object, width)),
                new ManagedAssignment(0, boxed, new IsInstValue(boxed, types.Object, width)),
                new ManagedAssignment(0, boxed, new CheckedCastValue(boxed, types.Object, width)), Ret(new UnboxValue(boxed, types.Int32, 32)))),
            Body(arrays, B(0, new ManagedAssignment(0, array, new NewArrayValue(arrayType, C(2), width)),
                new ManagedStore(0, element, C(9)), new ManagedAssignment(0, local, element), Ret(new ArrayLengthValue(array, types.Int32, 32)))),
            Body(finalizing, B(0, Ret(C(5))), B(1, new ManagedStore(1, count, C(1)), new ManagedEndFault(1))) with
                { Regions = [new([0], 1, [1], null, ManagedRegionKind.Finally)] },
            Body(floating, B(0, Ret(new ComparisonValue(ComparisonKind.FloatUnorderedOrEqual,
                new ArgumentValue(0, types.Double, 64), new ArgumentValue(1, types.Double, 64), types.Boolean)))),
        };
        // 按枚举名称逐项覆盖，避免迁移时按旧枚举数值对应。
        foreach (var operation in Enum.GetValues<BinaryOperator>())
        {
            var isFloat = operation is BinaryOperator.FloatAdd or BinaryOperator.FloatSubtract or BinaryOperator.FloatMultiply or BinaryOperator.FloatDivide;
            var type = isFloat ? types.Double : types.Int32;
            var bits = isFloat ? 64 : 32;
            var method = Method($"Binary{operation}", type, parameters: [type, type]);
            bodies.Add(Body(method, B(0, Ret(new BinaryValue(operation,
                new ArgumentValue(0, type, bits), new ArgumentValue(1, type, bits), type, bits)))));
        }
        foreach (var comparison in Enum.GetValues<ComparisonKind>())
        {
            var isFloat = comparison.ToString().StartsWith("Float", StringComparison.Ordinal);
            var type = isFloat ? types.Double : types.Int32;
            var bits = isFloat ? 64 : 32;
            var method = Method($"Compare{comparison}", types.Boolean, parameters: [type, type]);
            bodies.Add(Body(method, B(0, Ret(new ComparisonValue(comparison,
                new ArgumentValue(0, type, bits), new ArgumentValue(1, type, bits), types.Boolean)))));
        }
        var signedConversion = Method("ConvertSigned", types.Int32, parameters: [types.Double]);
        var unsignedConversion = Method("ConvertUnsigned", types.UInt64, parameters: [types.Double]);
        bodies.Add(Body(signedConversion, B(0, Ret(new ConversionValue(ConversionKind.FloatToSignedInteger,
            new ArgumentValue(0, types.Double, 64), types.Int32, 32)))));
        bodies.Add(Body(unsignedConversion, B(0, Ret(new ConversionValue(ConversionKind.FloatToUnsignedInteger,
            new ArgumentValue(0, types.Double, 64), types.UInt64, 64)))));
        var objectConstructor = new MethodDef
        {
            Index = methods.Count, Owner = obj, Name = ".ctor", Token = 0,
            Attributes = R.MethodAttributes.Public | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName,
            ImplAttributes = 0, Slot = -1, ReturnType = types.Corlib("System.Void"),
        };
        methods.Add(objectConstructor);
        obj.Methods = [objectConstructor];
        var constructor = Method(".ctor", types.Corlib("System.Void"), true);
        var created = Method("Create", ownerRef);
        var invalid = Method("Invalid", types.Int32);
        var constructorBody = Body(constructor, B(0,
            new ManagedCall(0, new(MethodRef.Open(objectConstructor), new ArgumentValue(-1, ownerRef, width), [], false), null),
            new ManagedReturn(0, null)));
        bodies.Add(constructorBody);
        bodies.Add(Body(created, B(0, Ret(new NewObjectValue(MethodRef.Open(constructor), [], width)))));
        var skeleton = new Skeleton(model, pointerSize * 2);
        var emitter = new BodyEmitter(skeleton, types);
        var problems = emitter.Emit(bodies);
        foreach (var problem in problems) Console.Error.WriteLine($"{problem.Key.Method}: {problem.Value}");
        checks.True(problems.Count == 0, $"{width} 位合成方法通过写出前检查与栈类型检查");
        OutputIlVerification.Check(checks, skeleton);
        using var stream = new MemoryStream();
        skeleton.Assembly("OutputChecks.dll").Write(stream);
        stream.Position = 0;
        using var read = AssemblyDefinition.ReadAssembly(stream);
        var readMethods = read.MainModule.Types.Single(t => t.Name == "Container").Methods.ToDictionary(m => m.Name);
        void Codes(string name, params Code[] codes) => checks.True(codes.All(c => readMethods[name].Body.Instructions.Any(i => i.OpCode.Code == c)), $"{name} 的关键 CIL 指令往返保留");
        checks.True(readMethods["Arithmetic"].IsStatic && readMethods["Arithmetic"].ReturnType.FullName == "System.Int32"
            && readMethods["Arithmetic"].Parameters.Count == 2 && readMethods["Arithmetic"].Body.Variables.Count == 1
            && readMethods["Arithmetic"].Body.Variables[0].VariableType.FullName == "System.Int32", "方法签名与局部变量往返保留");
        Codes("Arithmetic", Code.Add, Code.Div, Code.Ret);
        Codes("BinaryUnsignedDivide", Code.Div_Un);
        Codes("BinarySignedRemainder", Code.Rem);
        Codes("BinaryUnsignedRemainder", Code.Rem_Un);
        Codes("ConvertSigned", Code.Conv_I4);
        Codes("ConvertUnsigned", Code.Conv_U8);
        checks.True(readMethods["ConvertSigned"].Body.Variables.Count == 0
            && readMethods["ConvertUnsigned"].Body.Variables.Count == 0, "浮点转整数直接采用 IL 转换，不插入原生饱和分支");
        checks.True(!readMethods["Arithmetic"].Body.Instructions.Any(i => i.OpCode.FlowControl == FlowControl.Cond_Branch), "托管除法不插入原生除零默认值分支");
        Codes("Loop", Code.Clt, Code.Brtrue, Code.Br);
        checks.True(readMethods["Loop"].Body.Instructions.Any(i => i.Operand is Instruction target && target.Offset < i.Offset), "循环保留回边");
        Codes("Accesses", Code.Stfld, Code.Ldfld, Code.Stsfld, Code.Ldsfld, Code.Call, Code.Callvirt);
        Codes("Boxing", Code.Box, Code.Unbox_Any, Code.Isinst, Code.Castclass);
        Codes("Arrays", Code.Newarr, Code.Stelem_Any, Code.Ldelem_Any, Code.Ldlen);
        Codes("Finalizing", Code.Leave, Code.Endfinally);
        Codes(".ctor", Code.Call, Code.Ret);
        Codes("Create", Code.Newobj, Code.Ret);
        var handler = readMethods["Finalizing"].Body.ExceptionHandlers.Single();
        checks.True(handler.HandlerType == ExceptionHandlerType.Finally && handler.TryStart.Offset < handler.TryEnd.Offset
            && handler.TryEnd == handler.HandlerStart && handler.HandlerStart.Offset < handler.HandlerEnd.Offset, "finally 的半开区间与处理入口往返保留");
        var invalidBody = Body(invalid, B(0, Ret(new ConstantValue(0, types.Object, width))));
        var previous = skeleton.Method(invalid).Body;
        var rejected = emitter.Emit([invalidBody]);
        checks.True(rejected.TryGetValue(invalidBody, out var invalidProblem) && invalidProblem.Kind == EmissionProblemKind.StackType
            && ReferenceEquals(previous, skeleton.Method(invalid).Body), "栈类型不符时报告问题并保留原骨架体");
        var missingBaseCall = Body(constructor, B(0, new ManagedReturn(0, null)));
        checks.True(emitter.Check([missingBaseCall]).TryGetValue(missingBaseCall, out var constructorProblem)
            && constructorProblem.Kind == EmissionProblemKind.Constructor, "缺少基类初始化的构造函数被拒绝");
        var missingTarget = Body(invalid, B(0, new ManagedJump(0, new(1, []))));
        checks.True(emitter.Check([missingTarget]).Count == 1, "不存在的分支目标被拒绝");
        var missing = Body(holeMethod, B(0, Ret(new HoleValue("缺少证明", types.Int32, 32))));
        checks.True(emitter.Emit([missing], EmissionPolicy.Partial).Count == 0, "部分体的洞沿用显式辅助调用");
        checks.True(skeleton.Assembly("OutputChecks.dll").MainModule.Types.Single(t => t.FullName == "Cpp2CS.Unrecovered")
            .Methods.All(m => m.Body.Instructions.Last().OpCode == OpCodes.Throw), "洞辅助方法只抛出，不返回默认值");
        var pending = Body(pendingMethod, B(0, Ret(item with { Pending = new(0, "未折叠访问", false) })));
        checks.True(emitter.Check([pending]).Count == 0, "待折叠注解沿用字段访问校验，不生成默认值");
    }

    private sealed class Layouts(int pointerSize) : ITypeLayouts
    {
        public TypeLayout? Of(DefinitionRef type) => null;
        public (int Size, int Alignment) SizeAndAlignment(TypeRef type) => TrySizeAndAlignment(type) ?? throw new InvalidOperationException("没有合成布局");
        public (int Size, int Alignment)? TrySizeAndAlignment(TypeRef type) => ManagedTypes.PrimitiveName(type) switch
        {
            "Boolean" or "Byte" or "SByte" => (1, 1),
            "Char" or "Int16" or "UInt16" => (2, 2),
            "Int32" or "UInt32" or "Single" => (4, 4),
            "Int64" or "UInt64" or "Double" => (8, 8),
            "IntPtr" or "UIntPtr" => (pointerSize, pointerSize),
            _ when ManagedTypes.IsReferenceType(type) || type is PointerRef or ByRefRef => (pointerSize, pointerSize),
            _ => null,
        };
    }
}
