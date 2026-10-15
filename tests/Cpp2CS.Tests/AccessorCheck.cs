using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

/// <summary>访问器等价证明的正反例，以及真实内联读取和真实 setter 在替代宿主中的执行。</summary>
internal static class AccessorCheck
{
    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        var data = session.Model.Types.Single(t => t.FullName == "Sekai.Mysekai.Data.MaterialRenderingSettings");
        var property = data.Properties.Single(p => p.Name == "ShaderAttribute");
        var getter = new MethodRef(property.Getter!, [], []);
        var setter = new MethodRef(property.Setter!, [], []);
        var getProof = session.Accessors.Prove(getter, false);
        var setProof = session.Accessors.Prove(setter, true);
        Require(getProof is not null && setProof is not null && getProof.Field == setProof.Field, "真实 getter/setter 的等价证明");
        var nativeCaller = session.Model.Code[0xa45d0c8].Single().Method;
        Require(nativeCaller.Method.Name == "get_Attribute" && nativeCaller.Method.Owner.Name == "MaterialRenderingSettingsItem", "真实内联 case 身份");
        var prepared = session.Analyze(nativeCaller, 0xa45d0c8);
        var recovered = BodyRecovery.Recover(session, prepared);
        Require(recovered.Body is { Accessors.Count: 1 } && recovered.Body.Accessors[0].Proof.Method == getter, "真实内联字段读取还原为已证明 getter");
        Console.WriteLine($"真实内联读取 0xa45d0c8 → getter 0x{getProof!.Address:x}；setter 0x{setProof!.Address:x}；字段 {getProof.Field}");

        // 只在单块内展开局部定义；计算属性、额外读取和额外写入不能伪装成普通访问器。
        PreparedMethod Variant(MethodRef method, params Stmt[] statements) => new(method, session.Abi.ClassifyReturn(method.Method.ReturnType, out _),
            new MachineFunction { Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1100, BoundaryEvidence.SymbolCandidate, "合成检查"),
                Blocks = [new Block(0x1000) { Statements = [.. statements] }] }, null, []);
        var self = new Use(new Variable(Storage.Gpr(0), 0), 64);
        var location = new Binary(BinOp.Add, self, Expr.C((ulong)getProof.Field.Field.Offset, 64), 64);
        var load = new Load(location, 32);
        var saved = new Variable(Storage.Gpr(2), 1);
        var parameter = new Use(new Variable(Storage.Gpr(1), 0), 32);
        Require(Accessors.Match(session, Variant(getter, new Define(0x1000, saved, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, load, 64)),
            new Return(0x1004) { Value = new Use(saved, 32) }), false) == getProof.Field, "位宽扩展再截断不改变字段值");
        Require(Accessors.Match(session, Variant(getter, new Return(0x1000) { Value = new Binary(BinOp.Add, load, Expr.C(1, 32), 32) }), false) is null, "拒绝字段加一的计算属性");
        Require(Accessors.Match(session, Variant(getter, new Define(0x1000, saved, load), new Return(0x1004) { Value = load }), false) is null, "拒绝多次内存读取");
        Require(Accessors.Match(session, Variant(getter, new Nop(0x1000, "barrier"), new Return(0x1004) { Value = load }), false) is null, "屏障不能按普通字段访问证明等价");
        Require(Accessors.Match(session, Variant(getter, new Nop(0x1000, "hint #2"), new Return(0x1004) { Value = load }), false) is null, "等待事件指令不能当作普通空操作");
        Require(Accessors.Match(session, Variant(setter, new Store(0x1000, location, parameter), new Return(0x1004)), true) == getProof.Field, "参数直接写字段");
        Require(Accessors.Match(session, Variant(setter, new Store(0x1000, location, new Binary(BinOp.Add, parameter, Expr.C(1, 32), 32)), new Return(0x1004)), true) is null, "拒绝修改参数的 setter");
        Require(Accessors.Match(session, Variant(setter, new Store(0x1000, location, parameter), new Store(0x1004, location, Expr.C(0, 32)), new Return(0x1008)), true) is null, "拒绝额外写入");
        CheckAddressPreservation(types, nativeCaller, getProof);

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("AccessorChecks", new Version(1, 0)), "AccessorChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var dataType = new TypeDefinition("Checks", "Data", TypeAttributes.Public, module.TypeSystem.Object);
        var callerType = new TypeDefinition("Checks", "Caller", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(dataType); module.Types.Add(callerType);
        var ownerMap = new Dictionary<TypeDef, TypeDefinition> { [data] = dataType, [nativeCaller.Method.Owner] = callerType };
        TypeReference Type(TypeRef type)
        {
            type = types.Underlying(type);
            if (type is DefinitionRef d && ownerMap.TryGetValue(d.Definition, out var mapped)) return mapped;
            if (ManagedTypes.IsVoid(type)) return module.TypeSystem.Void;
            return module.ImportReference(System.Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        }
        var storage = new FieldDefinition("Value", FieldAttributes.Private, module.TypeSystem.Int32);
        dataType.Fields.Add(storage);
        var receiverField = nativeCaller.Method.Owner.Fields.Single(f => f.Type == getter.DeclaringType);
        var receiverStorage = new FieldDefinition("Data", FieldAttributes.Private, dataType);
        callerType.Fields.Add(receiverStorage);
        var fields = new Dictionary<FieldDef, FieldDefinition> { [getProof.Field.Field] = storage, [receiverField] = receiverStorage };
        var methods = new Dictionary<MethodDef, MethodDefinition>();
        void Declare(MethodRef method)
        {
            var target = new MethodDefinition(method.Method.Name, MethodAttributes.Public | (method.Method.IsStatic ? MethodAttributes.Static : 0), Type(method.Method.ReturnType));
            foreach (var parameterDef in method.Method.Parameters) target.Parameters.Add(new ParameterDefinition(Type(parameterDef.Type)));
            ownerMap[method.Method.Owner].Methods.Add(target); methods.Add(method.Method, target);
        }
        Declare(getter); Declare(setter); Declare(nativeCaller);
        var writeDefinition = new MethodDef { Index = -1, Owner = nativeCaller.Method.Owner, Name = "Write", Token = 0, Slot = -1,
            Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = types.Void,
            Parameters = [new ParameterDef("receiver", getter.DeclaringType, 0, null, false), new ParameterDef("value", getter.Method.ReturnType, 0, null, false)] };
        var writeMethod = new MethodRef(writeDefinition, [], []);
        Declare(writeMethod);
        var writeBody = InlineAccessors.Recover(session, new ManagedBody(writeMethod,
            [new ManagedBlock(0x2000, [new ManagedStore(0x2000,
                new FieldValue(new ArgumentValue(0, "receiver", getter.DeclaringType, 64), getProof.Field, getter.Method.ReturnType, 32),
                new ArgumentValue(1, "value", getter.Method.ReturnType, 32)), new ManagedReturn(0x2004, null)])]));
        Require(writeBody.Accessors is [{ Proof.IsSetter: true }] && writeBody.Blocks[0].Statements[0] is ManagedCall, "跨类字段写入恢复为 setter");
        var orderedDefinition = new MethodDef { Index = -2, Owner = nativeCaller.Method.Owner, Name = "ReadThenWrite", Token = 0, Slot = -1,
            Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL,
            ReturnType = getter.Method.ReturnType, Parameters = writeDefinition.Parameters };
        var orderedMethod = new MethodRef(orderedDefinition, [], []);
        Declare(orderedMethod);
        var oldValue = new LocalValue(new Variable(Storage.Gpr(20), 1), getter.Method.ReturnType, 32);
        var fieldValue = new FieldValue(new ArgumentValue(0, "receiver", getter.DeclaringType, 64), getProof.Field, getter.Method.ReturnType, 32);
        var orderedBody = InlineAccessors.Recover(session, new ManagedBody(orderedMethod,
            [new ManagedBlock(0x3000, [new ManagedAssignment(0x3000, oldValue, fieldValue),
                new ManagedStore(0x3004, fieldValue, new ArgumentValue(1, "value", getter.Method.ReturnType, 32)), new ManagedReturn(0x3008, oldValue)])]));
        Require(orderedBody.Accessors.Count == 2, "读写顺序测试同时恢复 getter 与 setter");
        var emitter = new BodyEmitter(types, Type, f => fields[f.Field], m => methods[m.Method]);
        foreach (var body in new[] { getProof.Body, setProof.Body, recovered.Body!, writeBody, orderedBody })
            Require(emitter.Emit(body, methods[body.Method.Method]) is null, "访问器及调用者可输出 CIL");
        Require(methods[nativeCaller.Method].Body.Instructions.Any(i => i.Operand == methods[getter.Method])
            && !methods[nativeCaller.Method].Body.Instructions.Any(i => i.Operand == storage), "调用者不直接访问外部私有字段");
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray());
        var runtimeData = runtime.GetType("Checks.Data", true)!;
        var runtimeCaller = runtime.GetType("Checks.Caller", true)!;
        var instance = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(runtimeData);
        var caller = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(runtimeCaller);
        runtimeCaller.GetField("Data", SR.BindingFlags.Instance | SR.BindingFlags.NonPublic)!.SetValue(caller, instance);
        foreach (var value in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            runtimeCaller.GetMethod("Write")!.Invoke(null, [instance, value]);
            Require((int)runtimeData.GetField("Value", SR.BindingFlags.Instance | SR.BindingFlags.NonPublic)!.GetValue(instance)! == value, "真实 setter 的写入行为");
            Require((int)runtimeCaller.GetMethod("get_Attribute")!.Invoke(caller, [])! == value, "真实内联读取经 getter 调用后保持位型");
            Require((int)runtimeCaller.GetMethod("ReadThenWrite")!.Invoke(null, [instance, ~value])! == value
                && (int)runtimeCaller.GetMethod("get_Attribute")!.Invoke(caller, [])! == ~value, "访问器替换保留写入前的读取值");
        }
        Console.WriteLine("访问器证明、拒绝副作用、值类型地址保留与生成 CIL 执行通过；真实 caller/getter/setter 使用替代宿主，未验证游戏运行时");
        return 0;
    }

    private static void CheckAddressPreservation(ManagedTypes types, MethodRef caller, AccessorProof proof)
    {
        var payload = new TypeDef { Index = -1, Assembly = "Synthetic.dll", Namespace = "Synthetic", Name = "Payload", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = true, IsEnum = false, Size = 8 };
        var payloadType = new DefinitionRef(payload, []);
        var container = new FieldDef { Index = -1, Owner = proof.Field.Field.Owner, Name = "Payload", Token = 0,
            Attributes = SR.FieldAttributes.Private, Type = payloadType, Offset = 16 };
        var member = new FieldDef { Index = -2, Owner = payload, Name = "Item", Token = 0,
            Attributes = SR.FieldAttributes.Public, Type = types.Int32, Offset = 0 };
        var parent = new FieldValue(new ArgumentValue(0, "receiver", proof.Method.DeclaringType, 64), new FieldRef(container, proof.Method.DeclaringType), payloadType, 64);
        var child = new FieldValue(parent, new FieldRef(member, payloadType), types.Int32, 32);
        var lookupCount = 0;
        AccessorProof? Find(FieldValue field, bool setter, TypeDef context) { lookupCount++; return proof; }
        var store = new ManagedStore(0x1000, child, new ConstantValue(1, types.Int32, 32));
        var body = InlineAccessors.Recover(types, new ManagedBody(caller, [new ManagedBlock(0x1000, [store])]), Find);
        Require(lookupCount == 0 && body.Accessors.Count == 0 && ((ManagedStore)body.Blocks[0].Statements[0]).Target == child,
            "值类型内部写入不能用返回副本的 getter 替代地址路径");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
