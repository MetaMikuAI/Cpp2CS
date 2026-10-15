using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Runtime;
using Mono.Cecil;
using Convert = System.Convert;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

internal static class RuntimeValueCheck
{
    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        var owner = new TypeDef { Index = -1, Assembly = "RuntimeChecks.dll", Namespace = "Checks", Name = "Harness", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var strings = new ArrayRef(types.String, 1);
        var ints = new ArrayRef(types.Int32, 1);
        var nonVector = ints with { IsVector = false };
        Require(nonVector != ints && ((ArrayRef)nonVector.Substitute([], [])).IsVector == false, "SZARRAY 与 rank=1 ARRAY 不可合并");
        var objects = new ArrayRef(types.Object, 1);
        MethodRef Method(string name, TypeRef result, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result,
            Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
        }, [], []);
        PreparedMethod Prepare(MethodRef method, params Stmt[] statements) => new(method, session.Abi.ClassifyReturn(method.Method.ReturnType, out _),
            new MachineFunction { Entry = 0x1000, Range = new FunctionRange(0x1000, 0x1100, BoundaryEvidence.SymbolCandidate, "合成检查"),
                Blocks = [new Block(0x1000) { Statements = [.. statements] }] }, null, []);
        Use Input(int index, int width = 64) => new(new Variable(Storage.Gpr(index), 0), width);
        var metadataAddress = new Variable(Storage.Gpr(10), 1);
        var metadataValue = new Variable(Storage.Gpr(11), 1);
        var allocated = new Variable(Storage.Gpr(0), 1);
        var arraySlot = session.Model.Image.RelocatedPointer(0xb6e8318);
        Require(arraySlot is { } && session.Model.UsageAt(arraySlot.Value) is { Kind: UsageKind.TypeInfo, Value: ArrayRef slotArray } && slotArray == strings,
            "真实重定位和元数据必须共同确认 string[] 类型");
        Require(session.Resolver.Resolve(0x49c868c) is HelperCallee { Helper.Kind: HelperKind.NewArray }, "数组辅助函数身份");
        Stmt[] Metadata() => [new Define(0x1000, metadataAddress, new Load(Expr.C(0xb6e8318, 64), 64)),
            new Define(0x1004, metadataValue, new Load(new Use(metadataAddress, 64), 64))];
        var allocation = new Call(0x1008, CallKind.Direct, Expr.C(0x49c868c, 64))
        {
            Sources = [Storage.Gpr(0), Storage.Gpr(1)], Arguments = [new Use(metadataValue, 64), Input(0)],
            Results = [Storage.Gpr(0)], Defines = [allocated],
        };
        var create = Prepare(Method("Create", strings, types.Int64), [.. Metadata(), allocation, new Return(0x100c) { Value = new Use(allocated, 64) }]);
        var references = new MetadataReferences(session.Model, create.Function);
        Require(references.IsRuntimeReference(metadataAddress) && references.IsRuntimeReference(metadataValue), "槽位地址和类型信息不作为 CLR 对象输出");
        Require(references.Usage(new Use(metadataAddress, 64)) is null && references.Usage(new Use(metadataValue, 64))?.Value is ArrayRef,
            "槽位地址不等于槽位内容");
        Require(references.Usage(new Load(Expr.C(arraySlot!.Value, 64), 32)) is null, "窄读取不能解析成元数据指针");
        Require(references.Usage(Expr.C(arraySlot.Value, 64)) is null, "常量地址不等于元数据内容");
        var wrong = allocation with { Arguments = [new Load(new Load(Expr.C(0xb737490, 64), 64), 64), Input(0)] };
        Require(new ValueRecovery(session, create).HelperValue(wrong, out _) is null, "普通类型不能冒充数组类型");
        Require(new ValueRecovery(session, create).HelperValue(allocation with { Arguments = [Expr.C(0, 64), Input(0)] }, out _) is null,
            "未知类型不能生成数组");
        Require(BodyRecovery.Recover(session, Prepare(Method("MissingLength", types.Void), [.. Metadata(),
            allocation with { Sources = [Storage.Gpr(0)], Arguments = [new Use(metadataValue, 64)] }, new Return(0x100c)])).Body is null,
            "缺少分配参数不能静默删去调用");
        var escaped = Prepare(Method("EscapedMetadata", types.Object), [.. Metadata(), new Return(0x1008) { Value = new Use(metadataValue, 64) }]);
        Require(BodyRecovery.Recover(session, escaped).Body is null, "元数据类指针不能作为普通对象返回");
        var other = new Variable(Storage.Gpr(12), 1);
        var merged = new Variable(Storage.Gpr(13), 1);
        var samePhi = Prepare(Method("MetadataPhi", types.Void), [.. Metadata(),
            new Define(0x1008, other, new Load(Expr.C(arraySlot.Value, 64), 64)), new Phi(0x100c, merged, [metadataValue, other])]);
        Require(new MetadataReferences(session.Model, samePhi.Function).IsRuntimeReference(merged), "相同元数据的汇合保持身份");
        var differentPhi = Prepare(Method("DifferentPhi", types.Void), [.. Metadata(),
            new Define(0x1008, other, new Load(new Load(Expr.C(0xb737490, 64), 64), 64)), new Phi(0x100c, merged, [metadataValue, other])]);
        Require(!new MetadataReferences(session.Model, differentPhi.Function).IsRuntimeReference(merged), "不同类型的汇合不能选取其中一侧");
        var badLoad = new ValueRecovery(session, Prepare(Method("Bad", types.Int32, ints)));
        Require(badLoad.Recover(new Load(new Binary(BinOp.Add, Input(0), Expr.C(32, 64), 64), 16), out _) is null,
            "数组元素的部分读取不能冒充整个元素");
        Require(badLoad.Location(new Binary(BinOp.Add, Input(0), Expr.C(24, 64), 64), 64, out _) is null,
            "数组长度不能作为可写位置");
        var md = new ValueRecovery(session, Prepare(Method("NonVector", types.UInt64, nonVector)));
        Require(md.Recover(new Load(new Binary(BinOp.Add, Input(0), Expr.C(24, 64), 64), 64), out _) is null,
            "普通 ARRAY 不能套用 SZARRAY 恢复规则");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("RuntimeChecks", new Version(1, 0)), "RuntimeChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(host);
        TypeReference Reference(TypeRef type) => type is ArrayRef a ? Skeleton.ArrayReference(a, Reference(a.Element))
            : type == types.String ? module.TypeSystem.String : type == types.Object ? module.TypeSystem.Object
            : module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var emitter = new BodyEmitter(types, Reference, f => throw new NotSupportedException(f.ToString()), m => throw new NotSupportedException(m.ToString()));
        void EmitBody(ManagedBody body)
        {
            var method = new MethodDefinition(body.Method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(body.Method.Method.ReturnType));
            foreach (var parameter in body.Method.Method.Parameters) method.Parameters.Add(new ParameterDefinition(Reference(parameter.Type)));
            host.Methods.Add(method);
            var problem = emitter.Emit(body, method);
            Require(problem is null, problem ?? "CIL 输出");
        }
        void Emit(PreparedMethod prepared)
        {
            var recovered = BodyRecovery.Recover(session, prepared);
            Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
            EmitBody(recovered.Body!);
        }
        Emit(create);
        Emit(Prepare(Method("Unused", types.Void, types.Int64), [.. Metadata(), allocation, new Return(0x100c)]));
        Emit(Prepare(Method("TailCreate", strings, types.Int64), [.. Metadata(), allocation with { Kind = CallKind.Tail, Defines = [], Results = [] }]));
        foreach (var element in new TypeRef[] { types.Int32, types.Object, types.Single })
        {
            var array = new ArrayRef(element, 1);
            var size = types.Size(element);
            var index = new Cpp2CS.Ir.Convert(ConvKind.SignExtend, Input(1, 32), 64);
            var address = new Binary(BinOp.Add, new Binary(BinOp.Add, Input(0), Expr.C(32, 64), 64),
                new Binary(BinOp.Mul, index, Expr.C((ulong)size, 64), 64), 64);
            var previous = new Variable(Storage.Temp(0), 1);
            var value = element == types.Single ? new Use(new Variable(Storage.Vec(0), 0), 32) : Input(2, size * 8);
            Emit(Prepare(Method("Exchange" + element, element, array, types.Int32, element),
                new Define(0x1000, previous, new Load(address, size * 8)), new Store(0x1004, address, value),
                new Return(0x1008) { Value = new Use(previous, size * 8) }));
        }
        Emit(Prepare(Method("Length", types.UInt64, ints), new Return(0x1000)
            { Value = new Load(new Binary(BinOp.Add, Input(0), Expr.C(24, 64), 64), 64) }));
        var text = "空\0白\n\"路径\\\ud83d\ude80\ud800";
        EmitBody(new(Method("Literal", types.String), [new ManagedBlock(0x1000, [new ManagedReturn(0x1000, new StringValue(text, types.String))])]));
        EmitBody(new(Method("NonVectorNull", nonVector), [new ManagedBlock(0x1000, [new ManagedReturn(0x1000, new ConstantValue(0, nonVector, 64))])]));
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
        Require(!runtime.GetMethod("NonVectorNull")!.ReturnType.IsSZArray && runtime.GetMethod("Create")!.ReturnType.IsSZArray,
            "CLR 回读仍区分两种单维数组签名");
        object? Invoke(string name, params object?[] arguments) => runtime.GetMethod(name)!.Invoke(null, arguments);
        foreach (var length in new[] { 0L, 1L, 4L })
            foreach (var name in new[] { "Create", "TailCreate" })
            {
                var created = (string?[])Invoke(name, length)!;
                Require(created.Length == length && created.All(v => v is null), "分配长度和默认元素");
                Require(!ReferenceEquals(created, Invoke(name, length)), "每次分配产生独立数组");
            }
        foreach (var name in new[] { "Create", "TailCreate", "Unused" }) Fault<OverflowException>(() => Invoke(name, -1L));
        var integers = new[] { int.MinValue, 0, int.MaxValue };
        Require((int)Invoke("Exchangeint", integers, 0, 13)! == int.MinValue && integers[0] == 13, "读取必须发生在原写入之前");
        Require((ulong)Invoke("Length", integers)! == 3 && (ulong)Invoke("Length", Array.Empty<int>())! == 0, "数组长度");
        Fault<IndexOutOfRangeException>(() => Invoke("Exchangeint", integers, -1, 0));
        Fault<IndexOutOfRangeException>(() => Invoke("Exchangeint", integers, 3, 0));
        Fault<NullReferenceException>(() => Invoke("Exchangeint", null, 0, 0));
        Fault<NullReferenceException>(() => Invoke("Length", [null]));
        var shared = new object(); var objectArray = new object?[] { shared };
        Require(ReferenceEquals(Invoke("Exchangeobject", objectArray, 0, null), shared) && objectArray[0] is null, "引用身份和空值写入");
        object[] covariant = new[] { "before" };
        Require((string)Invoke("Exchangeobject", covariant, 0, "after")! == "before" && (string)covariant[0] == "after", "协变数组有效读写");
        Fault<ArrayTypeMismatchException>(() => Invoke("Exchangeobject", covariant, 0, new object()));
        foreach (var bits in new[] { 0, unchecked((int)0x80000000), 1, 0x7f800000, 0x7fc12345 })
        {
            var floats = new[] { BitConverter.Int32BitsToSingle(bits) };
            Require(BitConverter.SingleToInt32Bits((float)Invoke("Exchangefloat", floats, 0, 1f)!) == bits && floats[0] == 1f, "浮点数组保持原始位型");
        }
        Require((string)Invoke("Literal")! == text && ReferenceEquals(Invoke("Literal"), Invoke("Literal")), "字符串 UTF-16 内容和驻留身份");
        Console.WriteLine("运行时值检查通过：元数据重定位、数组分配与尾调用、长度、元素读写、读取顺序、协变检查、异常和字符串位型");
        Native(session);
        GenericTargets(session);
        return 0;
    }

    private static void GenericTargets(RecoverySession session)
    {
        var method = session.Model.Code[0x57a3694].Single().Method;
        var prepared = session.Analyze(method, method.Method.Address);
        var values = new ValueRecovery(session, prepared);
        var calls = prepared.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
            .Where(c => c.Target is Const { Value: 0x702af74 }).ToArray();
        Require(calls.Length == 2, "真实样本包含两次共享泛型调用");
        var expected = new[] { 0xb740ad8UL, 0xb740ad0UL }.Select(slot =>
            (MethodRef)session.Model.UsageAt(session.Model.Image.RelocatedPointer(slot)!.Value)!.Value).ToArray();
        for (var i = 0; i < calls.Length; i++)
        {
            var resolved = values.Invocation(calls[i], out var problem);
            Require(resolved?.Method == expected[i] && resolved.Method.MethodArguments.Single() != session.Types.Object,
                problem ?? "具体实参必须来自调用处的 MethodInfo");
        }
        Require(expected[0] != expected[1], "同一原生目标的两个调用应保留不同泛型实参");
        var unrelated = new MethodRef(new MethodDef { Index = -1, Owner = method.Method.Owner, Name = "Unrelated", Token = 0, Slot = -1,
            Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL,
            ReturnType = session.Types.Void, Parameters = expected[0].Method.Parameters }, [], []);
        Require(CallTargets.Resolve(calls[0], new ManagedCallee([new CodeOwner(unrelated, false)], null), session.Abi, values.Metadata) is null,
            "MethodInfo 与目标定义不符时不能退回猜测");
        var wrongKind = calls[0] with { Arguments = [calls[0].Arguments[0], new Load(new Load(Expr.C(0xb6e8318, 64), 64), 64)] };
        Require(CallTargets.Resolve(wrongKind, (ManagedCallee)session.Resolver.Resolve(calls[0])!, session.Abi, values.Metadata) is null,
            "类型元数据不能冒充方法元数据");
        var missingInfo = calls[0] with { Arguments = [calls[0].Arguments[0], Expr.C(0, 64)] };
        Require(CallTargets.Resolve(missingInfo, (ManagedCallee)session.Resolver.Resolve(calls[0])!, session.Abi, values.Metadata) is null,
            "缺少 MethodInfo 时不能把共享登记实例当成真实泛型实参");
        Console.WriteLine($"共享泛型目标检查通过：{expected[0]}；{expected[1]}；不匹配的元数据拒绝");
    }

    private static void Native(RecoverySession session)
    {
        var types = session.Types;
        var slash = session.Model.Code[0x55d2ac4].Single().Method;
        var file = new MethodRef(slash.Method.Owner.Methods.Single(m => m.Name == "GetFileCombinePath"), [], []);
        var content = session.Model.Code[0x5acb814].Single().Method;
        Require(slash.ToString() == "Sekai.Mysekai.PathUtility.GetSlashCombinePath"
            && content.ToString() == "Sekai.Mysekai.ScreenLayerMysekaiCanvas.get_ContentListTypes", "真实方法身份");
        var element = (DefinitionRef)((ArrayRef)content.Method.ReturnType).Element;
        Require(element.Definition.IsEnum && types.Size(element) == 4
            && Convert.ToInt32(element.Definition.Fields.Single(f => f.Name == "Member").Constant) == 13, "枚举元数据与原生写入的 0xd 一致");
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeRuntimeChecks", new Version(1, 0)), "NativeRuntimeChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Native", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(host);
        var enumType = new TypeDefinition("Checks", "ContentListType", TypeAttributes.Public | TypeAttributes.Sealed, module.ImportReference(typeof(Enum)));
        enumType.Fields.Add(new FieldDefinition("value__", FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName, module.TypeSystem.Int32));
        enumType.Fields.Add(new FieldDefinition("Member", FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault, enumType) { Constant = 13 });
        module.Types.Add(enumType);
        TypeReference Reference(TypeRef type) => type == element ? enumType : type is ArrayRef array ? new ArrayType(Reference(array.Element))
            : type == types.String ? module.TypeSystem.String : throw new NotSupportedException(type.ToString());
        var methods = new Dictionary<MethodDef, MethodDefinition>();
        foreach (var source in new[] { slash, file, content })
        {
            var definition = new MethodDefinition(source.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(source.Method.ReturnType));
            foreach (var parameter in source.Method.Parameters) definition.Parameters.Add(new ParameterDefinition(Reference(parameter.Type)));
            methods.Add(source.Method, definition); host.Methods.Add(definition);
        }
        MethodReference Called(MethodRef method)
        {
            if (methods.TryGetValue(method.Method, out var defined)) return defined;
            if (method.Method.Address == 0xa2cc088 && method.Method.Owner.FullName == "System.IO.Path" && method.Method.Name == "Combine")
                return module.ImportReference(typeof(Path).GetMethod(nameof(Path.Combine), [typeof(string[])]));
            if (method.Method.Address == 0xa1c5924 && method.Method.Owner.FullName == "System.String" && method.Method.Name == "Replace")
                return module.ImportReference(typeof(string).GetMethod(nameof(string.Replace), [typeof(string), typeof(string)]));
            throw new NotSupportedException(method.ToString());
        }
        var emitter = new BodyEmitter(types, Reference, f => throw new NotSupportedException(f.ToString()), Called);
        foreach (var source in new[] { slash, file, content })
        {
            var recovered = BodyRecovery.Recover(session, session.Analyze(source, source.Method.Address));
            Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
            var problem = emitter.Emit(recovered.Body!, methods[source.Method]);
            Require(problem is null, problem ?? "真实方法输出");
        }
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Native", true)!;
        var paths = runtime.GetMethod(file.Method.Name)!;
        foreach (var input in new[] { Array.Empty<string>(), new[] { "one" }, new[] { "a", "b", "c" }, new[] { "a\\b", "c" }, new[] { "空白", "路径" } })
        {
            var actual = (string)paths.Invoke(null, [input])!;
            Require(actual == Path.Combine(input).Replace("\\", "/"), "两个真实恢复方法串联，BCL 提供路径组合和字符串替换");
        }
        Fault<ArgumentNullException>(() => paths.Invoke(null, [null]));
        var create = runtime.GetMethod(content.Method.Name)!;
        var first = (Array)create.Invoke(null, null)!;
        var second = (Array)create.Invoke(null, null)!;
        Require(first.Length == 1 && Convert.ToInt32(first.GetValue(0)) == 13 && !ReferenceEquals(first, second), "真实方法分配并初始化枚举数组");
        first.SetValue(Enum.ToObject(first.GetType().GetElementType()!, 99), 0);
        Require(Convert.ToInt32(second.GetValue(0)) == 13, "真实方法的多次分配互不影响");
        Console.WriteLine($"真实方法执行通过：GetFileCombinePath 0x{file.Method.Address:x} → GetSlashCombinePath 0x55d2ac4；ContentListTypes 0x5acb814；未加载 Unity，路径库使用当前 CLR");
    }

    private static void Fault<T>(Func<object?> action) where T : Exception
    {
        var task = Task.Run(action);
        Task.WhenAny(task).GetAwaiter().GetResult();
        Require(task.Exception?.InnerException is SR.TargetInvocationException { InnerException: T }, typeof(T).Name);
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
