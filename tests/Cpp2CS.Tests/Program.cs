using System.Numerics;
using System.Text;
using Cpp2CS.Abi;
using Cpp2CS.Import;
using Cpp2CS.IR;
using Cpp2CS.Model;

var passed = 0;
if (args is ["aggregate-abi", var aggregateAbiConfig, var aggregateAbiDirectory])
{
    AggregateAbiFixtures.Export(aggregateAbiConfig, aggregateAbiDirectory);
    return;
}
if (args is ["integer-projection" or "native-projection", var integerConfig, var integerDirectory])
{
    NativeProjectionFixtures.Export(integerConfig, integerDirectory);
    return;
}
if (args is ["namespace-inventory", var inventoryConfig, var inventoryOutput, .. var namespaces])
{
    NamespaceCorpus.Inventory(inventoryConfig, inventoryOutput, namespaces);
    return;
}
if (args is ["namespace-worker", var workerConfig, var workerAssembly, var workerOutput])
{
    NamespaceCorpus.Work(workerConfig, workerAssembly, workerOutput);
    return;
}
if (args is ["machine-effects", var effectsConfig, var effectsBinary, var effectsOutput])
{
    MachineEffectsChecks.Export(effectsConfig, effectsBinary, effectsOutput);
    return;
}
if (args is ["method-snapshot" or "method-pipeline", var snapshotConfig, var snapshotDirectory])
{
    MethodPipelineChecks.Record(snapshotConfig, snapshotDirectory, args[0] == "method-pipeline");
    return;
}
void Check(bool condition, string name)
{
    if (!condition) throw new InvalidOperationException($"FAIL: {name}");
    passed++;
    Console.WriteLine($"PASS: {name}");
}
var build = new BuildId("binary-a", "metadata-a", "aarch64-linux");
var typeId = new DefinitionId(build, 0, 0x02000001);
var methodId = new DefinitionId(build, 0, 0x06000001);
var i32 = new PrimitiveType("int", 4);
var f32 = new PrimitiveType("float", 4, true);
var typeT = new GenericParameterId(typeId, GenericOwner.Type, 0);
var methodT = new GenericParameterId(methodId, GenericOwner.Method, 0);
var context = new GenericContext(new Dictionary<GenericParameterId, TypeRef> { [typeT] = i32, [methodT] = f32 });
Check(context.Substitute(new ParameterType(typeT)) == i32 && context.Substitute(new ParameterType(methodT)) == f32, "类 T 与方法 T 不混淆");
var named = new NamedType(typeId, Sequence<TypeRef>.Of(new ParameterType(typeT)));
Check(context.Substitute(named) == new NamedType(typeId, Sequence<TypeRef>.Of(i32)), "泛型实例使用结构身份");
var unbound = new ParameterType(new(typeId, GenericOwner.Type, 1));
Check(context.Substitute(unbound) == unbound, "未绑定泛型不转换为 object");
Check(typeId != typeId with { Build = build with { BinarySha256 = "other" } }, "定义身份包含构建");
var evidence = new Evidence(EvidenceKind.Abi, "synthetic test");
var address = new NativeAddress(build, 0x100);
var bindings = new[]
{
    new MethodBinding(address, new(methodId, Sequence<TypeRef>.Of(i32), new([])), evidence),
    new MethodBinding(address, new(methodId, Sequence<TypeRef>.Of(f32), new([])), evidence)
};
var facts = new ProgramFacts(bindings, []);
Check(facts.MethodsAt(address).Count == 2, "共享机器地址保留两个方法实例");
Check(facts.LayoutOf(named, LayoutKind.UnboxedValue) is UnknownLayout, "未知泛型布局保持未知");
var catalog = new DefinitionCatalog(
    [new(typeId, "Example", "Container", TypeCategory.Class, null, Sequence<GenericParameterDefinition>.Of(new GenericParameterDefinition(typeT, "T", GenericConstraintKind.Unspecified, new([]))), evidence)],
    [],
    [new(methodId, typeId, "Convert", new(true, new ParameterType(methodT), Sequence<ParameterDefinition>.Of(new ParameterDefinition("value", new ParameterType(typeT)))),
        Sequence<GenericParameterDefinition>.Of(new GenericParameterDefinition(methodT, "T", GenericConstraintKind.Unspecified, new([]))), evidence)]);
var instantiated = catalog.Instantiate(new(methodId, Sequence<TypeRef>.Of(i32), Sequence<TypeRef>.Of(f32)));
Check(instantiated.ReturnType == f32 && instantiated.Parameters[0].Type == i32, "托管签名实例化分别绑定类与方法泛型");
var unboxed = new TypeLayout(named, LayoutKind.UnboxedValue, 8, 8, 0, new([]), evidence);
var boxed = new TypeLayout(named, LayoutKind.BoxedObject, 24, 8, 16, new([]), evidence);
var layoutFacts = new ProgramFacts([], [unboxed, boxed]);
Check(layoutFacts.LayoutOf(named, LayoutKind.UnboxedValue) == new KnownLayout(unboxed) && layoutFacts.LayoutOf(named, LayoutKind.BoxedObject) == new KnownLayout(boxed), "装箱与未装箱布局分别查询");

var region = new RegionId("frame", RegionKind.Stack);
var slot = new StorageAddress(region, 0);
var value = new InputBits("aggregate", 128);
var initial = new MemoryState("initial");
var stored = initial.Store("store", slot, value);
Check(stored.Load(slot, 16) == value, "结构体字节可无损重组");
Check(initial.Load(slot, 16) != value, "存储快照不可变");
var changed = stored.Store("partial", slot with { Offset = 8 }, BitOps.Constant(0x1234, 16));
Check(changed.Load(slot, 8) == BitOps.Slice(value, 0, 64), "部分覆盖保留前八字节");
Check(changed.Load(slot with { Offset = 8 }, 2) == BitOps.Constant(0x1234, 16), "部分覆盖写入两字节");
Check(changed.Load(slot with { Offset = 10 }, 6) == BitOps.Slice(value, 80, 48), "部分覆盖保留剩余字节");
Check(stored.Invalidate("call").Load(slot, 16) != value, "未知别名写入使旧存储失效");
var merged = MemoryState.Merge("join", stored, changed);
Check(merged.Load(slot, 8) == BitOps.Slice(value, 0, 64) && merged.Load(slot with { Offset = 8 }, 1) is PhiBits, "内存合流只改变分歧字节");
// 独立 byte[] 参考检查所有写入范围，不复用 IR 的切片算法。
var random = new Random(12345);
for (var start = 0; start < 16; start++)
for (var size = 1; size <= 16 - start; size++)
{
    var expected = new byte[16];
    random.NextBytes(expected);
    var memory = initial.Store("base", slot, BitOps.Constant(new BigInteger(expected, isUnsigned: true), 128));
    var replacement = new byte[size];
    random.NextBytes(replacement);
    replacement.CopyTo(expected, start);
    memory = memory.Store("patch", slot with { Offset = start }, BitOps.Constant(new BigInteger(replacement, isUnsigned: true), size * 8));
    if (memory.Load(slot, 16) is not ConstantBits c || c.Value != new BigInteger(expected, isUnsigned: true))
        throw new InvalidOperationException($"字节对照失败：{start}/{size}");
}
Check(true, "136 种部分写入与独立 byte[] 参考一致");

CallLayout Layout(AbiShape result, params AbiShape[] arguments) => Aapcs64.Classify(new(new(arguments), result, evidence)).Layout!;
string Reg(AbiValue argument, int index = 0) => ((RegisterLocation)argument.Pieces[index].Location).Name;
var floating = Layout(AbiShape.Void, AbiShape.Float(4), AbiShape.Float(8), AbiShape.Integer());
Check(Reg(floating.Arguments[0]) == "V0" && Reg(floating.Arguments[1]) == "V1" && Reg(floating.Arguments[2]) == "X0", "浮点与整数参数使用独立寄存器序列");
var pair = Layout(AbiShape.Composite(16), AbiShape.Integer(), AbiShape.Composite(16, 16));
Check(Reg(pair.Arguments[1]) == "X2" && Reg(pair.Arguments[1], 1) == "X3", "16 字节对齐参数跳过奇数寄存器");
Check(Reg(pair.Return) == "X0" && Reg(pair.Return, 1) == "X1", "双寄存器返回完整分类");
Check(Reg(Layout(AbiShape.Composite(24)).Return) == "X8", "大结构体返回使用 X8");
var indirect = Layout(AbiShape.Void, AbiShape.Composite(24));
Check(indirect.Arguments[0].Indirect && indirect.Arguments[0].Pieces[0].Size == 8, "大结构体参数显式传地址");
var hfa = Layout(AbiShape.Hfa(8, 3));
Check(hfa.Return.Pieces.Count == 3 && Reg(hfa.Return, 2) == "V2", "HFA 返回使用向量寄存器");
var spilled = Layout(AbiShape.Void, [.. Enumerable.Repeat(AbiShape.Integer(), 7), AbiShape.Composite(16), AbiShape.Integer()]);
Check(spilled.Arguments[7].Pieces[0].Location is StackLocation { Offset: 0 } && spilled.Arguments[8].Pieces[0].Location is StackLocation { Offset: 16 }, "聚合寄存器不足时整体上栈");
Check(!Aapcs64.Classify(new(new([]), AbiShape.Unknown, evidence)).IsSupported, "未知返回布局阻止 ABI 猜测");
Check(!Aapcs64.Classify(new(new([]), AbiShape.Void, evidence, true)).IsSupported, "可变参数显式不支持");

var registers = new RegisterState("entry").Set("X0", new InputBits("receiver", 64)).Set("X1", new InputBits("old-x1", 64))
    .Set("X19", new InputBits("saved", 64)).Set("V8", new InputBits("saved-v8", 128));
var call = new CallSite("call-1", address, new InputBits("target", 64), new(bindings), registers, stored, slot);
Check(registers.WriteW(1, BitOps.Constant(17, 32)).Read("X1") == BitOps.Constant(17, 64), "W 写入清零 X 高 32 位");
var hfaSpill = Layout(AbiShape.Void, [.. Enumerable.Repeat(AbiShape.Float(8), 7), AbiShape.Hfa(4, 2), AbiShape.Float(4)]);
Check(hfaSpill.Arguments[7].Pieces[0].Location is StackLocation { Offset: 0 } && hfaSpill.Arguments[8].Pieces[0].Location is StackLocation { Offset: 8 }, "HFA 不拆分到寄存器与栈，后续浮点继续上栈");
var outcome = CallTransfer.Apply(call, Layout(AbiShape.Composite(16), AbiShape.Integer(), AbiShape.Integer()), CallEffects.Unknown);
Check(outcome.Arguments[1].Value == registers.Read("X1"), "调用参数读取调用前状态");
Check(outcome.NormalRegisters!.Read("X1") == BitOps.Slice(outcome.ReturnValue!, 64, 64), "调用后 X1 来自新返回值");
Check(outcome.NormalRegisters.Read("X19") == registers.Read("X19"), "被调用者保存整数寄存器");
Check(outcome.ExceptionalRegisters!.Read("X0") is InputBits { Identity: var exceptionId } && exceptionId.EndsWith(":exception-object") &&
    outcome.ExceptionalRegisters.Read("X1") != outcome.NormalRegisters.Read("X1"), "异常入口不能接收正常返回的 source/token");
Check(outcome.ExceptionalRegisters!.Read("X19") == registers.Read("X19"), "异常状态保留 callee-saved 寄存器");
Check(BitOps.Slice(outcome.NormalRegisters.Read("V8"), 0, 64) == BitOps.Slice(registers.Read("V8"), 0, 64) &&
    BitOps.Slice(outcome.NormalRegisters.Read("V8"), 64, 64) != BitOps.Slice(registers.Read("V8"), 64, 64), "V8 仅低 64 位保存");
Check(outcome.ExceptionalMemory is not null && outcome.NormalMemory!.Load(slot, 16) != value, "未知调用保留异常并破坏存储");
var unknown = CallTransfer.Apply(call, null, CallEffects.Unknown);
Check(unknown.Unresolved is not null && unknown.NormalRegisters!.Read("X1") != registers.Read("X1") && unknown.Source.Before == registers, "未知调用保留原始输入且不沿用旧返回寄存器");
var noReturn = CallTransfer.Apply(call, null, new(true, true, true));
Check(noReturn.NormalRegisters is null && noReturn.ExceptionalMemory is not null, "noreturn 不等于不能抛异常");
var returnBuffer = CallTransfer.Apply(call, Layout(AbiShape.Composite(24)), new(false, false, false));
Check(returnBuffer.Unresolved is not null && returnBuffer.NormalMemory!.Load(slot, 16) != value, "未解析返回缓冲不猜测存储位置");
var entry = new BlockId("entry");
var normal = new BlockId("normal");
var exceptional = new BlockId("exceptional");
var graph = new ControlFlowGraph(entry,
[
    new(entry, new([]), new Invoke(new(call, CallEffects.Unknown, evidence), normal, exceptional)),
    new(normal, new([]), new Return(null)),
    new(exceptional, new([]), new Throw(new InputBits("exception", 64)))
]);
Check(graph.Reachable().Count == 3, "可达性保留异常分支");
using var json = new MemoryStream(Encoding.UTF8.GetBytes("""
{"ScriptMethod":[{"Address":256,"Name":"A<int>","Signature":"void A();"},{"Address":256,"Name":"A<float>"}],"ScriptMetadata":[{"Address":512,"Name":"A_TypeInfo"}]}
"""));
var imported = DumperSymbols.Read(json, build);
Check(imported.Methods.Count == 2 && imported.Methods[0].Address == imported.Methods[1].Address, "Dumper 导入保留同地址候选");
NativeChecks.Run(Check);
MachineEffectsChecks.Run(Check);
ArithmeticArrayChecks.Run(Check);
IntegerProjectionChecks.Run(Check);
RuntimeTypeChecks.Run(Check);
DelegateCacheChecks.Run(Check);
LambdaChecks.Run(Check);
AsyncChecks.Run(Check);
AwaitSiteChecks.Run(Check);
FinallyChecks.Run(Check);
SharedBodyChecks.Run(Check);
NamespaceCorpusChecks.Run(Check);
if (args is ["native-layout", var compiler]) AsyncChecks.Layouts(Check, compiler);
if (args is ["runtime-types-native", var runtimeTypesConfig]) RuntimeTypeChecks.Native(Check, runtimeTypesConfig);
if (args is ["ssa-construction-native", var ssaConstructionConfig]) SsaConstructionChecks.Native(Check, ssaConstructionConfig);
if (args is ["async-native", var config]) SsaRecoveryChecks.Run(Check, config);
if (args is ["multi-await-native", var multiConfig]) AwaitSiteChecks.Native(Check, multiConfig);
if (args is ["async-body-native", var bodyConfig]) AsyncBodyChecks.Run(Check, bodyConfig);
if (args is ["constructors-native", var ctorConfig]) NativeChecks.Constructors(Check, ctorConfig);
if (args is ["exceptions-native", var exceptionConfig]) NativeChecks.ExceptionBoundaries(Check, exceptionConfig);
if (args is ["arithmetic-native", var arithmeticConfig]) ArithmeticArrayChecks.Native(Check, arithmeticConfig);
if (args is ["aggregate-native", var aggregateConfig]) AggregateChecks.Native(Check, aggregateConfig);
if (args is ["complex-async-native", var complexConfig]) ComplexAsyncChecks.Native(Check, complexConfig);
if (args is ["delegates-native", var delegateConfig]) DelegateCacheChecks.Native(Check, delegateConfig);
if (args is ["lambdas-native", var lambdaConfig]) LambdaChecks.Native(Check, lambdaConfig);
if (args is ["closures-native", var closureConfig]) ClosureChecks.Native(Check, closureConfig);
if (args is ["closure-scopes-native", var scopeConfig]) ClosureScopeChecks.Native(Check, scopeConfig);
if (args is ["call-storage-native", var storageConfig]) CallStorageChecks.Native(Check, storageConfig);
if (args is ["finally-native", var finallyConfig]) FinallyChecks.Native(Check, finallyConfig);
if (args is ["call-arguments-native", var argumentConfig]) CallArgumentChecks.Native(Check, argumentConfig);
Console.WriteLine($"PASS: {passed} checks; 136 independent byte-range cases");
