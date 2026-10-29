using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

/// <summary>严格认回的反例：额外操作、可覆写方法、不同位宽和不同初始化类型不得通过。</summary>
internal static class FieldAccessorCheck
{
    [Command("accessor-rules", "F9 严格形态与权限反例", Arguments = "<binary> <metadata>")]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var a = new Assertions();
        TypeDef Owner(int index) => new() { Index = index, Assembly = "F9.Tests.dll", Namespace = "Tests", Name = "Subject" + index,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var owner = Owner(-1);
        var caller = Owner(-2);
        var ownerType = new DefinitionRef(owner, []);
        var receiver = new ArgumentValue(-1, ownerType, 64);
        var parameter = new ArgumentValue(0, types.Int32, 32);
        var field = new FieldDef { Index = -1, Owner = owner, Name = "value", Token = 0, Type = types.Int32, Offset = 16, Attributes = FieldAttributes.Private };
        var read = new FieldValue(receiver, new FieldRef(field, ownerType), types.Int32, 32);
        var local = new LocalValue(new Variable(Storage.Gpr(0), 1), types.Int32, 32);
        MethodRef Method(bool write, MethodAttributes attributes = MethodAttributes.Public, TypeDef? declaring = null) => new(new MethodDef
        {
            Index = -1, Owner = declaring ?? owner, Name = write ? "set_Value" : "get_Value", Token = 0, Attributes = attributes, ImplAttributes = 0, Slot = -1,
            ReturnType = write ? types.Corlib("System.Void") : types.Int32, Parameters = write ? [new("value", types.Int32, 0, null, false)] : [],
        }, [], []);
        ManagedBody Body(MethodRef m, params ManagedStatement[] statements) => new(m, [new(0, statements)]);
        var getter = Method(false);
        var setter = Method(true);
        var get = Body(getter, new ManagedReturn(0, read));
        var set = Body(setter, new ManagedStore(0, read, parameter), new ManagedReturn(1, null));
        var recognized = FieldAccessor.Recognize(get, false, types)!;
        a.True(recognized is not null, "单次实例读取");
        a.True(FieldAccessor.Recognize(set, true, types) is not null, "单次实例写入");
        a.True(FieldAccessor.Recognize(Body(getter, new ManagedAssignment(0, local, read), new ManagedReturn(1, local)), false, types) is not null, "局部复制保留单次读取");
        var wide = new LocalValue(local.Variable, types.UInt64, 64);
        var extended = new ManagedAssignment(0, wide, new ConversionValue(ConvKind.ZeroExtend, read, types.UInt64, 64));
        a.True(FieldAccessor.Recognize(Body(getter, extended, new ManagedReturn(1,
            new ConversionValue(ConvKind.Truncate, wide, types.UInt32, 32))), false, types) is not null, "跨局部变量的 W/X 寄存器往返");
        a.True(FieldAccessor.Recognize(Body(getter, extended, new ManagedReturn(1,
            new ConversionValue(ConvKind.Truncate, wide, types.UInt16, 16))), false, types) is null, "截断丢失字段高位不能认回");
        foreach (var body in new[]
        {
            Body(getter, new ManagedAssignment(0, local, read), new ManagedReturn(1, read)),
            Body(getter, new ManagedReturn(0, read with { Width = 64 })),
            Body(getter, new ManagedReturn(0, read with { Type = types.UInt32 })),
            Body(getter, new ManagedReturn(0, new BinaryValue(BinOp.Add, read, new ConstantValue(1, types.Int32, 32), types.Int32, 32))),
            Body(getter, new ManagedCall(0, new(getter, receiver, [], false), local, false), new ManagedReturn(1, read)),
            Body(getter, new ManagedBranch(0, new ConstantValue(1, types.Boolean, 1), new(0, []), new(0, []))),
            Body(Method(false, MethodAttributes.Public | MethodAttributes.Virtual), new ManagedReturn(0, read)),
        }) a.True(FieldAccessor.Recognize(body, false, types) is null, "拒绝额外读/算术/调用/分支/可覆写方法或类型位宽不符");
        a.True(FieldAccessor.Recognize(Body(Method(false, MethodAttributes.Public | MethodAttributes.Virtual | MethodAttributes.Final), new ManagedReturn(0, read)), false, types) is not null, "final 可直接调用");
        a.True(FieldAccessor.Recognize(Body(setter, new ManagedStore(0, read, parameter), new ManagedStore(1, read, parameter), new ManagedReturn(2, null)), true, types) is null, "拒绝两次写入");
        a.True(FieldAccessor.Recognize(Body(setter, new ManagedStore(0, read, new ConstantValue(0, types.Int32, 32)), new ManagedReturn(1, null)), true, types) is null, "setter 必须原样写入参数");
        a.True(recognized!.Matches(types, caller, read, false), "public getter 可替代 private 字段读取");
        var privateGetter = FieldAccessor.Recognize(Body(Method(false, MethodAttributes.Private), new ManagedReturn(0, read)), false, types)!;
        a.True(!privateGetter.Matches(types, caller, read, false), "拒绝调用不可访问 getter");
        a.True(!recognized.Matches(types, caller, read with { Width = 64 }, false), "调用点位宽必须一致");
        a.True(!recognized.Matches(types, caller, read, true), "getter 不能用于写入");
        var staticField = new FieldDef { Index = -2, Owner = owner, Name = "staticValue", Type = types.Int32, Offset = 0, Attributes = FieldAttributes.Private | FieldAttributes.Static };
        var staticRead = new StaticFieldValue(new FieldRef(staticField, ownerType), types.Int32, 32);
        var staticGet = Method(false, MethodAttributes.Public | MethodAttributes.Static);
        var staticSet = Method(true, MethodAttributes.Public | MethodAttributes.Static);
        a.True(FieldAccessor.Recognize(Body(staticGet, new ManagedReturn(0, staticRead)), false, types) is not null, "静态 getter");
        a.True(FieldAccessor.Recognize(Body(staticSet, new ManagedStore(0, staticRead, parameter), new ManagedReturn(1, null)), true, types) is not null, "静态 setter");
        a.True(FieldAccessor.Recognize(Body(Method(false, MethodAttributes.Public | MethodAttributes.Static, caller), new ManagedReturn(0, staticRead)), false, types) is null, "拒绝改变类初始化对象的跨类型静态访问器");
        a.True(FieldAccessor.Recognize(Body(getter, new ManagedReturn(0, staticRead)), false, types) is null, "实例 getter 不能冒充静态 getter");
        var choice = new ChoiceValue(new ConstantValue(0, types.Boolean, 1), read, new ConstantValue(0, types.Int32, 32), types.Int32, 32);
        var rewritten = AccessorRewriter.Rewrite(Body(getter, new ManagedReturn(0, choice)), (v, w) => v == read && !w ? recognized : null);
        a.True(rewritten.Blocks[0].Statements is [ManagedReturn { Value: ChoiceValue { True: FieldValue { Accessor: not null } } }], "getter 留在条件表达式原求值位置");
        var edge = new ManagedEdge(1, [new(local, read)]);
        var branch = new ManagedBranch(0, new ComparisonValue(Cond.Eq, read, parameter, types.Boolean), edge, new(2, []));
        var edgeRead = AccessorRewriter.Rewrite(Body(getter, branch), (v, w) => v == read && !w ? recognized : null);
        a.True(edgeRead.Blocks[0].Statements is [ManagedBranch { Condition: ComparisonValue { Left: FieldValue { Accessor: not null } },
            Taken.Copies: [{ Value: FieldValue { Accessor: not null } }], Fallthrough.Copies.Count: 0 }], "条件与边复制分别在原位置读取，不提前执行另一条边");
        var valueOwner = (DefinitionRef)types.Int32;
        var leaf = new FieldValue(new AddressValue(read), new FieldRef(valueOwner.Definition.Fields.Single(f => !f.IsStatic), valueOwner), types.Int32, 32);
        FieldAccessor? Select(ManagedValue value, bool write) => value == read && !write ? recognized : null;
        var nestedRead = AccessorRewriter.Rewrite(Body(getter, new ManagedReturn(0, leaf)), Select);
        a.True(nestedRead.Blocks[0].Statements is [ManagedReturn { Value: FieldValue { Receiver: FieldValue { Accessor: not null } } }],
            "只读子字段使用整值 getter，不保留私有字段地址");
        var nestedWrite = AccessorRewriter.Rewrite(Body(getter, new ManagedStore(0, leaf, parameter)), Select);
        a.True(nestedWrite.Blocks[0].Statements is [ManagedStore { Target: FieldValue { Receiver: AddressValue { Target: FieldValue { Accessor: null } } } }],
            "写子字段仍使用原存储地址");
        var escapingAddress = AccessorRewriter.Rewrite(Body(getter, new ManagedReturn(0, new AddressValue(read))), Select);
        a.True(escapingAddress.Blocks[0].Statements is [ManagedReturn { Value: AddressValue { Target: FieldValue { Accessor: null } } }],
            "传出地址不替换为 getter 返回的副本");
        DependencyShape(a);
        return a.Finish("F9 严格认回边界");
    }
    private static void DependencyShape(Assertions a)
    {
        using var module = Mono.Cecil.ModuleDefinition.CreateModule("F9.Dependency.Tests", Mono.Cecil.ModuleKind.Dll);
        var contract = new Mono.Cecil.TypeDefinition("Tests", "IValue", Mono.Cecil.TypeAttributes.Public | Mono.Cecil.TypeAttributes.Interface);
        var implementation = new Mono.Cecil.TypeDefinition("Tests", "Value", Mono.Cecil.TypeAttributes.Public);
        module.Types.Add(contract);
        module.Types.Add(implementation);
        var getter = new Mono.Cecil.MethodDefinition("get_Value", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Abstract | Mono.Cecil.MethodAttributes.Virtual, module.TypeSystem.Int32);
        contract.Methods.Add(getter);
        contract.Properties.Add(new Mono.Cecil.PropertyDefinition("Value", 0, module.TypeSystem.Int32) { GetMethod = getter });
        var method = new Mono.Cecil.MethodDefinition("Tests.IValue.get_Value", Mono.Cecil.MethodAttributes.Private | Mono.Cecil.MethodAttributes.Virtual, module.TypeSystem.Int32);
        implementation.Methods.Add(method);
        method.Overrides.Add(getter);
        a.True(Cpp2CS.Output.AccessorDependencyEligibility.Problem(implementation) is not null, "拒绝缺少属性关联的显式接口访问器依赖");
        implementation.Properties.Add(new Mono.Cecil.PropertyDefinition("Tests.IValue.Value", 0, module.TypeSystem.Int32) { GetMethod = method });
        a.True(Cpp2CS.Output.AccessorDependencyEligibility.Problem(implementation) is null, "具有属性关联的显式实现可用");
        implementation.Properties.Clear();
        contract.Properties.Clear();
        a.True(Cpp2CS.Output.AccessorDependencyEligibility.Problem(implementation) is null, "普通方法即使名字含 get_ 也不误判为属性");
    }

}
