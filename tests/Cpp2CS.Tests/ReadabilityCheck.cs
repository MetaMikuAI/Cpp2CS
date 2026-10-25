using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests;

/// <summary>审核前提的正反边界；执行语义仍由原生/CIL 全量差分检查。</summary>
internal static class ReadabilityCheck
{
    [Command("readability", "可读性窄版规则边界与 CIL 一致性检查", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var a = new Assertions();
        var owner = new TypeDef { Index = -1, Assembly = "Readability.Tests.dll", Namespace = "Tests", Name = "Subject",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodRef(new MethodDef { Index = -1, Owner = owner, Name = "Read", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        var receiver = new ArgumentValue(0, new DefinitionRef(owner, []), 64);
        var local = new LocalValue(new Variable(Storage.Gpr(0), 1), types.Int32, 32);
        ManagedBody Body(params ManagedStatement[] statements) => new(method, [new(0, statements)]);
        ManagedBody Rewrite(ManagedBody body, ReadabilityRules rules) => ReadabilityRewriter.Rewrite(body, types, rules);
        ManagedValue IntegerResult(ManagedValue value) => ((ManagedReturn)Rewrite(Body(new ManagedReturn(0, value)), ReadabilityRules.Int).Blocks[0].Statements[0]).Value!;

        foreach (var w in new[] { 8, 16, 32 })
        foreach (var width in new[] { 16, 32, 64 }.Where(width => width > w))
        foreach (var signed in new[] { false, true })
        foreach (var kind in new[] { ConvKind.ZeroExtend, ConvKind.SignExtend })
        {
            var input = new ArgumentValue(0, types.Integer(w, signed), w);
            var extended = new ConversionValue(kind, input, types.Integer(width, signed), width);
            var roundtrip = new ConversionValue(ConvKind.Truncate, extended, input.Type, w);
            var rewritten = IntegerResult(roundtrip);
            a.True(ReferenceEquals(input, rewritten), $"R-int {kind} {w}->{width}->{w} 保留原值与类型");
            var samples = w == 8 ? Enumerable.Range(0, 256).Select(i => (ulong)i)
                : new ulong[] { 0, 1, (1UL << (w - 1)) - 1, 1UL << (w - 1), (1UL << w) - 1, 0x87654321 };
            a.True(samples.All(bits => Bits(roundtrip, bits) == Bits(rewritten, bits)), "R-int 边界位型相等，含负数与高位置位");
        }
        var v = new ArgumentValue(0, types.Int32, 32);
        var extend = new ConversionValue(ConvKind.ZeroExtend, v, types.UInt64, 64);
        var valid = new ConversionValue(ConvKind.Truncate, extend, types.Int32, 32);
        foreach (var rejected in new ManagedValue[]
        {
            valid with { Type = types.UInt32 }, valid with { Width = 16 },
            valid with { Operand = extend with { Width = 32 } },
            valid with { Operand = extend with { Kind = ConvKind.Bitcast } },
            new ConversionValue(ConvKind.SignExtend, new ConversionValue(ConvKind.Truncate, v, types.Int16, 16), types.Int32, 32),
            valid with { Type = types.Single, Operand = extend with { Operand = new ArgumentValue(0, types.Single, 32) } },
            valid with { Type = types.IntPtr, Operand = extend with { Operand = new ArgumentValue(0, types.IntPtr, 32) } },
            valid with { Type = types.Boolean, Width = 8, Operand = extend with { Operand = new ArgumentValue(0, types.Boolean, 8) } },
        }) a.True(IntegerResult(rejected) is ConversionValue, "R-int 保留不满足审核前提的转换");
        var pairEdge = new ManagedEdge(1, [new(local, valid)]);
        var pairBody = new ManagedBody(method, [new(0, [new ManagedJump(0, pairEdge)]), new(1, [new ManagedReturn(1, local)])]);
        a.True(((ManagedJump)Rewrite(pairBody, ReadabilityRules.Int).Blocks[0].Statements[0]).Edge.Copies[0].Value == v, "R-int 遍历边复制的源值");

        var field = new FieldDef { Index = -1, Owner = owner, Name = "Value", Token = 0, Type = types.Int32, Offset = 16, Attributes = FieldAttributes.Public };
        var read = new FieldValue(receiver, new FieldRef(field, receiver.Type), types.Int32, 32);
        // F3 的叶子仍是嵌套 FieldValue；R 必须穿过聚合值，且不能改变字段路径、求值顺序或地址根。
        var structOwner = new TypeDef { Index = -5, Assembly = "Readability.Tests.dll", Namespace = "Tests", Name = "Pair",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false };
        var structType = new DefinitionRef(structOwner, []);
        var first = new FieldRef(new FieldDef { Index = -5, Owner = structOwner, Name = "First", Token = 0,
            Type = types.Int32, Offset = 16, Attributes = FieldAttributes.Public }, structType);
        var second = new FieldRef(new FieldDef { Index = -6, Owner = structOwner, Name = "Second", Token = 0,
            Type = types.Int32, Offset = 20, Attributes = FieldAttributes.Public }, structType);
        IReadOnlyList<FieldRef> firstPath = [first], secondPath = [second];
        var composed = new ComposedValue(structType, [(firstPath, valid), (secondPath, v)]);
        var rewrittenComposed = (ComposedValue)IntegerResult(composed);
        a.True(rewrittenComposed.Type.Equals(structType) && rewrittenComposed.Width == 0
            && rewrittenComposed.Leaves.Count == 2 && ReferenceEquals(firstPath, rewrittenComposed.Leaves[0].Path)
            && ReferenceEquals(secondPath, rewrittenComposed.Leaves[1].Path), "R-F3 保留结构体类型、叶子顺序与路径身份");
        a.True(rewrittenComposed.Leaves.All(l => l.Value == v), "R-F3 改写合成值中的整数往返");
        var leaf = new FieldValue(composed, first, types.Int32, 32);
        a.True(IntegerResult(leaf) is FieldValue { Receiver: ComposedValue c } && c.Leaves[0].Value == v,
            "R-F3 遍历整体值后的叶子读取");
        var structArgument = new ArgumentValue(1, structType, 0);
        var address = new AddressValue(new FieldValue(structArgument, first, types.Int32, 32));
        a.Equal(address, IntegerResult(address), "R-F3 保留参数叶子的可别名地址");
        var indirect = new IndirectValue(new AddressValue(structArgument), structType);
        a.Equal(indirect, IntegerResult(indirect), "R-F3 保留间接值的存储根");
        var stored = (ManagedStore)Rewrite(Body(new ManagedStore(0, indirect, composed)), ReadabilityRules.Int).Blocks[0].Statements[0];
        a.True(stored.Target == indirect && stored.Value is ComposedValue storedValue && storedValue.Leaves[0].Value == v,
            "R-F3 存储目标与源值都可遍历");
        var callback = new DelegateValue((DefinitionRef)receiver.Type, receiver, method, DelegateBinding.ClosedInstance);
        var mixed = new ManagedInvocation(method, callback, [composed, indirect, address], false);
        var rewrittenCall = (ManagedCall)Rewrite(Body(new ManagedCall(0, mixed, null, false)), ReadabilityRules.Int).Blocks[0].Statements[0];
        a.True(rewrittenCall.Invocation.Receiver == callback && rewrittenCall.Invocation.Arguments[0] is ComposedValue argument
            && argument.Leaves[0].Value == v && rewrittenCall.Invocation.Arguments[1] == indirect
            && rewrittenCall.Invocation.Arguments[2] == address, "R-F3/F4 同一遍历保留委托身份和结构体参数");
        var check = new ManagedCheck(0, new ComparisonValue(Cond.Eq, receiver, new ConstantValue(0, receiver.Type, 64), types.Boolean),
            types.CorlibMethod("System.NullReferenceException", ".ctor")!);
        var assignment = new ManagedAssignment(1, local, read);
        int Checks(ManagedBody body) => Rewrite(body, ReadabilityRules.Null).Blocks.Sum(b => b.Statements.OfType<ManagedCheck>().Count());
        a.Equal(0, Checks(Body(check, assignment)), "R-null 吸收同引用紧邻字段读取");
        a.Equal(0, Checks(Body(check, assignment with { Value = new ConversionValue(ConvKind.ZeroExtend, read, types.UInt64, 64) })), "R-null 允许外层整数扩展");
        var boolField = new FieldDef { Index = -4, Owner = owner, Name = "Flag", Token = 0, Type = types.Boolean, Offset = 20, Attributes = FieldAttributes.Public };
        var boolRead = new FieldValue(receiver, new FieldRef(boolField, receiver.Type), types.Boolean, 8);
        var boolExtend = new ConversionValue(ConvKind.ZeroExtend, boolRead, types.UInt64, 64);
        var absorbedBool = Rewrite(Body(check, assignment with { Value = boolExtend }), ReadabilityRules.Null);
        a.True(absorbedBool.Blocks[0].Statements is [ManagedAssignment remaining] && ReferenceEquals(remaining.Value, boolExtend), "R-null 吸收 bool 字段判空，原零扩展逐节点保留，不假定 bool 为 0/1");
        a.Equal(1, Checks(Body(check, assignment with { Value = new ConversionValue(ConvKind.ZeroExtend, read with { Type = types.Single }, types.UInt64, 64) })), "R-null 不穿透浮点存储到整数的转换");
        a.Equal(1, Checks(Body(check, assignment with { Value = new ConversionValue(ConvKind.ZeroExtend, read with { Type = types.IntPtr }, types.UInt64, 64) })), "R-null 不穿透指针到整数的转换");
        a.Equal(1, Checks(Body(check, assignment with { Value = read with { Receiver = receiver with { Index = 1 } } })), "R-null 不吸收其他引用");
        a.Equal(1, Checks(Body(check, assignment with { Value = new BinaryValue(BinOp.Add, read, v, types.Int32, 32) })), "R-null 不穿透算术表达式");
        a.Equal(1, Checks(Body(check, new ManagedAssignment(1, local, v), assignment)), "R-null 不跨越其他求值");
        a.Equal(1, Checks(Body(check, new ManagedStore(1, read, v), assignment)), "R-null 不跨越写入");
        a.Equal(1, Checks(Body(check with { Exception = types.CorlibMethod("System.InvalidOperationException", ".ctor")! }, assignment)), "R-null 保留其他异常");
        var staticField = new FieldDef { Index = -2, Owner = owner, Name = "Static", Token = 0, Type = types.Int32, Offset = 0, Attributes = FieldAttributes.Public | FieldAttributes.Static };
        a.Equal(1, Checks(Body(check, assignment with { Value = read with { Field = new FieldRef(staticField, receiver.Type) } })), "R-null 必须是实例字段");
        var inaccessible = new FieldDef { Index = -3, Owner = types.Object.Definition, Name = "Private", Token = 0, Type = types.Int32, Offset = 16, Attributes = FieldAttributes.Private };
        a.Equal(1, Checks(Body(check, assignment with { Value = read with { Field = new FieldRef(inaccessible, types.Object) } })), "R-null 不吸收不可访问字段");
        var straight = new ManagedBody(method, [new(0, [check, new ManagedJump(0, new(1, []))]), new(1, [assignment])]);
        a.Equal(0, Checks(straight), "R-null 允许唯一前驱的无复制直线边");
        a.Equal(1, Checks(straight with { Blocks = [new(0, [check, new ManagedJump(0, pairEdge)]), straight.Blocks[1]] }), "R-null 不跨边复制");
        a.Equal(1, Checks(straight with { Blocks = [.. straight.Blocks, new(2, [new ManagedJump(2, new(1, []))])] }), "R-null 不跨汇合点");
        a.Equal(1, Checks(Body(check, new ManagedJump(1, new(0, [])))), "R-null 不绕循环");
        a.Equal(1, Checks(Body(check, new ManagedBranch(1, v, new(0, []), new(0, [])), assignment)), "R-null 不跨分支");

        var other = local with { Variable = new Variable(Storage.Gpr(1), 1) };
        var parallel = new ManagedCopy[] { new(local, other), new(other, local) };
        var jumps = new ManagedBody(method, [new(0, [new ManagedJump(0, new(1, parallel))]),
            new(1, [new ManagedJump(1, new(2, []))]), new(2, [new ManagedReturn(2, local)])]);
        var bypassed = Rewrite(jumps, ReadabilityRules.Goto);
        a.Equal(2, bypassed.Blocks.Count, "R-goto 收缩空跳转块");
        a.True(((ManagedJump)bypassed.Blocks[0].Statements[0]).Edge is { Target: 2 } edge && ReferenceEquals(parallel, edge.Copies), "R-goto 保留入边并行交换");
        var cycle = new ManagedBody(method, [new(0, [new ManagedJump(0, new(1, []))]), new(1, [new ManagedJump(1, new(0, []))])]);
        a.True(Rewrite(cycle, ReadabilityRules.Goto).Blocks is [ { Address: 0, Statements: [ManagedJump { Edge.Target: 0 }] } ], "R-goto 保留无限循环为入口自环");
        a.Equal(1, Rewrite(Body(new ManagedJump(0, new(0, []))), ReadabilityRules.Goto).Blocks.Count, "R-goto 保留入口与自环");
        a.Equal(3, Rewrite(jumps with { Blocks = [jumps.Blocks[0], new(1, [new ManagedJump(1, new(2, parallel))]), jumps.Blocks[2]] }, ReadabilityRules.Goto).Blocks.Count, "R-goto 保留含出边复制的块");
        a.True(ReferenceEquals(jumps, Rewrite(jumps, ReadabilityRules.None)), "none 不改写");
        a.Equal(ReadabilityRules.Int | ReadabilityRules.Null, ReadabilityRewriter.Parse(null), "默认只启用已批准且有收益的规则");
        a.Equal(ReadabilityRules.Goto, ReadabilityRewriter.Parse("goto"), "goto 可独立实验");
        var rejectedOption = false;
        try { ReadabilityRewriter.Parse("bool"); } catch (ArgumentException) { rejectedOption = true; }
        a.True(rejectedOption, "未知或未批准规则不得静默启用");
        Fingerprints(a);
        return a.Finish("readability");
    }

    private static ulong Bits(ManagedValue value, ulong argument)
    {
        var mask = value.Width == 64 ? ulong.MaxValue : (1UL << value.Width) - 1;
        if (value is ArgumentValue) return argument & mask;
        var conversion = (ConversionValue)value;
        var bits = Bits(conversion.Operand, argument);
        if (conversion.Kind == ConvKind.SignExtend && (bits & (1UL << (conversion.Operand.Width - 1))) != 0)
            bits |= ulong.MaxValue << conversion.Operand.Width;
        return bits & mask;
    }

    private static void Fingerprints(Assertions a)
    {
        using var module = Mono.Cecil.ModuleDefinition.CreateModule("Readability", Mono.Cecil.ModuleKind.Dll);
        var type = new Mono.Cecil.TypeDefinition("Tests", "Subject", Mono.Cecil.TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(type);
        var method = new Mono.Cecil.MethodDefinition("Value", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
        type.Methods.Add(method);
        var il = method.Body.GetILProcessor();
        var genericType = new Mono.Cecil.TypeReference("Tests", "Generic`1", module, module.TypeSystem.CoreLibrary);
        var parameter = new Mono.Cecil.GenericParameter("T", genericType);
        genericType.GenericParameters.Add(parameter);
        var instance = new Mono.Cecil.GenericInstanceType(genericType);
        instance.GenericArguments.Add(module.TypeSystem.Int32);
        var callee = new Mono.Cecil.MethodReference("Use", module.TypeSystem.Void, instance);
        callee.Parameters.Add(new Mono.Cecil.ParameterDefinition(parameter));
        il.Emit(OpCodes.Ldc_I4, 0); il.Emit(OpCodes.Call, callee);
        il.Emit(OpCodes.Ldc_I4, 7); il.Emit(OpCodes.Ret);
        var before = EmittedBodyCheck.Describe(method);
        using var stream = new MemoryStream();
        module.Write(stream);
        stream.Position = 0;
        using var saved = Mono.Cecil.ModuleDefinition.ReadModule(stream);
        a.True(before.SequenceEqual(EmittedBodyCheck.Describe(saved.Types[1].Methods[0])), "写盘 token/MaxStack 变化不影响 CIL 身份");
        method.Body.Instructions[0].Operand = 8;
        a.True(!before.SequenceEqual(EmittedBodyCheck.Describe(method)), "CIL 一致性检查检出常量变化");
    }
}
