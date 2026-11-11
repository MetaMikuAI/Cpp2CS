using Cpp2CS.Managed;
using ManagedValues = Cpp2CS.Managed.ManagedValues;
using Cpp2CS.Model;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static class LoweringChecks
{
    public const string Command = "lowering";
    public static int Run()
    {
        using var source = new CompiledSource("""
            public static class Cases {
                public static float FloatAdd(float a, float b) => a + b;
                public static float FloatSelect(float a, float b) => a < b ? a : b;
                public static double DoubleBranch(double a, double b) => a < b ? a : b;
                public static int FloatInt(float a, float b) => (int)a;
                public static double UnsignedDouble(ulong a, ulong b) => a;
                public static int FloatBits(float a, float b) => System.BitConverter.SingleToInt32Bits(a);
                public static int Add(int a, int b) => a + b;
                public static int Branch(int a, int b) => a < b ? a : b;
                public static int Loop(int a, int b) { while (a < b) a++; return a; }
                public static int Spill(int a, int b) => a + b;
                public static int Swap(int a, int b) => (int)(((uint)a >> 24) | (((uint)a >> 8) & 0xff00) | (((uint)a << 8) & 0xff0000) | ((uint)a << 24));
                public static int Accumulate(int a, int b) { while (a > 0) { b += a; a >>= 1; } return b; }
                public static int Predicate(int a, int b) => (a < b) != (a == b) ? 1 : 0;
                public static sbyte Narrow(sbyte a, byte b) => unchecked((sbyte)(a + b));
            }
            """);
        var model = new CecilModel(source.Module);
        var executionTypes = new ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8);
        string[] names = ["Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference", "Void", "BitConverter"];
        var definitions = names.Select((n, i) => new TypeDef { Index = i, Assembly = "mscorlib.dll", Namespace = "System", Name = n,
            Token = (uint)(0x02000001 + i), Attributes = System.Reflection.TypeAttributes.Public,
            IsValueType = n is not ("Object" or "String" or "BitConverter"), IsEnum = false }).ToList();
        var owner = new TypeDef { Index = definitions.Count, Assembly = "LoweringChecks.dll", Namespace = "", Name = "Cases",
            Token = 0x02000001, Attributes = System.Reflection.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        definitions.Add(owner);
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        var methods = new[] { "Add", "Branch", "Loop", "Spill", "Swap", "Accumulate", "Predicate", "Narrow", "FloatAdd", "DoubleBranch", "FloatInt", "UnsignedDouble", "FloatBits", "FloatSelect" }.Select((n, i) => new MethodDef {
            Index = i, Owner = owner, Name = n, Token = (uint)(0x06000001 + i),
            Attributes = System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, ImplAttributes = 0, Slot = -1,
            ReturnType = Type(n switch { "Narrow" => "SByte", "FloatAdd" or "FloatSelect" => "Single", "DoubleBranch" or "UnsignedDouble" => "Double", _ => "Int32" }),
            Parameters = [new("a", Type(n == "Narrow" ? "SByte" : ParameterType(n)), 0, null, false), new("b", Type(n == "Narrow" ? "Byte" : ParameterType(n)), 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var bitConverter = definitions.Single(t => t.Name == "BitConverter");
        var conversions = new[] { ("SingleToInt32Bits", "Single", "Int32"), ("Int32BitsToSingle", "Int32", "Single"),
            ("DoubleToInt64Bits", "Double", "Int64"), ("Int64BitsToDouble", "Int64", "Double") }
            .Select((c, i) => new MethodDef {
                Index = methods.Length + i, Owner = bitConverter, Name = c.Item1, Token = (uint)(0x06000001 + i),
                Attributes = System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static,
                ImplAttributes = System.Reflection.MethodImplAttributes.Runtime, Slot = -1,
                ReturnType = Type(c.Item3), Parameters = [new("value", Type(c.Item2), 0, null, false)] }).ToArray();
        bitConverter.Methods = conversions;
        var program = new ProgramModel {
            MetadataVersion = 0, Types = definitions, Methods = [.. methods, .. conversions], Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(InputCorpusChecks.Spec("arm64-v8a"), 8, 8);
        var types = new ManagedTypes(program, layouts, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var skeleton = new Skeleton(program, 16);
        var emitter = new BodyEmitter(skeleton, types);
        var checks = new Assertions();
        foreach (var name in new[] { "Add", "Branch", "Loop", "Spill", "Swap", "Accumulate", "Predicate", "Narrow", "FloatAdd", "DoubleBranch", "FloatInt", "UnsignedDouble", "FloatBits", "FloatSelect" })
        {
            var reference = MethodRef.Open(methods.Single(m => m.Name == name));
            var executionReference = model.Method(source.Method("Cases", name));
            bool floating = ParameterType(name) != "Int32";
            var function = floating ? FloatFunction(name) : Function(name);
            var result = new IntegerLowering(function, reference, binder, types).Run();
            checks.True(result.Body is not null, $"{name} 下降：{result.Failure}");
            if (result.Body is null) continue;
            if (name == "FloatInt")
            {
                bool HasChoice(ManagedBody body) => body.Blocks.SelectMany(b => b.Statements)
                    .SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).Any(v => v is ChoiceValue);
                checks.True(!HasChoice(result.Body), "饱和转换在 IL 定义域内化为单次转换");
                var invalid = new IntegerLowering(FloatFunction(name, true), reference, binder, types).Run();
                checks.True(invalid.Body is not null && HasChoice(invalid.Body), "下界替代值不相等时保留选择");
            }
            var problems = emitter.Emit([result.Body]);
            checks.True(problems.Count == 0, $"{name} CIL 校验：{string.Join(';', problems.Values)}");
            if (problems.Count != 0) continue;
            var method = source.Method("Cases", name);
            var emitted = skeleton.Method(reference.Method);
            // 解释器使用真实编译模块的类型解析器；局部的类型引用相应映回该模块。
            method.Body = emitted.Body;
            foreach (var instruction in method.Body.Instructions)
                if (instruction.Operand is Mono.Cecil.MethodReference call && call.DeclaringType.FullName == "System.BitConverter")
                    instruction.Operand = source.Module.ImportReference(typeof(BitConverter).GetMethods().Single(m => m.Name == call.Name));
            foreach (var local in method.Body.Variables)
                local.VariableType = local.VariableType.MetadataType switch {
                    Mono.Cecil.MetadataType.Int64 => source.Module.TypeSystem.Int64,
                    Mono.Cecil.MetadataType.Single => source.Module.TypeSystem.Single,
                    Mono.Cecil.MetadataType.Double => source.Module.TypeSystem.Double,
                    _ => source.Module.TypeSystem.Int32 };
            var index = new WorldIndex(model.Program, executionTypes);
            var interpreter = new CilInterpreter(model, index) { BodyModule = source.Module, StepLimit = 10000 };
            if (floating)
            {
                foreach (var (a, b) in new[] { (0.0, -0.0), (-0.0, 1.0), (-3.25, 5.5), (7.0, 2.0), (-128.75, 255.0), (-2147483648.0, 1.0) })
                {
                    var args = name == "UnsignedDouble" ? new[] { StackValue.I8(unchecked((ulong)(long)a)), StackValue.I8(0) }
                        : name == "DoubleBranch" ? new[] { StackValue.F(a), StackValue.F(b) }
                        : new[] { StackValue.F32((float)a), StackValue.F32((float)b) };
                    ulong expected = name switch {
                        "FloatAdd" => BitConverter.SingleToUInt32Bits((float)a + (float)b),
                        "FloatSelect" => BitConverter.SingleToUInt32Bits(a < b ? (float)a : (float)b),
                        "DoubleBranch" => BitConverter.DoubleToUInt64Bits(a < b ? a : b),
                        "FloatInt" => unchecked((uint)(int)a),
                        "UnsignedDouble" => BitConverter.DoubleToUInt64Bits((double)unchecked((ulong)(long)a)),
                        _ => BitConverter.SingleToUInt32Bits((float)a) };
                    var execution = interpreter.Run(new World(index, 0, new Hints([], []), executionReference.DeclaringType), method, executionReference, args);
                    checks.True(execution.Result == $"return 0x{expected:x}", $"{name}({a},{b})：{execution.Result}，预期 0x{expected:x}");
                }
                continue;
            }
            foreach (var (a, b) in new[] { (0, 0), (-3, 5), (7, 2), (-128, 255), (127, 1), (int.MaxValue, 1) })
            {
                int expected = name switch { "Swap" => System.Buffers.Binary.BinaryPrimitives.ReverseEndianness(a), "Accumulate" => Sum(a, b), "Predicate" => (a < b) != (a == b) ? 1 : 0, "Branch" => Math.Min(a, b), "Loop" => Math.Max(a, b), "Narrow" => unchecked((sbyte)(a + b)), _ => a + b };
                var execution = interpreter.Run(new World(index, 0, new Hints([], []), executionReference.DeclaringType), method, executionReference, [StackValue.I4(a), StackValue.I4(b)]);
                ulong expectedBits = name == "Narrow" ? unchecked((byte)expected) : unchecked((uint)expected);
                checks.True(execution.Result == $"return 0x{expectedBits:x}", $"{name}({a},{b})：{execution.Result}，预期 {expected}");
            }
        }
        // 常量的隐式位重解释也须在写出前检查，缺少 BCL 方法不能抛出未分类异常。
        bitConverter.Methods = [];
        var nanBody = new ManagedBody(MethodRef.Open(methods.Single(m => m.Name == "FloatAdd")),
            [new ManagedBlock(0, [new ManagedReturn(0, new ConstantValue(0x7f800001, types.Single, 32))])]);
        checks.True(emitter.Emit([nanBody]).Count == 1, "非规范 NaN 常量缺少位重解释方法时拒绝写出");
        bitConverter.Methods = conversions;
        var spec = InputCorpusChecks.Spec("arm64-v8a").Layout;
        var catalog = RuntimeFunctionCatalog.Select(spec.UnityVersion, spec.Triple, spec.DataModel);
        var target = MethodRef.Open(methods[0]);
        CallNamingQuery Calls(params BindingEntry[] entries) => new(binder, new NamingChecks.Map([.. entries]), new NamingChecks.RuntimeMap(), catalog);
        var calls = Calls(new BindingEntry(target, BindingEntryKind.Ordinary));
        foreach (var name in new[] { "CallUse", "CallUnused", "CallTwice", "CallTail", "CallSpill" })
        {
            var result = new IntegerLowering(Function(name), target, binder, types, calls: calls, effects: new ManagedCallEffects(calls)).Run();
            checks.True(result.Body is not null, $"{name} 下降：{result.Failure}");
            if (result.Body is not { } body) continue;
            var statements = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().ToArray();
            checks.True(statements.Length == (name == "CallTwice" ? 2 : 1), name + " 保留调用数量");
            checks.True(statements.All(c => c.Invocation.Method == target && !c.Invocation.Virtual), name + " 直接调用唯一目标");
            checks.True(statements[0].Result is not null == (name is "CallUse" or "CallTwice" or "CallTail"), name + " 仅使用结果时建立局部");
            if (name == "CallTwice")
                checks.True(Cpp2CS.Managed.ManagedValues.Children(statements[1].Invocation.Arguments[0]).Any(v => v is LocalValue)
                    || statements[1].Invocation.Arguments[0] is LocalValue, "第二次调用依赖第一次结果");
            checks.True(emitter.Emit([body]).Count == 0, name + " CIL 校验");
        }
        var ambiguous = Calls(new BindingEntry(target, BindingEntryKind.Ordinary), new BindingEntry(MethodRef.Open(methods[^1]), BindingEntryKind.Ordinary));
        checks.True(new IntegerLowering(Function("CallTail"), target, binder, types, calls: ambiguous).Run().Failure?.Kind == LoweringFailureKind.AmbiguousCall,
            "签名不同的候选单列洞");
        var folded = Calls(new BindingEntry(target, BindingEntryKind.Ordinary), new BindingEntry(MethodRef.Open(methods[1]), BindingEntryKind.Ordinary));
        checks.True(new IntegerLowering(Function("CallTail"), target, binder, types, calls: folded).Run().Failure?.Kind == LoweringFailureKind.FoldedCall,
            "相同代码折叠单列洞");
        var narrowCalls = Calls(new BindingEntry(MethodRef.Open(methods[^1]), BindingEntryKind.Ordinary));
        var narrow = new IntegerLowering(Function("CallNarrow"), target, binder, types, calls: narrowCalls).Run();
        checks.True(narrow.Body is not null, "窄返回值只使用绑定的低位");
        checks.True(new IntegerLowering(Function("CallTail"), target, binder, types, calls: narrowCalls).Run().Failure?.Kind == LoweringFailureKind.Binding,
            "窄返回值的 ABI 未定义高位不能取用");
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
        return checks.Finish("标量下降");
    }

    private static string ParameterType(string name) => name switch
    {
        "FloatAdd" or "FloatInt" or "FloatBits" or "FloatSelect" => "Single",
        "DoubleBranch" => "Double", "UnsignedDouble" => "UInt64", _ => "Int32",
    };

    private static NativeFunction FloatFunction(string name, bool invalidMinimum = false)
    {
        var t = new TermTable(); var entry = new BlockIdentity();
        var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
        var builder = new FunctionBuilder(t, entry, 64, new(frame));
        int width = name is "DoubleBranch" or "UnsignedDouble" ? 64 : 32;
        bool integer = name == "UnsignedDouble";
        Term Arg(int i)
        {
            var slot = new AbstractSlot(integer ? SlotKind.Integer : SlotKind.Floating, i);
            var value = t.Atom(new EntryAtom(slot), integer ? 64 : 128);
            builder.Inputs.Add(new(slot, value)); return t.Slice(value, 0, width);
        }
        Term Op(CoreOperation op, int bits, params Term[] operands) => t.Apply(new CoreOperator(op), bits, operands);
        Term Saturate(Term input)
        {
            var rounded = Op(CoreOperation.FloatTruncate, 32, input);
            var limit = t.Constant(BitConverter.SingleToUInt32Bits(2147483648f), 32);
            var minimum = t.Constant(invalidMinimum ? 1 : 0x80000000, 32);
            var conversion = Op(CoreOperation.FloatToSigned, 32, rounded);
            conversion = Op(CoreOperation.Select, 32, Op(CoreOperation.FloatLessEqual, 1, limit, rounded), t.Constant(0x7fffffff, 32), conversion);
            conversion = Op(CoreOperation.Select, 32, Op(CoreOperation.FloatLessEqual, 1, rounded, Op(CoreOperation.FloatNegate, 32, limit)), minimum, conversion);
            conversion = Op(CoreOperation.Select, 32, Op(CoreOperation.FloatUnordered, 1, input, input), t.Constant(0, 32), conversion);
            return Op(CoreOperation.Select, 32, Op(CoreOperation.FloatEqual, 1, input, t.Constant(BitConverter.SingleToUInt32Bits(float.PositiveInfinity), 32)), minimum, conversion);
        }
        var a = Arg(0); var b = Arg(1);
        Return Ret(Term value) => new([new(new(name is "FloatInt" or "FloatBits" ? SlotKind.Integer : SlotKind.Floating, 0),
            t.Concat(value, t.Constant(0, (name is "FloatInt" or "FloatBits" ? 64 : 128) - value.Width)))]);
        if (name == "DoubleBranch")
        {
            var yes = new BlockIdentity(); var no = new BlockIdentity(); var join = new BlockIdentity(); var id = new MergeIdentity();
            var merged = t.Atom(new ResultAtom(id), 128);
            builder.Blocks.Add(new(entry, [], [], new Branch(Op(CoreOperation.FloatLess, 1, a, b), yes, no)));
            builder.Blocks.Add(new(yes, [], [], new Jump(join))); builder.Blocks.Add(new(no, [], [], new Jump(join)));
            builder.Blocks.Add(new(join, [new(id, merged, [new(yes, t.Concat(a, t.Constant(0, 64))), new(no, t.Concat(b, t.Constant(0, 64)))])], [], Ret(t.Slice(merged, 0, 64))));
        }
        else
        {
            var value = name switch {
                "FloatAdd" => Op(CoreOperation.FloatAdd, 32, a, b),
                "FloatSelect" => Op(CoreOperation.Select, 32, Op(CoreOperation.FloatLess, 1, a, b), a, b),
                "FloatInt" => Saturate(a),
                "UnsignedDouble" => Op(CoreOperation.UnsignedToFloat, 64, a), _ => a };
            builder.Blocks.Add(new(entry, [], [], Ret(value)));
        }
        return builder.Freeze();
    }

    private static int Sum(int a, int b)
    {
        while (a > 0) { b = unchecked(b + a); a >>= 1; }
        return b;
    }

    private static NativeFunction Function(string kind)
    {
        var t = new TermTable(); var entry = new BlockIdentity();
        var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
        var builder = new FunctionBuilder(t, entry, 64, new(frame));
        Term Arg(int i)
        {
            var slot = new AbstractSlot(SlotKind.Integer, i); var value = t.Atom(new EntryAtom(slot), 64);
            builder.Inputs.Add(new(slot, value)); return t.Slice(value, 0, 32);
        }
        var a = Arg(0); var b = Arg(1);
        Term Op(CoreOperation op, int width, params Term[] operands) => t.Apply(new CoreOperator(op), width, operands);
        Return Ret(Term value) => new([new(new(SlotKind.Integer, 0), Op(CoreOperation.ZeroExtend, 64, value))]);
        var sum = Op(CoreOperation.Add, 32, a, b);
        if (kind == "Narrow")
        {
            a = Op(CoreOperation.SignExtend, 32, t.Slice(a, 0, 8));
            b = Op(CoreOperation.ZeroExtend, 32, t.Slice(b, 0, 8));
            sum = Op(CoreOperation.Add, 32, a, b);
        }
        if (kind.StartsWith("Call", StringComparison.Ordinal))
        {
            var statements = new List<Statement>();
            Term Invoke(Term left)
            {
                var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ImageFunction(10),
                    [new(new(SlotKind.Integer, 0), Op(CoreOperation.ZeroExtend, 64, left)),
                     new(new(SlotKind.Integer, 1), Op(CoreOperation.ZeroExtend, 64, b)),
                     new(new(SlotKind.Integer, 2), t.Constant(0, 64))], [new(new(SlotKind.Integer, 0), result)], OutgoingArgumentArea: frame));
                return t.Slice(result, 0, 32);
            }
            if (kind == "CallSpill") statements.Add(new MemoryWrite(new(), frame, 32, sum));
            var value = Invoke(a);
            if (kind == "CallTwice") value = Invoke(value);
            if (kind == "CallNarrow") value = Op(CoreOperation.SignExtend, 32, t.Slice(value, 0, 8));
            if (kind == "CallUse") value = Op(CoreOperation.Add, 32, value, b);
            if (kind == "CallUnused") value = sum;
            if (kind == "CallSpill")
            {
                var read = new ReadIdentity(); value = t.Atom(new ResultAtom(read), 32);
                statements.Add(new MemoryRead(read, frame, 32, value));
            }
            builder.Blocks.Add(new(entry, [], [.. statements], Ret(value)));
        }
        else if (kind == "Branch")
        {
            var yes = new BlockIdentity(); var no = new BlockIdentity();
            builder.Blocks.Add(new(entry, [], [], new Branch(Op(CoreOperation.SignedLess, 1, a, b), yes, no)));
            builder.Blocks.Add(new(yes, [], [], Ret(a))); builder.Blocks.Add(new(no, [], [], Ret(b)));
        }
        else if (kind == "Loop")
        {
            var head = new BlockIdentity(); var body = new BlockIdentity(); var exit = new BlockIdentity(); var id = new MergeIdentity();
            var slotValue = t.Atom(new ResultAtom(id), 64);
            var value = t.Slice(slotValue, 0, 32);
            builder.Blocks.Add(new(entry, [], [], new Jump(head)));
            builder.Blocks.Add(new(head, [new(id, slotValue, [new(entry, a.Operands[0]), new(body, Op(CoreOperation.ZeroExtend, 64, Op(CoreOperation.Add, 32, value, t.Constant(1, 32))))])], [],
                new Branch(Op(CoreOperation.SignedLess, 1, value, b), body, exit)));
            builder.Blocks.Add(new(body, [], [], new Jump(head))); builder.Blocks.Add(new(exit, [], [], Ret(value)));
        }
        else if (kind == "Accumulate")
        {
            var head = new BlockIdentity(); var body = new BlockIdentity(); var exit = new BlockIdentity();
            var ai = new MergeIdentity(); var bi = new MergeIdentity();
            var av = t.Atom(new ResultAtom(ai), 64); var bv = t.Atom(new ResultAtom(bi), 64);
            var x = t.Slice(av, 0, 32); var y = t.Slice(bv, 0, 32);
            builder.Blocks.Add(new(entry, [], [], new Jump(head)));
            builder.Blocks.Add(new(head, [new(ai, av, [new(entry, a.Operands[0]), new(body, t.Concat(t.Slice(av, 1, 31), t.Constant(0, 33)))]),
                new(bi, bv, [new(entry, b.Operands[0]), new(body, Op(CoreOperation.ZeroExtend, 64, Op(CoreOperation.Add, 32, x, y)))])], [],
                new Branch(Op(CoreOperation.SignedLess, 1, t.Constant(0, 32), x), body, exit)));
            builder.Blocks.Add(new(body, [], [], new Jump(head))); builder.Blocks.Add(new(exit, [], [], Ret(y)));
        }
        else if (kind == "Swap")
            builder.Blocks.Add(new(entry, [], [], Ret(Op(CoreOperation.ReverseBytes, 32, a))));
        else if (kind == "Predicate")
            builder.Blocks.Add(new(entry, [], [], Ret(Op(CoreOperation.ZeroExtend, 32,
                Op(CoreOperation.Xor, 1, Op(CoreOperation.SignedLess, 1, a, b), Op(CoreOperation.Equal, 1, a, b))))));
        else if (kind == "Spill")
        {
            var id = new ReadIdentity(); var read = t.Atom(new ResultAtom(id), 32);
            builder.Blocks.Add(new(entry, [], [new MemoryWrite(new(), frame, 32, sum), new MemoryRead(id, frame, 32, read)], Ret(read)));
        }
        else builder.Blocks.Add(new(entry, [], [], Ret(sum)));
        return builder.Freeze();
    }
}
