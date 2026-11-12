using Cpp2CS.Recovery.Structure;
using Cpp2CS.Kernel.State;
using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Kernel.Queries;
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

internal static partial class LoweringChecks
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
        GenericChecks(checks, program);
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
        var ambiguous = Calls(new BindingEntry(target, BindingEntryKind.Ordinary), new BindingEntry(MethodRef.Open(methods.Single(m => m.Name == "Narrow")), BindingEntryKind.Ordinary));
        checks.True(new IntegerLowering(Function("CallTail"), target, binder, types, calls: ambiguous).Run().Failure?.Kind == LoweringFailureKind.AmbiguousCall,
            "签名不同的候选单列洞");
        var folded = Calls(new BindingEntry(target, BindingEntryKind.Ordinary), new BindingEntry(MethodRef.Open(methods[1]), BindingEntryKind.Ordinary));
        checks.True(new IntegerLowering(Function("CallTail"), target, binder, types, calls: folded).Run().Failure?.Kind == LoweringFailureKind.FoldedCall,
            "相同代码折叠单列洞");
        var narrowCalls = Calls(new BindingEntry(MethodRef.Open(methods.Single(m => m.Name == "Narrow")), BindingEntryKind.Ordinary));
        var narrow = new IntegerLowering(Function("CallNarrow"), target, binder, types, calls: narrowCalls).Run();
        checks.True(narrow.Body is not null, $"窄返回值只使用绑定的低位：{narrow.Failure}");
        checks.True(new IntegerLowering(Function("CallTail"), target, binder, types, calls: narrowCalls).Run().Failure?.Kind == LoweringFailureKind.Binding,
            "窄返回值的 ABI 未定义高位不能取用");
        NativeIntChecks(checks, program);
        SharedChecks(checks, program);
        RuntimeChecks(checks, program);
        ConstructorChecks(checks, program);
        AccessChecks(checks, program);
        RangeChecks(checks, program);
        AddressChecks(checks, program);
        StructChecks(checks, program);
        StateChecks(checks, program);
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
        return checks.Finish("标量下降");
    }

    private static void NativeIntChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        TypeRef Type(string name) => new DefinitionRef(primitives.Types.Single(t => t.Name == name), []);
        var native = Type("IntPtr"); var unsigned = Type("UIntPtr"); var pointer = new PointerRef(Type("Int32"));
        var owner = new TypeDef { Index = primitives.Types.Count(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter"), Assembly = "NativeIntChecks.dll", Namespace = "", Name = "Values",
            Token = 0x02000001, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false,
            Size = 32, PackingSize = 0, ClassSizeIsDefault = true };
        var reference = new DefinitionRef(owner, []);
        var array = new ArrayRef(native, 1);
        var field = new FieldDef { Index = 0, Owner = owner, Name = "Value", Type = native,
            Offset = (int)spec.Layout.ObjectHeaderSize, Attributes = FieldAttributes.Public };
        var shared = new FieldDef { Index = 1, Owner = owner, Name = "Shared", Type = native,
            Offset = 0, Attributes = FieldAttributes.Public | FieldAttributes.Static };
        owner.Fields = [field, shared];
        var methods = new List<MethodDef>();
        MethodDef Method(string name, TypeRef result, params TypeRef[] parameters)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1,
                ReturnType = result, Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(method); return method;
        }
        var target = Method("Target", native, native);
        var referenceTarget = Method("ReferenceTarget", native, new ByRefRef(native));
        var entries = new[] {
            Method("Forward", native, native), Method("Add", native, native), Method("Call", native, native), Method("CallAdd", native, native),
            Method("PointerCompare", Type("Boolean"), pointer, Type("UInt64")),
            Method("UnsignedToSigned", native, unsigned), Method("SignedToUnsigned", unsigned, native),
            Method("PointerToSigned", native, pointer), Method("SignedToPointer", pointer, native),
            Method("PointerForward", pointer, pointer), Method("UnsignedForward", unsigned, unsigned),
            Method("PointerAdd", pointer, pointer), Method("UnsignedAdd", unsigned, unsigned),
            Method("Read", native, reference), Method("Write", native, reference, native),
            Method("ArrayRead", native, array), Method("ArrayWrite", native, array, native),
            Method("FieldCall", native, reference), Method("Select", native, native, native), Method("Merge", native, native, native),
            Method("ReadPointer", Type("Int32"), pointer), Method("WritePointer", pointer, pointer),
            Method("ReferenceToNative", native, reference), Method("NativeToReference", reference, native),
            Method("ReferenceCall", native, reference), Method("ReferenceStore", native, reference),
            Method("ReferenceAddressCall", native, native), Method("ReferenceAddressToNative", native, new ByRefRef(native)),
            Method("ReferenceCompare", Type("Boolean"), reference, native),
            Method("Truncate", Type("Int32"), native), Method("Extend", native, Type("Int32")),
            Method("Bits", Type("Int64"), native), Method("UnsignedBits", Type("UInt64"), unsigned),
            Method("StaticRead", native), Method("StaticCall", native), Method("StaticWrite", native, native),
        }.ToDictionary(m => m.Name);
        owner.Methods = methods;
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").Append(owner).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = owner.Fields,
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([new BindingEntry(MethodRef.Open(target), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
        var addressCalls = new CallNamingQuery(binder, new NamingChecks.Map([new BindingEntry(MethodRef.Open(referenceTarget), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
        using var source = new CompiledSource("""
            public static unsafe class NativeValues {
                public static nint Forward(nint p) => p;
                public static nint Add(nint p) => unchecked(p + 3);
                public static nuint UnsignedAdd(nuint p) => unchecked(p + 3);
                public static bool PointerCompare(int* p, ulong value) => (ulong)p == value;
                public static nint UnsignedToSigned(nuint p) => unchecked((nint)p);
                public static int Truncate(nint p) => unchecked((int)p);
                public static nint NativeZero() => System.IntPtr.Zero;
                public static nuint UnsignedZero() => System.UIntPtr.Zero;
                public static nint NativeConstantZero() => 0;
                public static nuint UnsignedConstantZero() => 0;
                public static nint NativeOne() => 1;
                public static nuint UnsignedOne() => 1;
                public static nint Zero;
                public static nint MutableZero() => Zero;
            }
            """);
        foreach (var prefix in new[] { "Native", "Unsigned" })
        {
            var zero = source.Method("NativeValues", prefix + "Zero");
            checks.True(zero.Body.Instructions.Any(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Ldsfld), prefix + " 零值检查实际读取核心库字段");
            checks.True(CilComparison.Compare(zero, source.Method("NativeValues", prefix + "ConstantZero")).Status == CilComparisonStatus.Match,
                prefix + " 核心库零字段与零常量一致");
            checks.True(CilComparison.Compare(zero, source.Method("NativeValues", prefix + "One")).Status == CilComparisonStatus.Mismatch,
                prefix + " 核心库零字段仍能检出非零输出");
        }
        checks.True(CilComparison.Compare(source.Method("NativeValues", "MutableZero"), source.Method("NativeValues", "NativeConstantZero")).Status == CilComparisonStatus.Mismatch,
            "普通类型的可变 Zero 字段仍合成非零输入");
        var executionModel = new CecilModel(source.Module);
        var executionTypes = new ManagedTypes(executionModel.Program, new ManagedStorage(executionModel.Prepare), 8);
        var executionIndex = new WorldIndex(executionModel.Program, executionTypes);
        foreach (var (mode, method) in entries)
        {
            var terms = new TermTable(); var block = new BlockIdentity(); var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(terms, block, 64, new(frame));
            var args = method.Parameters.Select((_, i) => {
                var slot = new AbstractSlot(SlotKind.Integer, i); var value = terms.Atom(new EntryAtom(slot), 64);
                builder.Inputs.Add(new(slot, value)); return value;
            }).ToArray();
            var statements = new List<Statement>();
            Term Add(Term value, long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, terms.Constant(offset, 64));
            Term Read(Term address, int width)
            {
                var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), width);
                statements.Add(new MemoryRead(id, address, width, value)); return value;
            }
            var facts = NamingFacts.Empty;
            Term result = args.Length == 0 ? terms.Constant(0, 64) : args[0];
            if (mode.StartsWith("Static", StringComparison.Ordinal))
            {
                var image = terms.Atom(new RootAtom(AddressRoot.Image), 64); builder.ImageBase = image;
                var klass = Read(Add(image, 256), 64);
                var storage = Read(Add(klass, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset), 64);
                facts = facts with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(256,
                    Outcome<MetadataEntity>.Success(new ClassEntity(reference))) };
                if (mode == "StaticWrite") { statements.Add(new MemoryWrite(new(), storage, 64, args[0])); result = args[0]; }
                else result = Read(storage, 64);
            }
            if (mode is "Add" or "CallAdd" or "PointerAdd" or "UnsignedAdd") result = Add(result, 3);
            if (mode is "PointerCompare" or "ReferenceCompare") result = terms.Apply(new CoreOperator(CoreOperation.Equal), 1, args[0], args[1]);
            if (mode is "Read" or "FieldCall") result = Read(Add(args[0], field.Offset), 64);
            if (mode is "Write" or "ReferenceStore")
            {
                var value = mode == "Write" ? args[1] : args[0];
                statements.Add(new MemoryWrite(new(), Add(args[0], field.Offset), 64, value)); result = terms.Constant(0, 64);
            }
            if (mode is "ArrayRead" or "ArrayWrite")
            {
                var address = Add(args[0], spec.Layout.ArrayDataStart);
                if (mode == "ArrayRead") result = Read(address, 64);
                else { statements.Add(new MemoryWrite(new(), address, 64, args[1])); result = args[1]; }
            }
            if (mode == "ReadPointer") result = Read(args[0], 32);
            if (mode == "WritePointer") statements.Add(new MemoryWrite(new(), args[0], 32, terms.Constant(0, 32)));
            if (mode == "Select") result = terms.Apply(new CoreOperator(CoreOperation.Select), 64,
                terms.Apply(new CoreOperator(CoreOperation.Equal), 1, args[0], terms.Constant(0, 64)), args[0], args[1]);
            if (mode is "Call" or "CallAdd" or "FieldCall" or "StaticCall" or "ReferenceCall" or "ReferenceAddressCall")
            {
                var id = new CallIdentity(); var output = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ImageFunction(10), [new(new(SlotKind.Integer), result),
                    new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], [new(new(SlotKind.Integer), output)])); result = output;
            }
            if (mode == "Truncate") result = terms.Slice(args[0], 0, 32);
            if (mode == "Extend") result = terms.Apply(new CoreOperator(CoreOperation.SignExtend), 64, terms.Slice(args[0], 0, 32));
            Return Ret(Term value) => new([new(new(SlotKind.Integer), value.Width == 64 ? value : terms.Concat(value, terms.Constant(0, 64 - value.Width)))]);
            if (mode == "Merge")
            {
                var yes = new BlockIdentity(); var no = new BlockIdentity(); var join = new BlockIdentity(); var id = new MergeIdentity();
                var merged = terms.Atom(new ResultAtom(id), 64);
                builder.Blocks.Add(new(block, [], [], new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1, args[0], terms.Constant(0, 64)), yes, no)));
                builder.Blocks.Add(new(yes, [], [], new Jump(join))); builder.Blocks.Add(new(no, [], [], new Jump(join)));
                builder.Blocks.Add(new(join, [new(id, merged, [new(yes, args[0]), new(no, args[1])])], [], Ret(merged)));
            }
            else builder.Blocks.Add(new(block, [], [.. statements], Ret(result)));
            var currentCalls = mode == "ReferenceAddressCall" ? addressCalls : calls;
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(method), binder, types, calls: currentCalls, effects: new ManagedCallEffects(currentCalls), spec: spec, names: facts).Run();
            if (mode.StartsWith("Reference", StringComparison.Ordinal) || mode == "NativeToReference")
            {
                checks.True(lowered.Failure?.Reason.Code == "lowering.NativeInt.Reference", mode + " 引用与原生整数边界报洞：" + lowered.Failure);
                continue;
            }
            if (mode is "ReadPointer" or "WritePointer")
            {
                checks.True(lowered.Failure?.Reason.Code == "location.base-untyped", mode + " 非托管内存保持独立的洞：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, mode + " 原生整数下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var problems = emitter.Emit([body]);
            checks.True(problems.Count == 0, mode + " 原生整数 CIL 栈类型校验：" + string.Join(';', problems.Values));
            if (problems.Count != 0) continue;
            var codes = skeleton.Method(method).Body.Instructions.Select(i => i.OpCode.Code).ToArray();
            bool IsConversion(Mono.Cecil.Cil.Code code) => code.ToString().StartsWith("Conv_", StringComparison.Ordinal);
            if (mode is "Forward" or "PointerForward" or "UnsignedForward" or "Call" or "Read" or "FieldCall" or "StaticRead" or "StaticCall" or "StaticWrite")
                checks.True(!codes.Any(IsConversion), mode + " 同类型转发没有转换");
            if (mode is "ArrayRead" or "ArrayWrite")
                checks.True(codes.Count(IsConversion) == 1 && codes.Contains(Mono.Cecil.Cil.Code.Conv_I), mode + " 同类型数组值只保留下标的 native int 转换");
            if (mode is "Select" or "Merge")
                checks.True(codes.Count(IsConversion) == 1 && codes.Contains(Mono.Cecil.Cil.Code.Conv_I8), mode + " 同类型分支值只保留条件比较的整数转换");
            if (mode is "Add" or "CallAdd" or "PointerAdd" or "UnsignedAdd")
            {
                var input = mode is "Add" or "CallAdd" ? Mono.Cecil.Cil.Code.Conv_I8 : Mono.Cecil.Cil.Code.Conv_U8;
                var output = mode is "Add" or "CallAdd" ? Mono.Cecil.Cil.Code.Conv_I : Mono.Cecil.Cil.Code.Conv_U;
                checks.True(codes.Count(c => c == input) == 1 && codes.Count(c => c == output) == 1 && codes.Count(IsConversion) == 2,
                    mode + " 整数运算两端各转换一次：" + string.Join(',', codes));
            }
            if (mode is "UnsignedToSigned" or "PointerToSigned" or "SignedToUnsigned" or "SignedToPointer")
                checks.True(codes.Count(IsConversion) == 1 && codes.Contains(mode is "UnsignedToSigned" or "PointerToSigned" ? Mono.Cecil.Cil.Code.Conv_I : Mono.Cecil.Cil.Code.Conv_U), mode + " 按目标类型转换一次");
            if (mode == "PointerCompare") checks.True(codes.Count(c => c == Mono.Cecil.Cil.Code.Conv_U8) == 1, "指针比较进入无符号 64 位整数位型");
            if (mode is "Bits" or "UnsignedBits")
                checks.True(codes.Count(IsConversion) == 1 && codes.Contains(mode == "Bits" ? Mono.Cecil.Cil.Code.Conv_I8 : Mono.Cecil.Cil.Code.Conv_U8), mode + " 离开类型化位置只转换一次");
            if (mode is "Forward" or "Add" or "UnsignedAdd" or "PointerCompare" or "UnsignedToSigned" or "Truncate")
            {
                var executable = source.Method("NativeValues", mode);
                var executionMethod = executionModel.Method(executable);
                executable.Body = skeleton.Method(method).Body;
                var interpreter = new CilInterpreter(executionModel, executionIndex) { BodyModule = source.Module };
                foreach (ulong bits in new ulong[] { 0, uint.MaxValue, 1UL << 63, ulong.MaxValue })
                {
                    var inputs = mode == "PointerCompare" ? new[] { StackValue.I8(bits), StackValue.I8(0) } : [StackValue.I8(bits)];
                    ulong expected = mode switch {
                        "Add" or "UnsignedAdd" => unchecked(bits + 3), "Truncate" => (uint)bits,
                        "PointerCompare" => bits == 0 ? 1UL : 0, _ => bits };
                    var execution = interpreter.Run(new World(executionIndex, 0, new Hints([], []), executionMethod.DeclaringType), executable, executionMethod, inputs);
                    checks.True(execution.Result == $"return 0x{expected:x}", mode + " 保留指针位型与整数语义：" + execution.Result);
                }
            }
        }
        var invalidBody = new ManagedBody(MethodRef.Open(entries["Forward"]),
            [new ManagedBlock(0, [new ManagedReturn(0, new ConstantValue(1, types.Int64, 64))])]);
        checks.True(emitter.Emit([invalidBody]).Count == 1, "缺少原生整数边界转换时输出栈类型检查仍拒绝方法体");
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }

    private static void SharedChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        TypeRef Type(string name) => new DefinitionRef(primitives.Types.Single(t => t.Name == name), []);
        var owner = new TypeDef { Index = primitives.Types.Count(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter"), Assembly = "SharedChecks.dll", Namespace = "", Name = "Calls",
            Token = 0x02000001, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var box = new TypeDef { Index = owner.Index + 1, Assembly = owner.Assembly, Namespace = "", Name = "Box`1",
            Token = 0x02000002, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false,
            GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }] };
        var parameter = new GenericParameterRef("T", true, 0);
        MethodDef Method(int index, TypeDef declaring, string name, TypeRef result, TypeRef[] parameters, bool receiver = false) => new() {
            Index = index, Owner = declaring, Name = name, Token = (uint)(0x06000001 + index),
            Attributes = MethodAttributes.Public | (receiver ? 0 : MethodAttributes.Static), ImplAttributes = 0, Slot = -1,
            ReturnType = result, Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
        var generic = Method(0, owner, "G", parameter, [parameter]);
        generic.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        var other = Method(1, owner, "H", parameter, [parameter]); other.GenericParameters = generic.GenericParameters;
        var plain = Method(2, owner, "Plain", Type("String"), [Type("String")]);
        var instance = Method(3, box, "Get", new GenericParameterRef("T", false, 0), [], true);
        var caller = Method(4, owner, "Use", Type("String"), [Type("String")]);
        var instanceCaller = Method(5, owner, "UseInstance", Type("String"), [new DefinitionRef(box, [Type("String")])]);
        owner.Methods = [generic, other, plain, caller, instanceCaller]; box.Methods = [instance];
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").Concat([owner, box]).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = [.. owner.Methods, instance],
            Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        var canonical = new MethodRef(generic, [], [Type("Object")]);
        var witness = new MethodRef(generic, [], [Type("String")]);
        foreach (var mode in new[] { "Closed", "Multiple", "Missing", "Null", "Forward", "Entity", "Open", "NestedOpen", "Definition", "Signature", "CandidateSignature", "Unavailable", "Mixed", "MixedMissing", "MixedDefinition", "Instance" })
        {
            var terms = new TermTable(); var block = new BlockIdentity();
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(terms, block, 64, new(frame));
            var input = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var informationInput = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            builder.Inputs.Add(new(new(SlotKind.Integer), input)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), informationInput));
            var image = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var address = terms.Apply(new CoreOperator(CoreOperation.Add), 64, image, terms.Constant(256, 64));
            var read = new ReadIdentity(); var information = terms.Atom(new ResultAtom(read), 64);
            var call = new CallIdentity(); var output = terms.Atom(new ResultAtom(call), 64);
            MethodRef actual = mode switch {
                "Open" => MethodRef.Open(generic), "NestedOpen" => new(generic, [], [new DefinitionRef(box, [])]), "Definition" or "MixedDefinition" => new(other, [], [Type("String")]),
                "Signature" => new(generic, [], [Type("Int32")]),
                "Instance" => new(instance, [Type("String")], []), _ => witness };
            MetadataEntity entity = mode == "Entity" ? new ClassEntity(Type("String")) : new MethodEntity(actual);
            var facts = NamingFacts.Empty with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(256, Outcome<MetadataEntity>.Success(entity)) };
            var statements = new List<Statement>();
            if (mode == "Forward") information = informationInput;
            else if (mode is "Null" or "MixedMissing") information = terms.Constant(0, 64);
            else {
                statements.Add(new MemoryRead(read, address, 64, information));
                if (mode == "Missing") facts = NamingFacts.Empty;
            }
            statements.Add(new Call(call, new ImageFunction(10), [new(new(SlotKind.Integer), input), new(new(SlotKind.Integer, 1), information)],
                [new(new(SlotKind.Integer), output)]));
            builder.Blocks.Add(new(block, [], [.. statements], new Return([new(new(SlotKind.Integer), output)])));
            var entries = new List<BindingEntry> { new(mode == "Instance" ? new(instance, [Type("Object")], []) : canonical, BindingEntryKind.SharedGeneric) };
            if (mode is "Mixed" or "MixedMissing" or "MixedDefinition") entries.Add(new(MethodRef.Open(plain), BindingEntryKind.Ordinary));
            if (mode == "Multiple") entries.Add(new(witness, BindingEntryKind.SharedGeneric));
            if (mode == "CandidateSignature") entries.Add(new(new(generic, [], [Type("Int32")]), BindingEntryKind.SharedGeneric));
            if (mode == "Unavailable") entries.Add(new(MethodRef.Open(generic), BindingEntryKind.SharedGeneric));
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([.. entries]), new NamingChecks.RuntimeMap(), catalog);
            var result = new IntegerLowering(builder.Freeze(), MethodRef.Open(mode == "Instance" ? instanceCaller : caller), binder, types,
                calls: calls, spec: spec, names: facts).Run();
            if (mode is "Closed" or "Multiple" or "Mixed" or "Instance")
            {
                var loweredCall = result.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single();
                var invocation = loweredCall?.Invocation;
                checks.True(invocation is not null && invocation.Method == actual && loweredCall?.Result?.Type == Type("String") && (mode == "Instance" ? invocation.Receiver?.Type == actual.DeclaringType
                    : invocation.Arguments.Single().Type == Type("String")), mode + "：见证确定封闭目标和托管输入类型：" + result.Failure);
                var emitted = result.Body is not null && emitter.Emit([result.Body]).Count == 0;
                checks.True(emitted, mode + "：封闭泛型调用通过 CIL 写出校验");
                if (emitted)
                {
                    var operand = skeleton.Method(mode == "Instance" ? instanceCaller : caller).Body.Instructions
                        .Select(i => i.Operand).OfType<Mono.Cecil.MethodReference>().Single();
                    var argument = mode == "Instance" ? (operand.DeclaringType as Mono.Cecil.GenericInstanceType)?.GenericArguments.Single()
                        : (operand as Mono.Cecil.GenericInstanceMethod)?.GenericArguments.Single();
                    checks.True(argument?.FullName == "System.String", mode + "：CIL 调用保留见证的 string 实参");
                }
            }
            else if (mode is "MixedMissing" or "MixedDefinition")
                checks.True(result.Failure?.Kind == LoweringFailureKind.AmbiguousCall, mode + "：混合折叠没有匹配见证时沿用原有失败");
            else
            {
                // 方法信息为空且没有接收者：身份无从确定，原因单列。
                var kind = mode is "CandidateSignature" or "Unavailable" ? "Signature" : mode is "Definition" or "Signature" ? "Mismatch"
                    : mode == "Null" ? "Receiver" : "Witness";
                checks.True(result.Failure?.Reason.Code == "lowering.SharedCall." + kind, mode + "：共享调用失败原因独立：" + result.Failure);
            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }

    private static void RuntimeChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        var owner = new TypeDef { Index = definitions.Count, Assembly = "RuntimeChecks.dll", Namespace = "", Name = "RuntimeCases",
            Token = 0x02000001, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        definitions.Add(owner);
        var enumBase = new TypeDef { Index = definitions.Count, Assembly = "mscorlib.dll", Namespace = "System", Name = "Enum",
            Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false,
            BaseType = Primitive("Object") };
        definitions.Add(enumBase);
        var enumeration = new TypeDef { Index = definitions.Count, Assembly = owner.Assembly, Namespace = "", Name = "Number",
            Token = 0x02000002, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = true, Size = 4,
            BaseType = new DefinitionRef(enumBase, []) };
        definitions.Add(enumeration);
        var enumField = new FieldDef { Index = 0, Owner = enumeration, Name = "value__", Type = Primitive("Int32"), Offset = 0,
            Attributes = FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName };
        enumeration.Fields = [enumField];
        var enumType = new DefinitionRef(enumeration, []);
        var nullable = new TypeDef { Index = definitions.Count, Assembly = "mscorlib.dll", Namespace = "System", Name = "Nullable`1",
            Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false, Size = 8 };
        definitions.Add(nullable);
        string[] operations = ["IsInstance", "CastClass", "Box", "Unbox"];
        var methods = operations.Select((name, i) => new MethodDef { Index = i, Owner = owner, Name = name,
            Token = (uint)(0x06000001 + i), Attributes = MethodAttributes.Public | MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1, ReturnType = Primitive(name == "Box" ? "Object" : name == "Unbox" ? "Int32" : "String"),
            Parameters = [new("value", Primitive(name == "Box" ? "Int32" : "Object"), 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [enumField],
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var method in methods)
        {
            var t = new TermTable(); var block = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var builder = new FunctionBuilder(t, block, 64, new(frame)) { ImageBase = image };
            var obj = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); builder.Inputs.Add(new(new(SlotKind.Integer), obj));
            var slot = t.Apply(new CoreOperator(CoreOperation.Add), 64, image, t.Constant(128, 64));
            var read = new ReadIdentity(); var klass = t.Atom(new ResultAtom(read), 64);
            var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), 64);
            bool box = method.Name == "Box";
            bool unbox = method.Name == "Unbox";
            var call = new Call(id, new ImageFunction(20), box
                ? [new(new(SlotKind.Integer), klass), new(new(SlotKind.Integer, 1), frame)]
                : [new(new(SlotKind.Integer), obj), new(new(SlotKind.Integer, 1), klass)],
                [new(new(SlotKind.Integer), result)]) { Trace = new(32) };
            var statements = new List<Statement> { new MemoryRead(read, slot, 64, klass) };
            if (box) statements.Add(new MemoryWrite(new(), frame, 32, t.Slice(obj, 0, 32)));
            statements.Add(call);
            if (box) statements.Add(new MemoryWrite(new(), frame, 32, t.Constant(77, 32)));
            var dataRead = new ReadIdentity(); var dataValue = t.Atom(new ResultAtom(dataRead), 32);
            var load = new MemoryRead(dataRead, result, 32, dataValue) { Trace = new(40) };
            if (unbox) statements.Add(load);
            builder.Blocks.Add(new(block, [], [.. statements],
                new Return([new(new(SlotKind.Integer), unbox ? t.Concat(dataValue, t.Constant(0, 32)) : result)])));
            var runtime = catalog.Functions.First(f => f.Operation.Name == method.Name && f.Signature is not null);
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(runtime), catalog);
            NamingFacts Facts(TypeRef target) => NamingFacts.Empty with { Slots = NamingFacts.Empty.Slots.Add(128,
                Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(target))) };
            var facts = Facts(Primitive(box || unbox ? "Int32" : "String"));
            LoweringResult Lower(NamingFacts evidence) => new IntegerLowering(builder.Freeze(), MethodRef.Open(method), binder, types,
                calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: evidence).Run();
            var lowered = Lower(facts);
            checks.True(lowered.Body is not null, method.Name + " 运行时下降：" + lowered.Failure);
            if (lowered.Body is { } body)
            {
                var assignment = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Single();
                checks.True(assignment.Address == 32 && (method.Name == "IsInstance" ? assignment.Value is IsInstValue
                    : box ? assignment.Value is BoxValue : unbox ? assignment.Value is UnboxValue : assignment.Value is CheckedCastValue)
                    && Equals(assignment.Target.Type, assignment.Value.Type),
                    method.Name + " 在调用处求值，局部沿用操作的类型");
                var problems = emitter.Emit([body]);
                checks.True(problems.Count == 0, method.Name + " CIL 校验：" + string.Join(';', problems.Values));
            }
            checks.True(Lower(NamingFacts.Empty).Failure?.Reason.Code == (box ? "lowering.Box.Class" : unbox ? "lowering.Unbox.Class" : "lowering.TypeCheck.Class"), "运行时操作缺少类实体时报洞");
            if (unbox)
            {
                var original = builder.Blocks[0];
                foreach (var mode in new[] { "Offset", "Width", "Write", "Call", "NonFrameWrite", "FrameEscape", "Duplicate", "Return", "CrossBlock" })
                {
                    var changed = original.Statements.ToList();
                    if (mode == "Offset") changed[^1] = load with { Address = t.Apply(new CoreOperator(CoreOperation.Add), 64, result, t.Constant(1, 64)) };
                    if (mode == "Width")
                    {
                        var wide = new ReadIdentity();
                        changed[^1] = new MemoryRead(wide, result, 64, t.Atom(new ResultAtom(wide), 64));
                    }
                    if (mode == "Write") changed.Insert(2, new MemoryWrite(new(), result, 32, t.Constant(9, 32)));
                    if (mode == "NonFrameWrite") changed.Insert(2, new MemoryWrite(new(), obj, 32, t.Constant(9, 32)));
                    if (mode == "FrameEscape") changed.Insert(2, new MemoryWrite(new(), frame, 64, result));
                    if (mode == "Call")
                    {
                        var next = new CallIdentity();
                        changed.Insert(2, new Call(next, new ImageFunction(20), [new(new(SlotKind.Integer), result), new(new(SlotKind.Integer, 1), klass)],
                            [new(new(SlotKind.Integer), t.Atom(new ResultAtom(next), 64))]));
                    }
                    if (mode == "Duplicate")
                    {
                        var duplicate = new ReadIdentity();
                        changed.Add(new MemoryRead(duplicate, result, 32, t.Atom(new ResultAtom(duplicate), 32)));
                    }
                    builder.Blocks[0] = original with { Statements = [.. changed], End = mode is "Return" or "Width"
                        ? new Return([new(new(SlotKind.Integer), mode == "Return" ? result : ((MemoryRead)changed[^1]).Result)]) : original.End };
                    if (mode == "CrossBlock")
                    {
                        var next = new BlockIdentity();
                        builder.Blocks[0] = original with { Statements = [.. changed.Take(2)], End = new Jump(next) };
                        builder.Blocks.Add(new(next, [], [load], original.End));
                    }
                    var rejected = Lower(facts);
                    checks.True(rejected.Failure?.Reason.Code == "lowering.Unbox.Use", "拆箱拒绝 " + mode + "：" + rejected.Failure);
                    if (mode == "CrossBlock") builder.Blocks.RemoveAt(1);
                }
                builder.Blocks[0] = original with { Statements = [.. original.Statements.Take(2), new MemoryWrite(new(), frame, 32, t.Constant(9, 32)), load] };
                var privateWrite = Lower(facts);
                checks.True(privateWrite.Body is not null, "帧写入不阻断拆箱配对：" + privateWrite.Failure);
                if (privateWrite.Body is { } privateBody) checks.True(emitter.Emit([privateBody]).Count == 0, "跨帧写入的拆箱 CIL 校验");
                builder.Blocks[0] = original;
                var enumUnbox = Lower(Facts(enumType));
                checks.True(enumUnbox.Body is not null, "枚举拆箱下降：" + enumUnbox.Failure);
                if (enumUnbox.Body is { } enumBody) checks.True(emitter.Emit([enumBody]).Count == 0, "枚举拆箱 CIL 校验");
                checks.True(Lower(Facts(new DefinitionRef(nullable, []))).Failure?.Reason.Code == "lowering.Unbox.Nullable", "可空类型拆箱保留洞");
                checks.True(Lower(Facts(Primitive("TypedReference"))).Failure?.Reason.Code == "lowering.Unbox.Struct", "结构体拆箱保留洞");
            }
            if (box)
            {
                if (lowered.Body is { } boxed)
                    checks.True(boxed.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Single().Value is BoxValue value
                        && ManagedValues.Walk(value.Operand).Any(v => v is ArgumentValue), "装箱读取调用点的帧内容，不受调用后的覆盖影响");
                var enumBox = Lower(Facts(enumType));
                checks.True(enumBox.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Single().Value
                    is BoxValue { Boxed: var boxedType, Operand.Type: var storage } && Equals(boxedType, enumType) && Equals(storage, Primitive("Int32")),
                    "枚举按基础整数取值，保留枚举盒类型：" + enumBox.Failure);
                if (enumBox.Body is { } enumBody) checks.True(emitter.Emit([enumBody]).Count == 0, "枚举装箱 CIL 校验");
                checks.True(Lower(Facts(Primitive("TypedReference"))).Failure?.Reason.Code == "lowering.Box.Struct", "结构体装箱保留洞");
                checks.True(Lower(Facts(Primitive("String"))).Failure?.Reason.Code == "lowering.Box.Struct", "引用类型装箱保留洞");
                checks.True(Lower(Facts(new DefinitionRef(nullable, []))).Failure?.Reason.Code == "lowering.Box.Nullable", "可空类型装箱单列洞");
                var original = builder.Blocks[0];
                builder.Blocks[0] = original with { Statements = [new MemoryRead(read, slot, 64, klass),
                    new MemoryWrite(new(), frame, 32, t.Constant(0x3fc00000, 32)), call] };
                var floating = Lower(Facts(Primitive("Single")));
                checks.True(floating.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Single().Value
                    is BoxValue { Operand: ConstantValue { Bits: 0x3fc00000 } number } && Equals(number.Type, Primitive("Single")),
                    "浮点装箱保留数据位型：" + floating.Failure);
                if (floating.Body is { } floatBody) checks.True(emitter.Emit([floatBody]).Count == 0, "浮点装箱 CIL 校验");
                builder.Blocks[0] = builder.Blocks[0] with { Statements = [new MemoryRead(read, slot, 64, klass),
                    call with { Arguments = [new(new(SlotKind.Integer), klass), new(new(SlotKind.Integer, 1), obj)] }] };
                checks.True(Lower(facts).Failure?.Reason.Code == "lowering.Box.Address", "非帧数据地址装箱单列洞");
            }
            if (method.Name == "CastClass")
            {
                builder.Blocks[0] = builder.Blocks[0] with { End = new Return([new(new(SlotKind.Integer), t.Constant(0, 64))]) };
                var unused = Lower(facts);
                checks.True(unused.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
                    .SingleOrDefault() is { Address: 32, Value: CheckedCastValue }, "转换结果未使用时仍在调用处执行检查");
                if (unused.Body is { } unusedBody) checks.True(emitter.Emit([unusedBody]).Count == 0, "未使用的强制转换 CIL 校验");
            }
        }
        var barrier = catalog.Functions.Single(f => f.Name == "il2cpp_codegen_memory_barrier");
        var barrierCalls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(barrier), catalog);
        var barrierTerms = new TermTable(); var barrierBlock = new BlockIdentity();
        var barrierFrame = barrierTerms.Atom(new RootAtom(AddressRoot.Frame), 64);
        var barrierBuilder = new FunctionBuilder(barrierTerms, barrierBlock, 64, new(barrierFrame));
        barrierBuilder.Blocks.Add(new(barrierBlock, [], [new Call(new(), new ImageFunction(20), [], [])], new Return([])));
        var barrierImage = new InputMemoryImage();
        var barrierState = new StateQueries(new ManagedCallEffects(barrierCalls), image: barrierImage);
        var barrierNames = new ValueNamingQuery(barrierState, barrierCalls, NamingFacts.Empty, spec, binder);
        var erased = new UnobservableEffects(barrierState, barrierCalls, barrierNames, barrierImage).Run(barrierBuilder.Freeze());
        checks.True(!erased.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(), "登记后的内存屏障由结构变换删除");
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }

    private static void ConstructorChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").Select((t, i) => new TypeDef {
            Index = i, Assembly = t.Assembly, Namespace = t.Namespace, Name = t.Name, Token = (uint)(0x02000001 + i),
            Attributes = TypeAttributes.Public, IsValueType = t.IsValueType, IsEnum = false }).ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        var parent = ((DefinitionRef)Primitive("Object")).Definition;
        var owner = new TypeDef { Index = definitions.Count, Assembly = "ConstructorChecks.dll", Namespace = "", Name = "Owner", Token = 0x02000001,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, BaseType = new DefinitionRef(parent, []) };
        definitions.Add(owner);
        MethodDef Constructor(TypeDef type, int index, ParameterDef[] parameters) => new() { Index = index, Owner = type, Name = ".ctor", Token = (uint)(0x06000001 + index),
            Attributes = MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, ImplAttributes = 0, Slot = -1,
            ReturnType = Primitive("Void"), Parameters = parameters };
        var target = Constructor(parent, 0, []); parent.Methods = [target];
        var caller = Constructor(owner, 1, [new("condition", Primitive("Boolean"), 0, null, false)]); owner.Methods = [caller];
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = [target, caller], Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8);
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(MethodRef.Open(target), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
        for (int scenario = 0; scenario < 2; scenario++)
        {
            var t = new TermTable(); var head = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity(); var join = new BlockIdentity();
            var self = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); var argument = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            var f = new FunctionBuilder(t, head, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            f.Inputs.Add(new(new(SlotKind.Integer), self)); f.Inputs.Add(new(new(SlotKind.Integer, 1), argument));
            Call Initialize(Term value) => new(new(), new ImageFunction(10), [new(new(SlotKind.Integer), value), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], []);
            if (scenario == 0) f.Blocks.Add(new(head, [], [Initialize(self)], new Return([])));
            else
            {
                var condition = t.Slice(argument, 0, 1);
                f.Blocks.Add(new(head, [], [], new Branch(condition, left, right)));
                f.Blocks.Add(new(left, [], [Initialize(t.Apply(new CoreOperator(CoreOperation.Select), 64, condition, self, t.Constant(0, 64)))], new Jump(join)));
                f.Blocks.Add(new(right, [], [Initialize(self)], new Jump(join)));
                f.Blocks.Add(new(join, [], [], new Return([])));
            }
            var function = f.Freeze(); checks.True(ExitChecker.Check(function).IsValid, "构造函数见证输入契约：" + scenario);
            var lowered = new IntegerLowering(function, MethodRef.Open(caller), binder, types, calls: calls).Run();
            checks.True(scenario == 0 ? lowered.Body is not null : lowered.Failure?.Kind == LoweringFailureKind.ConstructorInitialization,
                "唯一直接初始化可下降，多条含条件接收者的候选保留为洞：" + lowered.Failure);
        }
    }

    private static void AccessChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, string assembly = "AccessChecks.dll", string ns = "", bool value = false)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = assembly, Namespace = ns, Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public,
                IsValueType = value, IsEnum = false, Size = value ? 16 : 128, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        var owner = Define("Owner"); var reference = new DefinitionRef(owner, []);
        var integer = Primitive("Int32"); var pointer = Primitive("IntPtr"); var array = new ArrayRef(integer, 1);
        var field = new FieldDef { Index = 0, Owner = owner, Name = "Data", Type = integer,
            Offset = (int)spec.Layout.ObjectHeaderSize, Attributes = FieldAttributes.Public };
        var inner = Define("Inner", value: true); var innerType = new DefinitionRef(inner, []);
        var leaf = new FieldDef { Index = 4, Owner = inner, Name = "Leaf", Type = integer, Offset = 0, Attributes = FieldAttributes.Public };
        inner.Fields = [leaf];
        var nested = new FieldDef { Index = 5, Owner = owner, Name = "Nested", Type = innerType,
            Offset = (int)spec.Layout.ObjectHeaderSize + 8, Attributes = FieldAttributes.Public };
        var hidden = new FieldDef { Index = 6, Owner = owner, Name = "Hidden", Type = integer,
            Offset = (int)spec.Layout.ObjectHeaderSize + 32, Attributes = FieldAttributes.Private };
        owner.Fields = [field, nested, hidden];
        var del = Define("Delegate", "mscorlib.dll", "System");
        del.Fields = new[] { "invoke_impl", "method_code", "method" }.Select((n, i) => new FieldDef {
            Index = i + 1, Owner = del, Name = n, Type = pointer, Offset = (int)spec.Layout.ObjectHeaderSize + i * 8,
            Attributes = FieldAttributes.Public }).ToArray();
        var multi = Define("MulticastDelegate", "mscorlib.dll", "System"); multi.BaseType = new DefinitionRef(del, []);
        var callback = Define("Callback"); callback.BaseType = new DefinitionRef(multi, []);
        var exception = Define("NullReferenceException", "mscorlib.dll", "System");
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, TypeRef result, TypeRef[] parameters, bool virtualCall = false, bool constructor = false, bool instance = false)
        {
            var method = new MethodDef { Index = methods.Count, Owner = type, Name = name,
                Token = (uint)(0x06000001 + methods.Count), Attributes = MethodAttributes.Public |
                    (constructor ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : virtualCall ? MethodAttributes.Virtual : instance ? 0 : MethodAttributes.Static),
                ImplAttributes = 0, Slot = virtualCall ? 0 : -1, ReturnType = result,
                Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(method); return method;
        }
        var hash = Method(((DefinitionRef)integer).Definition, "GetHashCode", integer, [], instance: true);
        var target = Method(owner, "Apply", integer, [integer], true);
        var invoke = Method(callback, "Invoke", integer, [integer], true);
        Method(exception, ".ctor", Primitive("Void"), [], constructor: true);
        string[] modes = ["Read", "Write", "Preserve", "Unused", "Null", "ArrayRead", "ArrayWrite", "Length", "Virtual", "Delegate", "Reference", "RefCall", "Merge", "Nested", "ByRef", "ScalarByRef", "ScalarStore", "ReferenceSlot", "ScalarReceiver", "WrongReceiver", "ReferenceBits", "PrivateRead", "Partial", "Cross"];
        var entries = modes.ToDictionary(n => n, n => Method(n == "PrivateRead" ? callback : owner, n, n is "Reference" or "RefCall" or "Merge" or "ReferenceSlot" ? reference : n == "ReferenceBits" ? Primitive("Int64") : integer,
            [(n.StartsWith("Array", StringComparison.Ordinal) || n == "Length") ? array : n == "Delegate" ? new DefinitionRef(callback, []) : n == "ByRef" ? new ByRefRef(innerType) : n is "ScalarByRef" or "ScalarStore" or "ScalarReceiver" ? new ByRefRef(integer) : n == "ReferenceSlot" ? new ByRefRef(reference) : n == "WrongReceiver" ? Primitive("Int64") : reference, integer]));
        foreach (var type in definitions.Where(t => t == owner || t == callback || t == exception || t == ((DefinitionRef)integer).Definition)) type.Methods = methods.Where(m => m.Owner == type).ToArray();
        owner.VTable = [MethodRef.Open(target)];
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods,
            Fields = [field, .. del.Fields, leaf, nested, hidden], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var mode in modes)
        {
            var terms = new TermTable(); var block = new BlockIdentity(); var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(terms, block, 64, new(frame));
            var root = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var argument = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            builder.Inputs.Add(new(new(SlotKind.Integer), root)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), argument));
            var statements = new List<Statement>();
            Term Add(Term value, long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, terms.Constant(offset, 64));
            Term Read(Term address, int width)
            {
                var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), width);
                statements.Add(new MemoryRead(id, address, width, value)); return value;
            }
            Term result = terms.Constant(0, 32); var address = Add(root, field.Offset);
            if (mode.StartsWith("Array", StringComparison.Ordinal))
                address = terms.Apply(new CoreOperator(CoreOperation.Add), 64, Add(root, spec.Layout.ArrayDataStart),
                    terms.Apply(new CoreOperator(CoreOperation.ShiftLeft), 64, terms.Apply(new CoreOperator(CoreOperation.SignExtend), 64, terms.Slice(argument, 0, 32)), terms.Constant(2, 64)));
            if (mode is "Read" or "Preserve" or "Unused" or "Null" or "ArrayRead") result = Read(address, 32);
            if (mode is "Write" or "Preserve" or "ArrayWrite") statements.Add(new MemoryWrite(new(), address, 32, terms.Constant(9, 32)));
            if (mode == "PrivateRead") result = Read(Add(root, hidden.Offset), 32);
            if (mode == "Nested") result = Read(Add(root, nested.Offset), 32);
            if (mode is "ByRef" or "ScalarByRef") result = Read(root, 32);
            if (mode == "ScalarStore") statements.Add(new MemoryWrite(new(), root, 32, terms.Constant(9, 32)));
            if (mode == "ReferenceSlot") result = Read(root, 64);
            if (mode == "Length") result = terms.Slice(Read(Add(root, spec.Layout.Field("Il2CppArray", "max_length").ByteOffset), 64), 0, 32);
            if (mode == "Partial") result = Read(address, 16);
            if (mode == "Cross") result = Read(Add(address, 2), 32);
            if (mode == "Unused") result = terms.Constant(0, 32);
            if (mode == "Read") result = terms.Apply(new CoreOperator(CoreOperation.Add), 32, result, terms.Constant(1, 32));
            if (mode is "Reference" or "ReferenceBits") result = root;
            if (mode is "ScalarReceiver" or "WrongReceiver")
            {
                var id = new CallIdentity(); var output = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ImageFunction(10), [new(new(SlotKind.Integer), root),
                    new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], [new(new(SlotKind.Integer), output)]));
                result = terms.Slice(output, 0, 32);
            }
            if (mode == "RefCall")
            {
                var id = new CallIdentity(); result = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ImageFunction(10), [new(new(SlotKind.Integer), root), new(new(SlotKind.Integer, 1), argument),
                    new(new(SlotKind.Integer, 2), terms.Constant(0, 64))], [new(new(SlotKind.Integer), result)]));
            }
            if (mode is "Virtual" or "Delegate")
            {
                Term pointerValue, info, receiver = root;
                if (mode == "Delegate")
                { pointerValue = Read(Add(root, del.Fields[0].Offset), 64); receiver = Read(Add(root, del.Fields[1].Offset), 64); info = Read(Add(root, del.Fields[2].Offset), 64); }
                else
                {
                    var klass = Read(Add(root, spec.Layout.Field("Il2CppObject", "klass").ByteOffset), 64);
                    pointerValue = Read(Add(klass, spec.Layout.VtableStart + spec.Layout.Field("VirtualInvokeData", "methodPtr").ByteOffset), 64);
                    info = Read(Add(klass, spec.Layout.VtableStart + spec.Layout.Field("VirtualInvokeData", "method").ByteOffset), 64);
                }
                var id = new CallIdentity(); var output = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ComputedTarget(pointerValue), [new(new(SlotKind.Integer), receiver), new(new(SlotKind.Integer, 1), argument), new(new(SlotKind.Integer, 2), info)], [new(new(SlotKind.Integer), output)]));
                result = terms.Slice(output, 0, 32);
            }
            Return Ret(Term value) => new([new(new(SlotKind.Integer), value.Width == 64 ? value : terms.Concat(value, terms.Constant(0, 64 - value.Width)))]);
            RuntimeFunction? runtime = null;
            if (mode == "Null")
            {
                runtime = catalog.Functions.First(f => f.Operation.FixedThrownException == "System.NullReferenceException" && f.Signature is not null);
                var success = new BlockIdentity(); var fail = new BlockIdentity();
                builder.Blocks.Add(new(block, [], [], new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1, root, terms.Constant(0, 64)), fail, success)));
                builder.Blocks.Add(new(success, [], statements.ToImmutableArray(), Ret(result)));
                builder.Blocks.Add(new(fail, [], [new Call(new(), new ImageFunction(20), [], [], DoesNotReturn: true)], new Unreachable()));
            }
            else if (mode == "Merge")
            {
                var yes = new BlockIdentity(); var no = new BlockIdentity(); var join = new BlockIdentity(); var id = new MergeIdentity(); var merged = terms.Atom(new ResultAtom(id), 64);
                builder.Blocks.Add(new(block, [], [], new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1, terms.Slice(argument, 0, 32), terms.Constant(0, 32)), yes, no)));
                builder.Blocks.Add(new(yes, [], [], new Jump(join))); builder.Blocks.Add(new(no, [], [], new Jump(join)));
                builder.Blocks.Add(new(join, [new(id, merged, [new(yes, root), new(no, terms.Constant(0, 64))])], [], Ret(merged)));
            }
            else builder.Blocks.Add(new(block, [], statements.ToImmutableArray(), Ret(result)));
            var calls = new CallNamingQuery(binder, new NamingChecks.Map(mode == "RefCall" ? [new BindingEntry(MethodRef.Open(entries["Reference"]), BindingEntryKind.Ordinary)] : mode is "ScalarReceiver" or "WrongReceiver" ? [new BindingEntry(MethodRef.Open(hash), BindingEntryKind.Ordinary)] : []), new NamingChecks.RuntimeMap(runtime), catalog);
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(entries[mode]), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec).Run();
            if (mode == "ReferenceBits")
            {
                checks.True(lowered.Failure?.Reason.Code == "lowering.ReferenceBits", "引用位型不能直接转换为整数");
                continue;
            }
            if (mode == "WrongReceiver")
            {
                checks.True(lowered.Failure?.Kind == LoweringFailureKind.UnsupportedType, "整数地址不能冒充值类型接收者");
                continue;
            }
            if (mode == "PrivateRead")
            {
                checks.True(lowered.Failure?.Reason.Code == "lowering.Access.Field", "私有字段需要内联逆证明：" + lowered.Failure);
                continue;
            }
            if (mode == "Cross")
            {
                checks.True(lowered.Failure?.Reason.Code == "location.padding", "跨字段读取使用填充位时报洞：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, mode + " 访问下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var problems = emitter.Emit([body]);
            checks.True(problems.Count == 0, mode + " CIL 校验：" + string.Join(';', problems.Values));
            var loweredStatements = body.Blocks.SelectMany(b => b.Statements).ToArray();
            if (mode == "Preserve") checks.True(loweredStatements[0] is ManagedAssignment && loweredStatements[1] is ManagedStore &&
                loweredStatements.OfType<ManagedReturn>().Single().Value is ConversionValue { Operand: LocalValue }, "读取在原位置保存，写后使用旧值局部");
            if (mode == "Unused") checks.True(!loweredStatements.OfType<ManagedAssignment>().Any(), "未使用的读取不产生访问");
            if (mode is "Virtual" or "Delegate") checks.True(loweredStatements.OfType<ManagedCall>().Single().Invocation.Virtual && !loweredStatements.OfType<ManagedAssignment>().Any(), "分派内部读取不写出");
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }

    private static void StructChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, int size, bool value = true)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = "StructChecks.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public,
                IsValueType = value, IsEnum = false, Size = size, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        int fieldIndex = 0;
        FieldDef Field(TypeDef owner, string name, TypeRef type, int offset, FieldAttributes attributes = FieldAttributes.Public) => new() {
            Index = fieldIndex++, Owner = owner, Name = name, Type = type, Offset = offset, Attributes = attributes };
        var pair = Define("Pair", 8); var pairType = new DefinitionRef(pair, []);
        pair.Fields = [Field(pair, "First", Primitive("Int32"), 0), Field(pair, "Second", Primitive("Int32"), 4)];
        var otherPair = Define("OtherPair", 8); var otherPairType = new DefinitionRef(otherPair, []);
        otherPair.Fields = [Field(otherPair, "First", Primitive("Int32"), 0), Field(otherPair, "Second", Primitive("Int32"), 4)];
        var mixed = Define("Mixed", 16); var mixedType = new DefinitionRef(mixed, []);
        mixed.Fields = [Field(mixed, "Object", Primitive("Object"), 0), Field(mixed, "Count", Primitive("Int32"), 8)];
        var padded = Define("Padded", 16); var paddedType = new DefinitionRef(padded, []);
        padded.Fields = [Field(padded, "Tag", Primitive("Byte"), 0), Field(padded, "Value", Primitive("Int64"), 8)];
        var nested = Define("Nested", 8); var nestedType = new DefinitionRef(nested, []);
        nested.Fields = [Field(nested, "Inner", pairType, 0)];
        var hfa = Define("Hfa", 8); var hfaType = new DefinitionRef(hfa, []);
        hfa.Fields = [Field(hfa, "First", Primitive("Single"), 0), Field(hfa, "Second", Primitive("Single"), 4)];
        var large = Define("Large", 24); var largeType = new DefinitionRef(large, []);
        large.Fields = Enumerable.Range(0, 3).Select(i => Field(large, "Part" + i, Primitive("Int64"), i * 8)).ToArray();
        var generic = Define("Envelope`1", 4);
        generic.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        generic.Fields = [Field(generic, "Item", new GenericParameterRef("T", false, 0), 0)];
        var genericType = new DefinitionRef(generic, [Primitive("Int32")]);
        var wrapper = Define("Wrapper", 4); var wrapperType = new DefinitionRef(wrapper, []);
        wrapper.Fields = [Field(wrapper, "Value", Primitive("Int32"), 0)];
        var pointerWrapper = Define("PointerWrapper", 8); var pointerWrapperType = new DefinitionRef(pointerWrapper, []);
        pointerWrapper.Fields = [Field(pointerWrapper, "Pointer", Primitive("IntPtr"), 0)];
        var unsignedPointerWrapper = Define("UnsignedPointerWrapper", 8); var unsignedPointerWrapperType = new DefinitionRef(unsignedPointerWrapper, []);
        unsignedPointerWrapper.Fields = [Field(unsignedPointerWrapper, "Pointer", Primitive("UIntPtr"), 0)];
        var chain = Define("Chain", 4); var chainType = new DefinitionRef(chain, []);
        chain.Fields = [Field(chain, "Inner", wrapperType, 0)];
        var readOnly = Define("Readonly", 4); var readOnlyType = new DefinitionRef(readOnly, []);
        readOnly.Fields = [Field(readOnly, "Value", Primitive("Int32"), 0, FieldAttributes.Public | FieldAttributes.InitOnly)];
        foreach (var name in new[] { "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle" })
        {
            var previous = definitions.Single(t => t.Name == name);
            var handle = new TypeDef { Index = previous.Index, Assembly = previous.Assembly, Namespace = previous.Namespace,
                Name = previous.Name, Token = previous.Token, Attributes = previous.Attributes, IsValueType = true, IsEnum = false,
                Size = 8, PackingSize = 0, ClassSizeIsDefault = true };
            definitions[definitions.IndexOf(previous)] = handle;
            handle.Fields = [Field(handle, "value", Primitive("IntPtr"), 0, FieldAttributes.Private)];
        }
        var wrapped = Define("Wrapped", 4); var wrappedType = new DefinitionRef(wrapped, []);
        wrapped.Fields = [Field(wrapped, "Value", Primitive("Int32"), 0, FieldAttributes.Private)];
        var box = Define("Box", 40, false); var boxType = new DefinitionRef(box, []);
        box.Fields = [Field(box, "Data", pairType, (int)spec.Layout.ObjectHeaderSize), Field(box, "Wrapped", wrappedType, (int)spec.Layout.ObjectHeaderSize + 8)];
        var referenceWrapper = Define("ReferenceWrapper", 8); var referenceWrapperType = new DefinitionRef(referenceWrapper, []);
        referenceWrapper.Fields = [Field(referenceWrapper, "Object", boxType, 0)];
        var owner = Define("Cases", 16, false);
        var methods = new List<MethodDef>();
        MethodDef Method(string name, TypeRef result, params TypeRef[] parameters)
        {
            var method = new MethodDef { Index = methods.Count, Owner = owner, Name = name,
                Token = (uint)(0x06000001 + methods.Count), Attributes = MethodAttributes.Public | MethodAttributes.Static,
                ImplAttributes = 0, Slot = -1, ReturnType = result,
                Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(method); return method;
        }
        var target = Method("Identity", pairType, pairType);
        var refTarget = Method("TakeRef", Primitive("Void"), new ByRefRef(pairType));
        var createLarge = Method("CreateLarge", largeType);
        var refLarge = Method("TakeLargeRef", Primitive("Void"), new ByRefRef(largeType));
        var consumeLarge = Method("ConsumeLarge", Primitive("Void"), largeType);
        var cases = new Dictionary<string, MethodDef> {
            ["Forward"] = Method("Forward", pairType, pairType),
            ["ReferenceRoot"] = Method("ReferenceRoot", Primitive("Int32"), new ByRefRef(referenceWrapperType)),
            ["Compose"] = Method("Compose", pairType, Primitive("Int32"), Primitive("Int32")),
            ["ComposeHfa"] = Method("ComposeHfa", hfaType, Primitive("Single"), Primitive("Single")),
            ["ComposeMixed"] = Method("ComposeMixed", mixedType, Primitive("Object"), Primitive("Int32")),
            ["ComposePadded"] = Method("ComposePadded", paddedType, Primitive("Int64")),
            ["ProjectWide"] = Method("ProjectWide", otherPairType, boxType),
            ["FrameRef"] = Method("FrameRef", Primitive("Void")),
            ["FrameWhole"] = Method("FrameWhole", pairType, pairType),
            ["FrameIndirectResult"] = Method("FrameIndirectResult", Primitive("Int64")),
            ["FrameResultSnapshot"] = Method("FrameResultSnapshot", Primitive("Int64")),
            ["FrameLargePass"] = Method("FrameLargePass", Primitive("Void")),
            ["FrameBufferPartial"] = Method("FrameBufferPartial", Primitive("Int64")),
            ["FrameBufferPhi"] = Method("FrameBufferPhi", Primitive("Int64")),
            ["Wrap"] = Method("Wrap", wrapperType, Primitive("Int32")),
            ["WrapPointer"] = Method("WrapPointer", pointerWrapperType, Primitive("Int64")),
            ["WrapUnsignedPointer"] = Method("WrapUnsignedPointer", unsignedPointerWrapperType, Primitive("UInt64")),
            ["WrapChain"] = Method("WrapChain", chainType, Primitive("Int32")),
            ["Unwrap"] = Method("Unwrap", Primitive("Int32"), wrapperType),
            ["PrivateWrap"] = Method("PrivateWrap", wrappedType, Primitive("Int32")),
            ["PrivateUnwrap"] = Method("PrivateUnwrap", Primitive("Int32"), wrappedType),
            ["ReadonlyWrap"] = Method("ReadonlyWrap", readOnlyType, Primitive("Int32")),
            ["TypeToken"] = Method("TypeToken", Primitive("RuntimeTypeHandle")),
            ["ClassToken"] = Method("ClassToken", Primitive("RuntimeTypeHandle")),
            ["FieldToken"] = Method("FieldToken", Primitive("RuntimeFieldHandle")),
            ["MethodToken"] = Method("MethodToken", Primitive("RuntimeMethodHandle")),
            ["WrongToken"] = Method("WrongToken", Primitive("RuntimeTypeHandle")),
            ["StoreForward"] = Method("StoreForward", Primitive("Void"), boxType, wrappedType),
            ["NestedField"] = Method("NestedField", Primitive("Int32"), nestedType),
            ["CallResult"] = Method("CallResult", pairType, pairType),
            ["Hfa"] = Method("Hfa", hfaType, hfaType),
            ["IndirectField"] = Method("IndirectField", Primitive("Int64"), largeType),
            ["FieldCopy"] = Method("FieldCopy", pairType, boxType),
            ["WholeCopy"] = Method("WholeCopy", pairType, boxType),
            ["ArrayCopy"] = Method("ArrayCopy", pairType, new ArrayRef(pairType, 1)),
            ["GenericForward"] = Method("GenericForward", genericType, genericType),
            ["LargeForward"] = Method("LargeForward", largeType, largeType),
            ["InterleavedLarge"] = Method("InterleavedLarge", largeType, largeType),
            ["ChangedField"] = Method("ChangedField", pairType, boxType),
            ["Incomplete"] = Method("Incomplete", pairType, pairType),
        };
        owner.Methods = methods;
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods,
            Fields = definitions.SelectMany(t => t.Fields).ToArray(), RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8);
        var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var (mode, definition) in cases)
        {
            var terms = new TermTable(); var entry = new BlockIdentity();
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(terms, entry, 64, new(frame));
            Term Input(SlotKind kind, int index)
            {
                var slot = new AbstractSlot(kind, index); var term = terms.Atom(new EntryAtom(slot), kind == SlotKind.Floating ? 128 : 64);
                builder.Inputs.Add(new(slot, term)); return term;
            }
            var root = Input(mode is "Hfa" or "ComposeHfa" ? SlotKind.Floating : SlotKind.Integer, 0);
            var statements = new List<Statement>();
            Term Add(Term value, long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, terms.Constant(unchecked((ulong)offset), 64));
            Term Read(Term address, int width)
            {
                var id = new ReadIdentity(); var term = terms.Atom(new ResultAtom(id), width);
                statements.Add(new MemoryRead(id, address, width, term)); return term;
            }
            Term result = root;
            var facts = NamingFacts.Empty;
            if (mode.EndsWith("Token", StringComparison.Ordinal))
            {
                var image = terms.Atom(new RootAtom(AddressRoot.Image), 64); builder.ImageBase = image;
                result = Read(Add(image, 256), 64);
                MetadataEntity entity = mode switch {
                    "ClassToken" => new ClassEntity(Primitive("Object")),
                    "FieldToken" or "WrongToken" => new FieldEntity(new FieldRef(box.Fields[0], boxType)),
                    "MethodToken" => new MethodEntity(MethodRef.Open(target)),
                    _ => new TypeEntity(Primitive("Object")) };
                facts = facts with { Slots = facts.Slots.Add(256, Outcome<MetadataEntity>.Success(entity)) };
            }
            if (mode == "NestedField") result = terms.Concat(terms.Slice(root, 32, 32), terms.Constant(0, 32));
            if (mode == "IndirectField") result = Read(Add(root, 8), 64);
            if (mode == "ReferenceRoot") result = terms.Concat(Read(Add(Read(root, 64), box.Fields[0].Offset), 32), terms.Constant(0, 32));
            if (mode == "CallResult")
            {
                var id = new CallIdentity(); result = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ImageFunction(10), [new(new(SlotKind.Integer), root), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], [new(new(SlotKind.Integer), result)]));
            }
            if (mode is "FieldCopy" or "ChangedField")
            {
                var first = Read(Add(root, box.Fields[0].Offset), 32);
                if (mode == "ChangedField") statements.Add(new MemoryWrite(new(), Add(root, box.Fields[0].Offset + 4), 32, terms.Constant(19, 32)));
                result = terms.Concat(first, Read(Add(root, box.Fields[0].Offset + 4), 32));
            }
            Term? secondResult = null;
            Merge? bufferMerge = null; BlockIdentity? bufferLeft = null, bufferRight = null, bufferJoin = null;
            if (mode == "Compose") result = terms.Concat(terms.Slice(root, 0, 32), terms.Slice(Input(SlotKind.Integer, 1), 0, 32));
            if (mode == "ComposeMixed") secondResult = terms.Concat(terms.Slice(Input(SlotKind.Integer, 1), 0, 32), terms.Undefined(32));
            if (mode == "ComposePadded")
            {
                secondResult = root;
                result = terms.Concat(terms.Constant(3, 8), terms.Undefined(56));
            }
            if (mode == "FrameWhole")
            {
                var address = Add(frame, -32);
                statements.Add(new MemoryWrite(new(), address, 32, terms.Slice(root, 0, 32)));
                statements.Add(new MemoryWrite(new(), Add(address, 4), 32, terms.Slice(root, 32, 32)));
                statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
                result = Read(address, 64);
            }
            if (mode is "FrameIndirectResult" or "FrameResultSnapshot" or "FrameLargePass" or "FrameBufferPartial" or "FrameBufferPhi")
            {
                var address = Add(frame, -64);
                Term buffer = mode == "FrameBufferPartial" ? Add(address, 8) : address;
                if (mode == "FrameBufferPhi")
                {
                    bufferLeft = new(); bufferRight = new(); bufferJoin = new();
                    var mergeId = new MergeIdentity(); buffer = terms.Atom(new ResultAtom(mergeId), 64);
                    bufferMerge = new(mergeId, buffer, [new(bufferLeft, address), new(bufferRight, Add(address, 8))]);
                }
                statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), terms.Constant(0, 64)),
                    new(new(SlotKind.IndirectResult), buffer)], []));
                if (mode == "FrameResultSnapshot") result = Read(Add(address, 8), 64);
                statements.Add(new Call(new(), new ImageFunction(30), [new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
                if (mode == "FrameLargePass") statements.Add(new Call(new(), new ImageFunction(40), [new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
                else if (mode != "FrameResultSnapshot") result = Read(Add(address, 8), 64);
            }
            if (mode == "FrameRef") statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), frame), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
            if (mode == "StoreForward") statements.Add(new MemoryWrite(new(), Add(root, box.Fields[1].Offset), 32, terms.Slice(Input(SlotKind.Integer, 1), 0, 32)));
            if (mode is "WholeCopy" or "ProjectWide") result = Read(Add(root, box.Fields[0].Offset), 64);
            if (mode == "ArrayCopy") result = Read(Add(root, spec.Layout.ArrayDataStart), 64);
            if (mode is "LargeForward" or "InterleavedLarge")
            {
                var output = Input(SlotKind.IndirectResult, 0);
                if (mode == "InterleavedLarge")
                    for (int i = 0; i < 3; i++) statements.Add(new MemoryWrite(new(), Add(output, i * 8), 64, Read(Add(root, i * 8), 64)));
                else
                {
                    var pieces = Enumerable.Range(0, 3).Select(i => Read(Add(root, i * 8), 64)).ToArray();
                    for (int i = 0; i < pieces.Length; i++)
                        statements.Add(new MemoryWrite(new(), Add(output, i * 8), 64, pieces[i]));
                }
            }
            if (mode == "Incomplete") result = terms.Concat(terms.Slice(root, 0, 32), terms.Undefined(32));
            var returned = mode is "Hfa" or "ComposeHfa" ? new Return([new(new(SlotKind.Floating), root), new(new(SlotKind.Floating, 1), Input(SlotKind.Floating, 1))])
                : new Return(secondResult is null ? [new(new(SlotKind.Integer), result)] : [new(new(SlotKind.Integer), result), new(new(SlotKind.Integer, 1), secondResult)]);
            if (bufferMerge is not null)
            {
                builder.Blocks.Add(new(entry, [], [], new Branch(terms.Constant(1, 1), bufferLeft!, bufferRight!)));
                builder.Blocks.Add(new(bufferLeft!, [], [], new Jump(bufferJoin!)));
                builder.Blocks.Add(new(bufferRight!, [], [], new Jump(bufferJoin!)));
                builder.Blocks.Add(new(bufferJoin!, [bufferMerge], [.. statements], returned));
            }
            else builder.Blocks.Add(new(entry, [], statements.ToImmutableArray(), mode is "LargeForward" or "InterleavedLarge" ? new Return([]) : returned));
            var selectedTarget = mode is "FrameRef" or "FrameWhole" ? refTarget
                : mode is "FrameIndirectResult" or "FrameResultSnapshot" or "FrameLargePass" or "FrameBufferPartial" or "FrameBufferPhi" ? createLarge : target;
            var calls = new CallNamingQuery(binder, new AddressMap(selectedTarget, refLarge, consumeLarge), new NamingChecks.RuntimeMap(), catalog);
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(definition), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            if (mode is "FrameBufferPartial" or "FrameBufferPhi")
            {
                checks.True(lowered.Failure?.Reason.Code == "lowering.Frame.Struct" && lowered.Failure.Reason.Message.Contains(largeType.ToString(), StringComparison.Ordinal), "间接结果部分覆盖结构体帧时报类型明确的洞");
                continue;
            }
            if (mode is "PrivateWrap" or "PrivateUnwrap" or "ReadonlyWrap" or "WrongToken")
            {
                var expected = mode switch { "PrivateUnwrap" => "lowering.Access.Field", "ReadonlyWrap" => "lowering.Struct.Readonly", "WrongToken" => "lowering.Struct.TokenEntity", _ => "lowering.Struct.Inaccessible" };
                checks.True(lowered.Failure?.Reason.Code == expected, mode + " 分开报告不可写或实体不匹配：" + lowered.Failure);
                continue;
            }
            if (mode is "Incomplete" or "InterleavedLarge")
            {
                checks.True(lowered.Failure?.Reason.Code.StartsWith("lowering.Struct.", StringComparison.Ordinal) == true, mode + " 不冒充整体转发：" + lowered.Failure);
                continue;
            }
            checks.True(lowered.Body is not null, mode + " 结构体下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            if (mode is "FrameIndirectResult" or "FrameResultSnapshot" or "FrameLargePass")
            {
                var loweredCalls = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().ToArray();
                var original = loweredCalls[0].Result;
                var stored = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().SingleOrDefault(a => a.Value == original);
                checks.True(original is not null && stored is not null && stored.Target != original, mode + " 间接结果用独立快照写回可变帧局部");
                checks.True(loweredCalls[1].Invocation.Arguments[0] is AddressValue address && address.Target == stored?.Target, mode + " 后续按引用调用使用同一帧局部");
                if (mode == "FrameLargePass") checks.True(loweredCalls[2].Invocation.Arguments[0] == stored?.Target, "间接 ABI 的结构体帧整体按值传出");
                if (mode == "FrameResultSnapshot") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>()
                    .SelectMany(r => ManagedValues.Walk(r.Value!)).OfType<FieldValue>().Any(f => f.Receiver == original), "调用前读取保持独立调用结果快照，不读后来被改写的帧局部");
            }
            if (mode == "FrameWhole") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
                .Any(a => a.Value is ArgumentValue { Index: 0 } && a.Target.Type.Equals(pairType)), "连续叶子写入按同类型整体复制到帧局部");
            var problems = emitter.Emit([body]);
            checks.True(problems.Count == 0, mode + " 结构体 CIL 校验：" + string.Join(';', problems.Values));
            if (mode.EndsWith("Token", StringComparison.Ordinal)) checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value is TypeHandleValue or FieldHandleValue or MethodHandleValue, mode + " 使用 ldtoken 值");
            if (mode == "ChangedField") checks.True(body.Blocks[0].Statements[0] is ManagedAssignment { Value: FieldValue }
                && body.Blocks[0].Statements[1] is ManagedStore
                && body.Blocks[0].Statements.OfType<ManagedReturn>().Single().Value is ComposedValue, "中间有写入时逐字段组成，旧字段仍在写入前求值");
            if (mode is "Compose" or "ComposeHfa" or "ComposeMixed" or "ComposePadded" or "ProjectWide")
                checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value is ComposedValue, mode + " 逐叶子组成而非类型重解释");
            if (mode == "CallResult") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single().Result?.Type.Equals(pairType) == true, "结构体调用结果保存在同类型局部");
            if (mode == "FieldCopy") checks.True(body.Blocks[0].Statements[0] is ManagedAssignment { Value: FieldValue { Type: var copied } } && copied.Equals(pairType), "整体字段在首个原生读取处保存");
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
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
    private sealed class AddressMap(MethodDef target, MethodDef wrong, MethodDef unrelated) : IBindingCodeMap
    {
        public ImmutableArray<BindingEntry> At(ulong address) => address switch {
            10 => [new(MethodRef.Open(target), BindingEntryKind.Ordinary)],
            30 => [new(MethodRef.Open(wrong), BindingEntryKind.Ordinary)],
            40 => [new(MethodRef.Open(unrelated), BindingEntryKind.Ordinary)], _ => [] };
    }
    private static void AddressChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, bool value = false)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = "AddressChecks.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public,
                IsValueType = value, IsEnum = false, Size = value ? 8 : 64, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        var owner = Define("Owner"); var reference = new DefinitionRef(owner, []);
        var inner = Define("Inner", true); var structure = new DefinitionRef(inner, []);
        var integer = Primitive("Int32"); int header = (int)spec.Layout.ObjectHeaderSize;
        int nextField = 0;
        FieldDef Field(TypeDef type, string name, TypeRef fieldType, int offset, bool statics = false) => new() {
            Index = nextField++, Owner = type, Name = name, Type = fieldType, Offset = offset,
            Attributes = FieldAttributes.Public | (statics ? FieldAttributes.Static : 0) };
        var leaf = Field(inner, "Leaf", integer, 4); inner.Fields = [leaf];
        var data = Field(owner, "Data", integer, header);
        var aggregate = Field(owner, "Nested", structure, header + 8);
        var shared = Field(owner, "Shared", integer, 0, true);
        var sharedStruct = Field(owner, "SharedStruct", structure, 8, true);
        var bits = Field(owner, "Bits", Primitive("Int64"), header + 16);
        var native = Field(owner, "Native", Primitive("IntPtr"), header + 24);
        owner.Fields = [data, aggregate, shared, sharedStruct, bits, native];
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, TypeRef result, TypeRef[] parameters, bool instance = false)
        {
            var method = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (instance ? 0 : MethodAttributes.Static), ImplAttributes = 0, Slot = -1,
                ReturnType = result, Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray() };
            methods.Add(method); return method;
        }
        var take = Method(owner, "Take", Primitive("Void"), [new ByRefRef(integer)]);
        var takeNative = Method(owner, "TakeNative", Primitive("Void"), [new ByRefRef(Primitive("IntPtr"))]);
        var wrong = Method(owner, "Wrong", Primitive("Void"), [new ByRefRef(Primitive("Int64"))]);
        var pointer = Method(owner, "Pointer", Primitive("Void"), [new PointerRef(integer)]);
        var ordinary = Method(owner, "Ordinary", Primitive("Void"), [Primitive("Int64")]);
        var unrelated = Method(owner, "Unrelated", Primitive("Void"), []);
        var takeObject = Method(owner, "TakeObject", Primitive("Void"), [new ByRefRef(reference)]);
        var takeSingle = Method(owner, "TakeSingle", Primitive("Void"), [new ByRefRef(Primitive("Single"))]);
        var takeBoolean = Method(owner, "TakeBoolean", Primitive("Void"), [new ByRefRef(Primitive("Boolean"))]);
        var takeStruct = Method(owner, "TakeStruct", Primitive("Void"), [new ByRefRef(structure)]);
        var instance = Method(inner, "Apply", Primitive("Void"), [], true);
        var consumeStruct = Method(owner, "ConsumeStruct", Primitive("Void"), [structure]);
        string[] modes = ["Field", "NativeField", "Nested", "StructThis", "ByRef", "ThisField", "Static", "StaticNested", "StaticStruct", "Array", "ArrayField", "ArrayStruct", "Repeat", "Reload",
            "Mismatch", "Store", "FrameStore", "Return", "Pointer", "Ordinary", "Arithmetic", "Compare", "CompareConstant", "Runtime", "Interior", "Frame", "ReferenceArray", "FrameOut", "FrameRef", "FrameUnrelated", "FrameHeap", "FrameMixed", "FrameOverlap", "FrameCross", "FramePartial", "FrameRefObject", "FrameFloat", "FrameBool", "FrameNative", "FrameRuntime", "FrameOrdinary", "FrameArithmetic", "FrameStructThis", "FrameStructOut", "FrameStructWide", "FrameStructPartial", "FrameStructCross", "FrameStructValue", "FrameThreeCalls"];
        var entries = modes.ToDictionary(n => n, n => Method(n == "ThisField" ? inner : owner, n,
            n == "Return" ? Primitive("Int64") : integer, n == "ThisField" ? [] :
            [n.StartsWith("Array", StringComparison.Ordinal) ? new ArrayRef(n == "Array" ? integer : structure, 1) :
                n == "ReferenceArray" ? new ArrayRef(reference, 1) : n == "ByRef" ? new ByRefRef(structure) : reference, integer], n == "ThisField"));
        owner.Methods = methods.Where(m => m.Owner == owner).ToArray(); inner.Methods = methods.Where(m => m.Owner == inner).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods,
            Fields = [.. owner.Fields, leaf], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var mode in modes)
        {
            var terms = new TermTable(); var block = new BlockIdentity(); var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var image = terms.Atom(new RootAtom(AddressRoot.Image), 64);
            var builder = new FunctionBuilder(terms, block, 64, new(frame)) { ImageBase = image };
            var root = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64); var index = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            builder.Inputs.Add(new(new(SlotKind.Integer), root)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), index));
            var statements = new List<Statement>(); var facts = NamingFacts.Empty;
            Term Add(Term value, long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, terms.Constant(unchecked((ulong)offset), 64));
            Term Read(Term address, int width)
            { var id = new ReadIdentity(); var value = terms.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, value)); return value; }
            Term address = Add(root, data.Offset);
            if (mode is "Nested" or "StructThis") address = Add(root, aggregate.Offset + (mode == "Nested" ? 4 : 0));
            if (mode is "ByRef" or "ThisField") address = Add(root, 4);
            if (mode.StartsWith("Static", StringComparison.Ordinal))
            {
                var klass = Read(Add(image, 256), 64);
                var storage = Read(Add(klass, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset), 64);
                address = Add(storage, mode == "Static" ? 0 : mode == "StaticStruct" ? 8 : 12);
                facts = facts with { Slots = ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty.Add(256, Outcome<MetadataEntity>.Success(new ClassEntity(reference))) };
            }
            if (mode.StartsWith("Array", StringComparison.Ordinal) || mode == "ReferenceArray")
            {
                int size = mode == "Array" ? 4 : 8;
                var scaled = terms.Apply(new CoreOperator(CoreOperation.Multiply), 64, terms.Apply(new CoreOperator(CoreOperation.SignExtend), 64, terms.Slice(index, 0, 32)), terms.Constant(size, 64));
                address = terms.Apply(new CoreOperator(CoreOperation.Add), 64, Add(root, spec.Layout.ArrayDataStart + (mode == "ArrayField" ? 4 : 0)), scaled);
            }
            if (mode == "NativeField") address = Add(root, native.Offset);
            if (mode == "Interior") address = Add(address, 1);
            if (mode.StartsWith("Frame", StringComparison.Ordinal) && mode != "FrameStore") address = Add(frame, -32);
            if (mode == "FrameStructThis") statements.Add(new MemoryWrite(new(), Add(address, 4), 32, terms.Constant(7, 32)));
            if (mode == "FrameStructPartial") statements.Add(new MemoryWrite(new(), Add(address, 4), 16, terms.Constant(0, 16)));
            if (mode is "FrameRef" or "FrameUnrelated") statements.Add(new MemoryWrite(new(), address, 32, terms.Constant(7, 32)));
            if (mode == "FrameHeap") statements.Add(new MemoryWrite(new(), Add(root, bits.Offset), 64, address));
            if (mode is "FrameCross" or "FramePartial") statements.Add(new MemoryWrite(new(), address, mode == "FrameCross" ? 64 : 16, terms.Constant(0, mode == "FrameCross" ? 64 : 16)));
            Term result = terms.Constant(0, 32);
            var before = mode == "Reload" ? Read(address, 32) : null;
            var target = mode switch { "StructThis" or "StaticStruct" or "FrameStructThis" => instance, "FrameStructOut" or "FrameStructWide" or "FrameStructPartial" or "FrameStructCross" or "FrameStructValue" or "ArrayStruct" => takeStruct, "ReferenceArray" => takeObject,
                "NativeField" or "FrameNative" => takeNative, "FrameRefObject" => takeObject, "FrameFloat" => takeSingle, "FrameBool" => takeBoolean, "FrameOrdinary" => ordinary, "Mismatch" => wrong, "Pointer" => pointer, "Ordinary" => ordinary, _ => take };
            if (mode is "Store" or "FrameStore") statements.Add(new MemoryWrite(new(), mode == "Store" ? Add(root, bits.Offset) : Add(frame, -8), 64, address));
            else if (mode == "Return") result = address;
            else if (mode is "Arithmetic" or "FrameArithmetic" or "Compare" or "CompareConstant")
                result = terms.Apply(new CoreOperator(mode is "Arithmetic" or "FrameArithmetic" ? CoreOperation.Xor : CoreOperation.Equal), mode is "Arithmetic" or "FrameArithmetic" ? 64 : 1,
                    address, mode == "Compare" ? terms.Apply(new CoreOperator(CoreOperation.SignExtend), 64, terms.Slice(index, 0, 32)) : terms.Constant(3, 64));
            else
            {
                statements.Add(new Call(new(), new ImageFunction(mode is "Runtime" or "FrameRuntime" ? 20UL : 10UL), [new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
                if (mode == "Repeat") statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
            }
            if (mode is "FrameMixed" or "FrameOverlap") statements.Add(new Call(new(), new ImageFunction(30), [new(new(SlotKind.Integer), Add(address, mode == "FrameOverlap" ? 2 : 0)), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
            if (mode == "FrameUnrelated") statements.Add(new Call(new(), new ImageFunction(40), [new(new(SlotKind.Integer), terms.Constant(0, 64))], []));
            if (mode is "FrameOut" or "FrameRef" or "FrameUnrelated") result = Read(address, 32);
            if (mode == "FrameRefObject") result = Read(Add(Read(address, 64), data.Offset), 32);
            if (mode == "FrameFloat") result = terms.Apply(new CoreOperator(CoreOperation.FloatEqual), 1, Read(address, 32), terms.Constant(0, 32));
            if (mode == "FrameBool") result = terms.Concat(Read(address, 8), terms.Constant(0, 24));
            if (mode == "FrameNative") result = Read(address, 64);
            if (mode is "FrameStructThis" or "FrameStructOut") result = Read(Add(address, 4), 32);
            if (mode == "FrameStructWide") result = terms.Slice(Read(address, 64), 32, 32);
            if (mode == "FrameStructCross") result = Read(Add(address, 2), 32);
            if (mode == "FrameStructValue") statements.Add(new Call(new(), new ImageFunction(40), [new(new(SlotKind.Integer), Read(address, 64)), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
            if (mode == "FrameThreeCalls")
            {
                var firstRead = Read(address, 32);
                statements.Add(new Call(new(), new ImageFunction(40), [new(new(SlotKind.Integer), terms.Constant(0, 64))], []));
                var middleRead = Read(address, 32);
                statements.Add(new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], []));
                result = terms.Apply(new CoreOperator(CoreOperation.Add), 32, firstRead,
                    terms.Apply(new CoreOperator(CoreOperation.Add), 32, middleRead, Read(address, 32)));
            }
            if (mode == "Reload") result = terms.Apply(new CoreOperator(CoreOperation.Add), 32, before!, Read(address, 32));
            var output = result.Width < 64 ? terms.Concat(result, terms.Constant(0, 64 - result.Width)) : result;
            builder.Blocks.Add(new(block, [], statements.ToImmutableArray(), new Return([new(new(SlotKind.Integer), output)])));
            var calls = new CallNamingQuery(binder, new AddressMap(target, wrong, mode == "FrameStructValue" ? consumeStruct : unrelated),
                new NamingChecks.RuntimeMap(catalog.Functions.First(f => f.Operation.Name == "ThrowManaged" && f.Signature is not null)), catalog);
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(entries[mode]), binder, types, calls: calls,
                effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            var code = mode switch { "FrameStructPartial" or "FrameStructCross" => "lowering.Frame.Struct", "FrameHeap" or "FrameRuntime" or "FrameOrdinary" or "FrameArithmetic" => "lowering.Frame.Use", "FrameMixed" or "FrameOverlap" or "FrameCross" => "lowering.Frame.Mixed", "FramePartial" => "lowering.Frame.Partial", "Interior" or "ReferenceArray" => "lowering.Address.Location",
                "Mismatch" or "Store" or "FrameStore" or "Return" or "Pointer" or "Ordinary" or "Arithmetic" or "Compare" or "CompareConstant" or "Runtime" => "lowering.Address.Use", _ => null };
            if (code is not null)
            { checks.True(lowered.Failure?.Reason.Code == code, mode + " 取址用途拒绝：" + lowered.Failure); continue; }
            checks.True(lowered.Body is not null, mode + " 取址下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            var problems = emitter.Emit([body]);
            checks.True(problems.Count == 0, mode + " 取址 CIL 校验：" + string.Join(';', problems.Values));
            var loweredStatements = body.Blocks.SelectMany(b => b.Statements).ToArray();
            var call = loweredStatements.OfType<ManagedCall>().First();
            checks.True((call.Invocation.Receiver ?? call.Invocation.Arguments[0]) is AddressValue, mode + " 产生托管地址值");
            if (mode == "Reload")
            {
                var reads = loweredStatements.OfType<ManagedAssignment>().Where(a => a.Value is FieldValue).ToArray();
                checks.True(reads.Length == 2 && reads[0].Target != reads[1].Target && Array.IndexOf(loweredStatements, reads[0]) < Array.IndexOf(loweredStatements, call)
                    && Array.IndexOf(loweredStatements, reads[1]) > Array.IndexOf(loweredStatements, call), "传出字段地址的调用之后重新读取同字段，不复用调用前的局部");
            }
            if (mode is "FrameStructThis" or "FrameStructOut" or "FrameStructWide")
                checks.True(loweredStatements.OfType<ManagedAssignment>().Any(a => a.Value is FieldValue { Receiver: AddressValue { Target: LocalValue } }), mode + " 经局部地址读取结构体叶子并留在原读取位置");
            if (mode == "FrameThreeCalls")
            {
                var storage = ((AddressValue)call.Invocation.Arguments[0]).Target;
                var reloads = loweredStatements.OfType<ManagedAssignment>().Where(a => a.Value == storage).ToArray();
                var emittedCalls = loweredStatements.OfType<ManagedCall>().ToArray();
                checks.True(reloads.Length == 3 && emittedCalls.Length == 3 && Enumerable.Range(0, 3).All(i =>
                    Array.IndexOf(loweredStatements, reloads[i]) > Array.IndexOf(loweredStatements, emittedCalls[i])
                    && (i == 2 || Array.IndexOf(loweredStatements, reloads[i]) < Array.IndexOf(loweredStatements, emittedCalls[i + 1]))),
                    "两次按引用调用之间有无关调用时，三次读取各自在原调用之后物化");
            }
            if (mode == "FrameStructValue") checks.True(loweredStatements.OfType<ManagedCall>().Last().Invocation.Arguments[0].Type.Equals(structure), "结构体帧对象完整按值传出");
            if (mode is "FrameOut" or "FrameRef" or "FrameUnrelated")
            {
                var storage = (LocalValue)((AddressValue)call.Invocation.Arguments[0]).Target;
                var reload = loweredStatements.OfType<ManagedAssignment>().SingleOrDefault(a => a.Value == storage);
                checks.True(reload is not null && Array.IndexOf(loweredStatements, reload) > Array.LastIndexOf(loweredStatements, loweredStatements.OfType<ManagedCall>().Last()), mode + " 在最后调用之后读取同一个可寻址局部");
            }
            if (mode == "Repeat") checks.True(loweredStatements.OfType<ManagedCall>().Count() == 2, "同一地址项可以多次传出");
            var emitted = skeleton.Assemblies.SelectMany(a => a.MainModule.Types).SelectMany(t => t.Methods).Single(m => m.Name == mode);
            var expected = mode.StartsWith("Frame", StringComparison.Ordinal) ? Mono.Cecil.Cil.Code.Ldloca : mode.StartsWith("Array", StringComparison.Ordinal) ? Mono.Cecil.Cil.Code.Ldelema : mode.StartsWith("Static", StringComparison.Ordinal) ? Mono.Cecil.Cil.Code.Ldsflda : Mono.Cecil.Cil.Code.Ldflda;
            checks.True(emitted.Body.Instructions.Any(i => i.OpCode.Code == expected), mode + " 写出对应取址指令");
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
