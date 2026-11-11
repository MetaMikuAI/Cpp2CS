using Cpp2CS.Model;
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
        string[] names = ["Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference", "Void"];
        var definitions = names.Select((n, i) => new TypeDef { Index = i, Assembly = "mscorlib.dll", Namespace = "System", Name = n,
            Token = (uint)(0x02000001 + i), Attributes = System.Reflection.TypeAttributes.Public,
            IsValueType = n is not ("Object" or "String"), IsEnum = false }).ToList();
        var owner = new TypeDef { Index = definitions.Count, Assembly = "LoweringChecks.dll", Namespace = "", Name = "Cases",
            Token = 0x02000001, Attributes = System.Reflection.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        definitions.Add(owner);
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        var methods = new[] { "Add", "Branch", "Loop", "Spill", "Swap", "Accumulate", "Predicate", "Narrow" }.Select((n, i) => new MethodDef {
            Index = i, Owner = owner, Name = n, Token = (uint)(0x06000001 + i),
            Attributes = System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, ImplAttributes = 0, Slot = -1,
            ReturnType = Type(n == "Narrow" ? "SByte" : "Int32"),
            Parameters = [new("a", Type(n == "Narrow" ? "SByte" : "Int32"), 0, null, false), new("b", Type(n == "Narrow" ? "Byte" : "Int32"), 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var program = new ProgramModel {
            MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var layouts = new Cpp2CS.Runtime.Layouts.FieldLayouts(InputCorpusChecks.Spec("arm64-v8a"), 8, 8);
        var types = new ManagedTypes(program, layouts, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var skeleton = new Skeleton(program, 16);
        var emitter = new BodyEmitter(skeleton, types);
        var checks = new Assertions();
        foreach (var name in new[] { "Add", "Branch", "Loop", "Spill", "Swap", "Accumulate", "Predicate", "Narrow" })
        {
            var reference = MethodRef.Open(methods.Single(m => m.Name == name));
            var executionReference = model.Method(source.Method("Cases", name));
            var function = Function(name);
            var result = new IntegerLowering(function, reference, binder, types).Run();
            checks.True(result.Body is not null, $"{name} 下降：{result.Failure}");
            if (result.Body is null) continue;
            var problems = emitter.Emit([result.Body]);
            checks.True(problems.Count == 0, $"{name} CIL 校验：{string.Join(';', problems.Values)}");
            if (problems.Count != 0) continue;
            var method = source.Method("Cases", name);
            var emitted = skeleton.Method(reference.Method);
            // 解释器使用真实编译模块的类型解析器；整数局部的类型引用相应映回该模块。
            method.Body = emitted.Body;
            foreach (var local in method.Body.Variables)
                local.VariableType = local.VariableType.MetadataType == Mono.Cecil.MetadataType.Int64 ? source.Module.TypeSystem.Int64 : source.Module.TypeSystem.Int32;
            var index = new WorldIndex(model.Program, executionTypes);
            var interpreter = new CilInterpreter(model, index) { BodyModule = source.Module, StepLimit = 10000 };
            foreach (var (a, b) in new[] { (0, 0), (-3, 5), (7, 2), (-128, 255), (127, 1), (int.MaxValue, 1) })
            {
                int expected = name switch { "Swap" => System.Buffers.Binary.BinaryPrimitives.ReverseEndianness(a), "Accumulate" => Sum(a, b), "Predicate" => (a < b) != (a == b) ? 1 : 0, "Branch" => Math.Min(a, b), "Loop" => Math.Max(a, b), "Narrow" => unchecked((sbyte)(a + b)), _ => a + b };
                var execution = interpreter.Run(new World(index, 0, new Hints([], []), executionReference.DeclaringType), method, executionReference, [StackValue.I4(a), StackValue.I4(b)]);
                ulong expectedBits = name == "Narrow" ? unchecked((byte)expected) : unchecked((uint)expected);
                checks.True(execution.Result == $"return 0x{expectedBits:x}", $"{name}({a},{b})：{execution.Result}，预期 {expected}");
            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
        return checks.Finish("整数下降");
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
        if (kind == "Branch")
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
