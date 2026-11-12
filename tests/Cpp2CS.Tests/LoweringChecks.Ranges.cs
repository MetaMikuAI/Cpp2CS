using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void RangeChecks(Assertions checks, ProgramModel primitives)
    {
        const string source = """
            public struct RangePair { public int A, B; }
            public class RangeOwner {
                public int A, B; public long Flags; public object R, S; public RangePair Pair; public float Floating; public bool B0, B1;
                public static int Constant(RangeOwner o, long x) { o.A = 1; o.B = -2; return o.A + o.B; }
                public static int Variable(RangeOwner o, long x) { o.A = (int)x; o.B = (int)(x >> 32); return o.A + o.B; }
                public static int Composed(RangeOwner o, long x) { o.A = (o.A & ~0xff00) | 0x8100; return o.A; }
                public static int Partial(RangeOwner o, long x) { o.A = (o.A & ~0xff00) | 0x8100; return o.A; }
                public static int Mixed(RangeOwner o, long x) { o.A = (o.A & 0xffff) | 0x12340000; o.B = (o.B & ~0xffff) | 0x5678; return o.A + o.B; }
                public static int Unsigned(RangeOwner o, long x) => (byte)((ulong)o.Flags >> 16);
                public static int Signed(RangeOwner o, long x) => (sbyte)((ulong)o.Flags >> 16);
                public static int Combined(RangeOwner o, long x) => o.A + o.B;
                public static long Packed(RangeOwner o, long x) => (uint)o.A | ((long)o.B << 32);
                public static int ReadPreserve(RangeOwner o, long x) { int a = o.A, b = o.B; o.A = 99; return a + b; }
                public static int Nested(RangeOwner o, long x) { o.Pair.A = 1; o.Pair.B = 2; return o.Pair.A + o.Pair.B; }
                public static int NestedCross(RangeOwner o, long x) { o.Pair.A = 1; o.Pair.B = 2; o.Floating = 0; return 0; }
                public static int References(RangeOwner o, long x) { o.R = null; o.S = null; return 0; }
                public static int ArrayWrite(int[] o, long x) { o[0] = 1; o[1] = 2; return o[0] + o[1]; }
                public static int ArrayPartial(int[] o, long x) { o[0] = (o[0] & ~0xff00) | 0x8100; return o[0]; }
                public static int ArrayRead(int[] o, long x) => o[0] + o[1];
                public static int ArrayIndex(int[] o, int x) { o[x] = 1; o[x+1] = 2; return 0; }
                public static int PaddingWrite(RangeOwner o, long x) { o.B = 1; o.Flags = 2; return 0; }
                public static int PaddingTail(RangeOwner o, long x) { o.B = 1; return 0; }
                public static int PaddingSlice(RangeOwner o, long x) => o.B;
                public static int PaddingRead(RangeOwner o, long x) => 0;
                public static int ReferencePartial(RangeOwner o, long x) => 0;
                public static int Booleans(RangeOwner o, long x) { o.B0 = true; o.B1 = true; return 0; }
                public static int HeaderWrite(RangeOwner o, long x) => 0;
                public static int FloatPartial(RangeOwner o, long x) => 0;
            }
            """;
        using var reference = new CompiledSource(source);
        using var tested = new CompiledSource(source);
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, bool value, int size)
        {
            var type = new TypeDef { Index = definitions.Count, Assembly = "Ranges.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public,
                IsValueType = value, IsEnum = false, Size = size, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(type); return type;
        }
        var pair = Define("RangePair", true, 8); var owner = Define("RangeOwner", false, 96);
        var fields = new List<FieldDef>();
        FieldDef Field(TypeDef type, string name, TypeRef fieldType, int offset)
        {
            var field = new FieldDef { Index = fields.Count, Owner = type, Name = name, Type = fieldType, Offset = offset, Attributes = FieldAttributes.Public };
            fields.Add(field); return field;
        }
        var integer = Primitive("Int32"); var longType = Primitive("Int64"); var ownerType = new DefinitionRef(owner, []);
        int header = (int)spec.Layout.ObjectHeaderSize;
        pair.Fields = [Field(pair, "A", integer, 0), Field(pair, "B", integer, 4)];
        owner.Fields = [Field(owner, "A", integer, header), Field(owner, "B", integer, header + 4),
            Field(owner, "Flags", longType, header + 16), Field(owner, "R", Primitive("Object"), header + 24),
            Field(owner, "S", Primitive("Object"), header + 32), Field(owner, "Pair", new DefinitionRef(pair, []), header + 40),
            Field(owner, "Floating", Primitive("Single"), header + 48), Field(owner, "B0", Primitive("Boolean"), header + 52),
            Field(owner, "B1", Primitive("Boolean"), header + 53)];
        string[] modes = ["Constant", "Variable", "Partial", "Composed", "Mixed", "Unsigned", "Signed", "Combined", "Packed", "ReadPreserve", "Nested", "NestedCross", "References",
            "ArrayWrite", "ArrayPartial", "ArrayRead", "ArrayIndex", "PaddingWrite", "PaddingTail", "PaddingSlice", "PaddingRead", "ReferencePartial", "FloatPartial", "Booleans", "HeaderWrite"];
        var methods = modes.Select((name, i) => new MethodDef { Index = i, Owner = owner, Name = name, Token = (uint)(0x06000001 + i),
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = name == "Packed" ? longType : integer,
            Parameters = [new("o", name.StartsWith("Array", StringComparison.Ordinal) ? new ArrayRef(integer, 1) : ownerType, 0, null, false),
                new("x", name == "ArrayIndex" ? integer : longType, 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = fields,
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, header); var emitter = new BodyEmitter(skeleton, types);
        foreach (var mode in modes)
        {
            var t = new TermTable(); var block = new BlockIdentity(); var root = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var argument = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            var builder = new FunctionBuilder(t, block, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            builder.Inputs.Add(new(new(SlotKind.Integer), root)); builder.Inputs.Add(new(new(SlotKind.Integer, 1), argument));
            var statements = new List<Statement>();
            Term Address(long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(offset, 64));
            Term Read(Term address, int bits) { var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), bits); statements.Add(new MemoryRead(id, address, bits, value)); return value; }
            void Write(Term address, int bits, Term value) => statements.Add(new MemoryWrite(new(), address, bits, value));
            Term Sum(Term a, Term b) => t.Apply(new CoreOperator(CoreOperation.Add), 32, a, b);
            Term result = t.Constant(0, 32);
            var start = Address(mode.StartsWith("Array", StringComparison.Ordinal) ? spec.Layout.ArrayDataStart : header);
            if (mode is "Constant" or "Variable") { Write(start, 64, mode == "Constant" ? t.Constant(0xfffffffe00000001, 64) : argument); result = Sum(Read(start, 32), Read(Address(header + 4), 32)); }
            if (mode is "Partial" or "ArrayPartial") { Write(Address((mode == "Partial" ? header : spec.Layout.ArrayDataStart) + 1), 8, t.Constant(0x81, 8)); result = Read(start, 32); }
            if (mode == "Composed") { var old = Read(start, 32); var next = t.Concat(t.Slice(old, 0, 8), t.Constant(0x81, 8), t.Slice(old, 16, 16)); Write(start, 32, next); result = Read(start, 32); }
            if (mode == "Mixed") { Write(Address(header + 2), 32, t.Constant(0x56781234, 32)); result = Sum(Read(start, 32), Read(Address(header + 4), 32)); }
            if (mode is "Unsigned" or "Signed") result = t.Apply(new CoreOperator(mode == "Signed" ? CoreOperation.SignExtend : CoreOperation.ZeroExtend), 32, Read(Address(header + 18), 8));
            if (mode is "Combined" or "ArrayRead" or "ReadPreserve") { var wide = Read(start, 64); result = Sum(t.Slice(wide, 0, 32), t.Slice(wide, 32, 32)); if (mode == "ReadPreserve") Write(start, 32, t.Constant(99, 32)); }
            if (mode == "Packed") result = Read(start, 64);
            if (mode == "Nested") { Write(Address(header + 40), 64, t.Constant(0x200000001, 64)); result = Sum(Read(Address(header + 40), 32), Read(Address(header + 44), 32)); }
            if (mode == "NestedCross") Write(Address(header + 40), 96, t.Constant(0x200000001, 96));
            if (mode == "References") Write(Address(header + 24), 128, t.Constant(0, 128));
            if (mode == "ArrayWrite") { Write(start, 64, t.Constant(0x200000001, 64)); result = Sum(Read(start, 32), Read(Address(spec.Layout.ArrayDataStart + 4), 32)); }
            if (mode == "ArrayIndex") Write(t.Apply(new CoreOperator(CoreOperation.Add), 64, start,
                t.Apply(new CoreOperator(CoreOperation.ShiftLeft), 64, t.Apply(new CoreOperator(CoreOperation.SignExtend), 64, t.Slice(argument, 0, 32)), t.Constant(2, 64))), 64, t.Constant(0x200000001, 64));
            if (mode == "PaddingWrite") Write(Address(header + 4), 160, t.Constant((System.Numerics.BigInteger.One << 96) * 2 + 1, 160));
            if (mode == "PaddingTail") Write(Address(header + 4), 96, t.Constant(1, 96));
            if (mode is "PaddingSlice" or "PaddingRead") { var wide = Read(Address(header + 4), 64); result = t.Slice(wide, mode == "PaddingSlice" ? 0 : 32, 32); }
            if (mode == "ReferencePartial") Write(Address(header + 25), 8, t.Constant(0, 8));
            if (mode == "FloatPartial") Write(Address(header + 49), 8, t.Constant(0, 8));
            if (mode == "Booleans") Write(Address(header + 52), 16, t.Constant(0x101, 16));
            if (mode == "HeaderWrite") Write(root, 192, t.Constant(0, 192));
            builder.Blocks.Add(new(block, [], statements.ToImmutableArray(), new Return([new(new(SlotKind.Integer), result.Width == 64 ? result : t.Concat(result, t.Constant(0, 32)))])));
            var method = MethodRef.Open(methods.Single(m => m.Name == mode));
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
            var lowered = new IntegerLowering(builder.Freeze(), method, binder, types, calls: calls, spec: spec).Run();
            if (mode == "HeaderWrite") { checks.True(lowered.Body is null, "对象头不能作为字段填充丢弃"); continue; }
            string? hole = mode switch { "PaddingRead" => "location.padding", "ReferencePartial" or "FloatPartial" => "location.partial-write-type", _ => null };
            if (hole is not null) { checks.True(lowered.Failure?.Reason.Code == hole, mode + " 保守报洞：" + lowered.Failure); continue; }
            checks.True(lowered.Body is not null, mode + " 范围下降：" + lowered.Failure); if (lowered.Body is null) continue;
            var problems = emitter.Emit([lowered.Body]); checks.True(problems.Count == 0, mode + " 范围 CIL 校验：" + string.Join(';', problems.Values)); if (problems.Count != 0) continue;
            var output = tested.Method("RangeOwner", mode); output.Body = skeleton.Method(method.Method).Body;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type)
            {
                if (type is Mono.Cecil.ByReferenceType byref) return new Mono.Cecil.ByReferenceType(MapType(byref.ElementType));
                if (type is Mono.Cecil.ArrayType array) return new Mono.Cecil.ArrayType(MapType(array.ElementType));
                return tested.Module.GetType(type.FullName) ?? tested.Module.ImportReference(System.Type.GetType(type.FullName, throwOnError: true)!);
            }
            foreach (var instruction in output.Body.Instructions)
                if (instruction.Operand is Mono.Cecil.FieldReference field)
                    instruction.Operand = tested.Module.GetTypes().SelectMany(x => x.Fields).Single(f => f.FullName == field.FullName);
                else if (instruction.Operand is Mono.Cecil.TypeReference type) instruction.Operand = MapType(type);
            foreach (var local in output.Body.Variables) local.VariableType = MapType(local.VariableType);
            var comparison = CilComparison.Compare(reference.Method("RangeOwner", mode), output);
            checks.True(comparison.Status == CilComparisonStatus.Match, mode + " 范围执行对照：" + comparison);
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
