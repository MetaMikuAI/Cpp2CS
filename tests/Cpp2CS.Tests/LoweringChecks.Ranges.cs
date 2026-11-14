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
using ManagedValues = Cpp2CS.Managed.ManagedValues;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void RangeChecks(Assertions checks, ProgramModel primitives)
    {
        const string source = """
            public struct RangePair { public int A, B; }
            public struct RangeBlock { public double A, B; }
            public struct RangeQuad { public float A, B, C, D; }
            public struct RangePadded { public byte A; public long B; }
            public class RangeOwner {
                public int A, B; public long Flags; public object R, S; public RangePair Pair; public float Floating; public bool B0, B1;
                public RangeBlock Block, Other; public double D0, D1; public float F0, F1, F2, F3;
                public RangePadded Padded; public RangeQuad Quad;
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
                public static int WideCopy(RangeOwner o, long x) { o.Other = o.Block; return 0; }
                public static int WidePairCopy(RangeOwner o, RangeOwner x) { o.Block = x.Block; o.Other = x.Other; return 0; }
                public static int WidePairZero(RangeOwner o, long x) { o.Block = default; o.Other = default; return 0; }
                public static int WideZero(RangeOwner o, long x) { o.Block = default; return 0; }
                public static int WideDoubles(RangeOwner o, long x) { o.D0 = o.Block.A; o.D1 = o.Block.B; return 0; }
                public static int WideFloats(RangeOwner o, long x) { o.F0 = o.Quad.A; o.F1 = o.Quad.B; o.F2 = o.Quad.C; o.F3 = o.Quad.D; return 0; }
                public static int WideFieldsZero(RangeOwner o, long x) { o.F0 = o.F1 = o.F2 = o.F3 = 0; return 0; }
                public static int WideConstants(RangeOwner o, long x) { o.F0 = 1; o.F1 = 2; o.F2 = 3; o.F3 = 4; return 0; }
                public static int WideConcat(RangeOwner o, long x) { o.Block.A = o.D0; o.Block.B = o.D1; return 0; }
                public static int WideSlice(RangeOwner o, long x) { float value = o.Quad.C; o.Quad = default; return value == 0 ? 1 : 0; }
                public static int WideReadPreserve(RangeOwner o, long x) { var old = o.Block; o.Block = default; o.D0 = old.A; o.D1 = old.B; return 0; }
                public static int WideMerge(RangeOwner o, long x) { var value = (x & 1) != 0 ? o.Block : o.Other; o.D0 = value.A; o.D1 = value.B; return 0; }
                public static int WideArithmetic(RangeOwner o, long x) => 0;
                public static int WideDestPartial(RangeOwner o, long x) => 0;
                public static int WideSourcePartial(RangeOwner o, long x) => 0;
                public static int WideCrossObject(RangeOwner o, long x) => 0;
                public static int WidePadding(RangeOwner o, long x) { o.Padded = default; return 0; }
                public static int ArrayToFrame(RangeBlock[] o, long x) { var value = o[0]; return Touch(ref value); }
                public static int StackStructCopy(RangeOwner o, double p0, double p1, double p2, double p3, double p4, double p5, double p6, double p7, RangeBlock value) { o.Block = value; return 0; }
                public static int Touch(ref RangeBlock value) { value.A += 1; return (int)value.A; }
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
        var pair = Define("RangePair", true, 8); var owner = Define("RangeOwner", false, 176);
        var wideBlock = Define("RangeBlock", true, 16); var quad = Define("RangeQuad", true, 16); var padded = Define("RangePadded", true, 16);
        var fields = new List<FieldDef>();
        FieldDef Field(TypeDef type, string name, TypeRef fieldType, int offset)
        {
            var field = new FieldDef { Index = fields.Count, Owner = type, Name = name, Type = fieldType, Offset = offset, Attributes = FieldAttributes.Public };
            fields.Add(field); return field;
        }
        var integer = Primitive("Int32"); var longType = Primitive("Int64"); var ownerType = new DefinitionRef(owner, []);
        int header = (int)spec.Layout.ObjectHeaderSize;
        pair.Fields = [Field(pair, "A", integer, 0), Field(pair, "B", integer, 4)];
        wideBlock.Fields = [Field(wideBlock, "A", Primitive("Double"), 0), Field(wideBlock, "B", Primitive("Double"), 8)];
        quad.Fields = [Field(quad, "A", Primitive("Single"), 0), Field(quad, "B", Primitive("Single"), 4), Field(quad, "C", Primitive("Single"), 8), Field(quad, "D", Primitive("Single"), 12)];
        padded.Fields = [Field(padded, "A", Primitive("Byte"), 0), Field(padded, "B", longType, 8)];
        owner.Fields = [Field(owner, "A", integer, header), Field(owner, "B", integer, header + 4),
            Field(owner, "Flags", longType, header + 16), Field(owner, "R", Primitive("Object"), header + 24),
            Field(owner, "S", Primitive("Object"), header + 32), Field(owner, "Pair", new DefinitionRef(pair, []), header + 40),
            Field(owner, "Floating", Primitive("Single"), header + 48), Field(owner, "B0", Primitive("Boolean"), header + 52),
            Field(owner, "B1", Primitive("Boolean"), header + 53),
            Field(owner, "Block", new DefinitionRef(wideBlock, []), header + 56), Field(owner, "Other", new DefinitionRef(wideBlock, []), header + 72),
            Field(owner, "D0", Primitive("Double"), header + 88), Field(owner, "D1", Primitive("Double"), header + 96),
            Field(owner, "F0", Primitive("Single"), header + 104), Field(owner, "F1", Primitive("Single"), header + 108),
            Field(owner, "F2", Primitive("Single"), header + 112), Field(owner, "F3", Primitive("Single"), header + 116),
            Field(owner, "Padded", new DefinitionRef(padded, []), header + 120), Field(owner, "Quad", new DefinitionRef(quad, []), header + 136)];
        string[] modes = ["Constant", "Variable", "Partial", "Composed", "Mixed", "Unsigned", "Signed", "Combined", "Packed", "ReadPreserve", "Nested", "NestedCross", "References",
            "ArrayWrite", "ArrayPartial", "ArrayRead", "ArrayIndex", "PaddingWrite", "PaddingTail", "PaddingSlice", "PaddingRead", "ReferencePartial", "FloatPartial", "Booleans", "HeaderWrite",
            "WideCopy", "WidePairCopy", "WidePairZero", "WideZero", "WideDoubles", "WideFloats", "WideFieldsZero", "WideConstants", "WideConcat", "WideSlice", "WideReadPreserve", "WideMerge", "WideArithmetic", "WideDestPartial", "WideSourcePartial", "WideCrossObject", "WidePadding", "ArrayToFrame", "StackStructCopy"];
        var methods = modes.Select((name, i) => new MethodDef { Index = i, Owner = owner, Name = name, Token = (uint)(0x06000001 + i),
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = name == "Packed" ? longType : integer,
            Parameters = name == "StackStructCopy"
                ? [new("o", ownerType, 0, null, false), .. Enumerable.Range(0, 8).Select(p => new ParameterDef("p" + p, Primitive("Double"), 0, null, false)), new("value", new DefinitionRef(wideBlock, []), 0, null, false)]
                : [new("o", name == "ArrayToFrame" ? new ArrayRef(new DefinitionRef(wideBlock, []), 1) : name.StartsWith("Array", StringComparison.Ordinal) ? new ArrayRef(integer, 1) : ownerType, 0, null, false),
                new("x", name == "WidePairCopy" ? ownerType : name == "ArrayIndex" ? integer : longType, 0, null, false)] }).ToArray();
        var touch = new MethodDef { Index = methods.Length, Owner = owner, Name = "Touch", Token = (uint)(0x06000001 + methods.Length),
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = integer,
            Parameters = [new("value", new ByRefRef(new DefinitionRef(wideBlock, [])), 0, null, false)] };
        methods = [.. methods, touch];
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
            if (mode == "WideCopy") Write(Address(header + 72), 128, Read(Address(header + 56), 128));
            if (mode == "WidePairCopy") Write(Address(header + 56), 256, Read(t.Apply(new CoreOperator(CoreOperation.Add), 64, argument, t.Constant(header + 56, 64)), 256));
            if (mode == "WidePairZero") Write(Address(header + 56), 256, t.Constant(0, 256));
            if (mode == "WideZero") Write(Address(header + 56), 128, t.Constant(0, 128));
            if (mode == "WideDoubles") Write(Address(header + 88), 128, Read(Address(header + 56), 128));
            if (mode == "WideFloats") Write(Address(header + 104), 128, Read(Address(header + 136), 128));
            if (mode == "WideFieldsZero") Write(Address(header + 104), 128, t.Constant(0, 128));
            if (mode == "WideConstants") Write(Address(header + 104), 128, t.Concat(t.Constant(0x400000003f800000, 64), t.Constant(0x4080000040400000, 64)));
            if (mode == "WideConcat") Write(Address(header + 56), 128, t.Concat(Read(Address(header + 88), 64), Read(Address(header + 96), 64)));
            if (mode == "WideSlice") { result = t.Apply(new CoreOperator(CoreOperation.FloatEqual), 1, t.Slice(Read(Address(header + 136), 128), 64, 32), t.Constant(0, 32)); Write(Address(header + 136), 128, t.Constant(0, 128)); }
            if (mode == "WideReadPreserve") { var old = Read(Address(header + 56), 128); Write(Address(header + 56), 128, t.Constant(0, 128)); Write(Address(header + 88), 128, old); }
            if (mode == "WideDestPartial") Write(Address(header + 89), 128, t.Constant(0, 128));
            if (mode == "WideSourcePartial") Write(Address(header + 88), 128, Read(Address(header + 57), 128));
            if (mode == "WideCrossObject") Write(Address(168), 128, t.Constant(0, 128));
            if (mode == "WidePadding") Write(Address(header + 120), 128, t.Constant(0, 128));
            // 零扩展后加常量的进位已由规范化归一成比较；这里用宽乘法作真正的宽算术。
            if (mode == "WideArithmetic") result = t.Slice(t.Apply(new CoreOperator(CoreOperation.Multiply), 65,
                t.Concat(argument, t.Constant(0, 1)), t.Concat(argument, t.Constant(0, 1))), 64, 1);
            if (mode == "ArrayToFrame")
            {
                var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
                Write(frame, 128, Read(start, 128));
                var call = new CallIdentity(); var returned = t.Atom(new ResultAtom(call), 64);
                statements.Add(new Call(call, new ImageFunction(10), [new(new(SlotKind.Integer), frame), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [new(new(SlotKind.Integer), returned)]));
                result = t.Slice(returned, 0, 32);
            }
            if (mode == "StackStructCopy")
            {
                var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
                builder.IncomingArgumentArea = frame;
                for (int p = 0; p < 8; p++) builder.Inputs.Add(new(new(SlotKind.Floating, p), t.Atom(new EntryAtom(new(SlotKind.Floating, p)), 128)));
                Write(Address(header + 56), 128, Read(frame, 128));
            }
            if (mode == "WideMerge")
            {
                var yes = new BlockIdentity(); var no = new BlockIdentity(); var join = new BlockIdentity();
                var a = Read(Address(header + 56), 128); var first = statements[^1]; statements.Clear();
                var b = Read(Address(header + 72), 128); var second = statements[^1]; statements.Clear();
                var merge = new MergeIdentity(); var value = t.Atom(new ResultAtom(merge), 128);
                Write(Address(header + 88), 128, value);
                builder.Blocks.Add(new(block, [], [], new Branch(t.Slice(argument, 0, 1), yes, no)));
                builder.Blocks.Add(new(yes, [], [first], new Jump(join)));
                builder.Blocks.Add(new(no, [], [second], new Jump(join)));
                builder.Blocks.Add(new(join, [new(merge, value, [new(yes, a), new(no, b)])], statements.ToImmutableArray(), new Return([new(new(SlotKind.Integer), t.Constant(0, 64))])));
            }
            else builder.Blocks.Add(new(block, [], statements.ToImmutableArray(), new Return([new(new(SlotKind.Integer), result.Width == 64 ? result : t.Concat(result, t.Constant(0, 32)))])));
            var method = MethodRef.Open(methods.Single(m => m.Name == mode));
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(MethodRef.Open(touch), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
            var lowered = new IntegerLowering(builder.Freeze(), method, binder, types, calls: calls, effects: new Cpp2CS.Pipeline.ManagedCallEffects(calls), spec: spec).Run();
            if (mode == "HeaderWrite") { checks.True(lowered.Body is null, "对象头不能作为字段填充丢弃"); continue; }
            string? hole = mode switch { "PaddingRead" => "location.padding", "ReferencePartial" or "FloatPartial" => "location.partial-write-type",
                "WideArithmetic" => "lowering.FloatingOrVector",
                "WideDestPartial" or "WideSourcePartial" or "WideCrossObject" => "lowering.Wide.Layout", _ => null };
            if (hole is not null) { checks.True(lowered.Failure?.Reason.Code == hole, mode + " 保守报洞：" + lowered.Failure); continue; }
            checks.True(lowered.Body is not null, mode + " 范围下降：" + lowered.Failure); if (lowered.Body is null) continue;
            if (mode.StartsWith("Wide", StringComparison.Ordinal) || mode is "ArrayToFrame" or "StackStructCopy")
                checks.True(lowered.Body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                    .SelectMany(ManagedValues.Walk).All(v => v.Width <= 64), mode + " 不生成宽整数托管值");
            if (mode is "WideCopy" or "WideZero" or "StackStructCopy")
                checks.True(lowered.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedStore>()
                    .Any(s => s.Value.Type.Equals(new DefinitionRef(wideBlock, []))), mode + " 保留结构体整体赋值");
            if (mode is "WidePairCopy" or "WidePairZero")
                checks.True(lowered.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedStore>()
                    .Count(s => s.Value.Type.Equals(new DefinitionRef(wideBlock, []))) == 2, mode + " 按完整结构体字段拆分");
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
                else if (instruction.Operand is Mono.Cecil.MethodReference called && called.DeclaringType.FullName == "RangeOwner")
                    instruction.Operand = tested.Module.GetTypes().SelectMany(x => x.Methods).Single(m => m.FullName == called.FullName);
                else if (instruction.Operand is Mono.Cecil.TypeReference type) instruction.Operand = MapType(type);
            foreach (var local in output.Body.Variables) local.VariableType = MapType(local.VariableType);
            var comparison = CilComparison.Compare(reference.Method("RangeOwner", mode), output);
            checks.True(comparison.Status == CilComparisonStatus.Match, mode + " 范围执行对照：" + comparison);
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
