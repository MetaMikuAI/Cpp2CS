using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    internal static void ArrayStoreChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        TypeRef Type(string name) => new DefinitionRef(primitives.Types.Single(t => t.Assembly == "mscorlib.dll" && t.Name == name), []);
        var owner = new TypeDef { Index = primitives.Types.Count, Assembly = "ArrayChecks.dll", Namespace = "", Name = "ArrayChecks", Token = 0x02000001,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        string[] modes = ["Parameter", "Allocated", "Bounds", "BoundsIndexed", "BoundsSignedIndex", "BoundsConstant", "BoundsWideLength", "BoundsWrongIndex", "NoValueNull", "OtherClassArray", "WrongThrow", "NoStore", "OtherValue", "OtherArray", "InterveningCall", "ValueElement", "ExtraEvent"];
        var methods = modes.Select((mode, i) => new MethodDef { Index = primitives.Methods.Count + i, Owner = owner, Name = mode, Token = (uint)(0x06000001 + i),
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = Type("Void"),
            Parameters = [new("array", new ArrayRef(mode == "ValueElement" ? Type("Int32") : Type("Object"), 1), 0, null, false),
                new("value", mode == "ValueElement" ? Type("Int32") : Type("Object"), 0, null, false), new("other", new ArrayRef(Type("Object"), 1), 0, null, false), new("index", Type(mode == "BoundsWideLength" ? "IntPtr" : "Int32"), 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var exceptionType = new TypeDef { Index = primitives.Types.Count + 1, Assembly = "mscorlib.dll", Namespace = "System", Name = "IndexOutOfRangeException", Token = 0x0200ffff,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, BaseType = Type("Object") };
        var exceptionConstructor = new MethodDef { Index = primitives.Methods.Count + methods.Length, Owner = exceptionType, Name = ".ctor", Token = 0x0600ffff,
            Attributes = MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, ImplAttributes = 0, Slot = -1, ReturnType = Type("Void"), Parameters = [] };
        exceptionType.Methods = [exceptionConstructor];
        var definitions = primitives.Types.Append(owner).Append(exceptionType).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = [.. primitives.Methods, .. methods, exceptionConstructor], Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var method in methods)
        {
            string mode = method.Name;
            var t = new TermTable(); var entry = new BlockIdentity(); var nonnull = new BlockIdentity(); var test = new BlockIdentity(); var passed = new BlockIdentity(); var failed = new BlockIdentity(); var done = new BlockIdentity();
            var bounds = new BlockIdentity(); var boundFail = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var slot = new AbstractSlot(SlotKind.Integer); var array = t.Atom(new EntryAtom(slot), 64); var value = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64); var other = t.Atom(new EntryAtom(new(SlotKind.Integer, 2)), 64);
            var builder = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
            var indexInput = t.Atom(new EntryAtom(new(SlotKind.Integer, 3)), 64);
            builder.Inputs.Add(new(new(SlotKind.Integer, 3), indexInput));
            builder.Inputs.AddRange(new[] { new EntryInput(slot, array), new EntryInput(new(SlotKind.Integer, 1), value), new EntryInput(new(SlotKind.Integer, 2), other) });
            Term Op(CoreOperation op, int width, params Term[] values) => t.Apply(new CoreOperator(op), width, values);
            Term Add(Term root, long offset) => Op(CoreOperation.Add, 64, root, t.Constant(offset, 64));
            Term Read(List<Statement> statements, Term address, int width = 64)
            { var id = new ReadIdentity(); var result = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, result)); return result; }
            Call Runtime(string operation, Term[] inputs, out Term? result)
            {
                var function = catalog.Functions.First(f => f.Operation.Name == operation && f.Signature is not null);
                var signature = binder.Classify(function.Signature!).Value!; var id = new CallIdentity();
                result = signature.Slots.Return.Pieces.IsEmpty ? null : t.Atom(new ResultAtom(id), 64);
                return new(id, new NamedFunction(function.MangledName), inputs.Select((v, i) => new SlotValue(signature.Slots.Parameters[i].Pieces.Single().Slot, v)).ToImmutableArray(),
                    result is null ? [] : [new(signature.Slots.Return.Pieces.Single().Slot, result)], function.Operation.DoesNotReturn);
            }
            var prefix = new List<Statement>();
            var facts = NamingFacts.Empty;
            if (mode == "Allocated")
            {
                var cls = Read(prefix, Add(image, 128));
                prefix.Add(Runtime("AllocateVector", [cls, t.Constant(1, 64)], out var allocated)); array = allocated!;
                facts = facts with { Slots = facts.Slots.Add(128, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(new ArrayRef(Type("Object"), 1)))) };
            }
            builder.Blocks.Add(new(entry, [], prefix.ToImmutableArray(), new Branch(Op(CoreOperation.Equal, 1, array, t.Constant(0, 64)), done, nonnull)));
            builder.Blocks.Add(new(nonnull, [], [], mode == "NoValueNull" || mode == "ValueElement" ? new Jump(test)
                : new Branch(Op(CoreOperation.Equal, 1, value, t.Constant(0, 64)), passed, test)));
            var body = new List<Statement>();
            if (mode != "ValueElement")
            {
                var klass = Read(body, Add(mode == "OtherClassArray" ? other : array, spec.Layout.Field("Il2CppObject", "klass").ByteOffset));
                var element = Read(body, Add(klass, spec.Layout.Field("Il2CppClass", "element_class").ByteOffset));
                body.Add(Runtime("IsInstance", [value, element], out var result));
                if (mode == "ExtraEvent") body.Add(new Call(new(), new ComputedTarget(value), [], []));
                builder.Blocks.Add(new(test, [], body.ToImmutableArray(), new Branch(Op(CoreOperation.Equal, 1, result!, t.Constant(0, 64)), failed, passed)));
                var failing = new List<Statement>();
                failing.Add(Runtime("NewArrayTypeMismatchException", [], out var exception));
                failing.Add(Runtime(mode == "WrongThrow" ? "ThrowNullReference" : "ThrowManaged", mode == "WrongThrow" ? [] : [exception!, t.Constant(0, 64)], out _));
                builder.Blocks.Add(new(failed, [], failing.ToImmutableArray(), new Unreachable()));
            }
            else builder.Blocks.Add(new(test, [], [], new Jump(passed)));
            var stores = new List<Statement>();
            if (mode == "InterveningCall") stores.Add(new Call(new(), new ComputedTarget(value), [], []));
            var target = Add(mode == "OtherArray" ? other : array, spec.Layout.Field("Il2CppArraySize", "vector").ByteOffset);
            if (mode is "BoundsIndexed" or "BoundsSignedIndex") target = Op(CoreOperation.Add, 64, target, Op(CoreOperation.ShiftLeft, 64,
                Op(mode == "BoundsSignedIndex" ? CoreOperation.SignExtend : CoreOperation.ZeroExtend, 64, t.Slice(indexInput, 0, 32)), t.Constant(3, 64)));
            if (mode == "BoundsWideLength") target = Op(CoreOperation.Add, 64, target, Op(CoreOperation.ShiftLeft, 64, indexInput, t.Constant(3, 64)));
            if (mode is "BoundsWrongIndex" or "BoundsConstant") target = Add(target, types.PointerSize);
            if (mode != "NoStore") stores.Add(new MemoryWrite(new(), target, mode == "ValueElement" ? 32 : 64, mode == "OtherValue" ? other : mode == "ValueElement" ? t.Slice(value, 0, 32) : value));
            builder.Blocks.Add(new(passed, [], mode.StartsWith("Bounds", StringComparison.Ordinal) ? [] : stores.ToImmutableArray(), mode.StartsWith("Bounds", StringComparison.Ordinal) ? new Jump(bounds) : new Jump(done)));
            if (mode.StartsWith("Bounds", StringComparison.Ordinal))
            {
                var reads = new List<Statement>(); var length = Read(reads, Add(array, spec.Layout.Field("Il2CppArray", "max_length").ByteOffset), 32);
                var store = new BlockIdentity();
                var within = Op(CoreOperation.UnsignedLess, 1, mode is "BoundsIndexed" or "BoundsSignedIndex" ? t.Slice(indexInput, 0, 32) : t.Constant(0, 32), length);
                if (mode == "BoundsWideLength") within = Op(CoreOperation.UnsignedLess, 1, indexInput, Op(CoreOperation.ZeroExtend, 64, length));
                if (mode == "BoundsConstant")
                {
                    var carry = t.Slice(Op(CoreOperation.Add, 33, Op(CoreOperation.ZeroExtend, 33, length), t.Constant(uint.MaxValue, 33)), 32, 1);
                    within = Op(CoreOperation.And, 1, carry, Op(CoreOperation.NotEqual, 1, length, t.Constant(1, 32)));
                }
                builder.Blocks.Add(new(bounds, [], reads.ToImmutableArray(), new Branch(within, store, boundFail)));
                builder.Blocks.Add(new(store, [], stores.ToImmutableArray(), new Jump(done)));
                builder.Blocks.Add(new(boundFail, [], [Runtime("ThrowBounds", [], out _)], new Unreachable()));
            }
            builder.Blocks.Add(new(done, [], [], new Return([])));
            var state = new StateQueries(); var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
            var names = new ValueNamingQuery(state, calls, facts, spec, binder, binder.Entry(MethodRef.Open(method), BindingEntryKind.Ordinary).Value);
            var transformed = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot>()).Run(builder.Freeze());
            checks.True(ExitChecker.Check(transformed.Function).IsValid, mode + " 数组检查结构契约");
            bool folded = mode is not ("NoValueNull" or "OtherClassArray" or "WrongThrow" or "ValueElement" or "ExtraEvent");
            checks.True(transformed.Records.Any(r => r.Kind == "array-store-check" && r.Removed) == folded, mode + " 数组检查折叠：" + string.Join(';', transformed.Records.Where(r => r.Why is not null).Select(r => r.Why)));
            if (!folded && mode != "ValueElement")
            {
                checks.True(transformed.Records.Any(r => r.Why?.Code.StartsWith("structure.array-store-check.", StringComparison.Ordinal) == true), mode + " 数组检查拒绝原因"); continue;
            }
            var lowered = new IntegerLowering(transformed.Function, MethodRef.Open(method), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            if (mode is "NoStore" or "OtherValue" or "OtherArray" or "InterveningCall" or "BoundsWrongIndex")
                checks.True(lowered.Failure?.Reason.Code == "lowering.ArrayStoreCheck", mode + " 未配对存入必须报洞：" + lowered.Failure);
            else
            {
                checks.True(lowered.Body is not null, mode + " 检查由元素写入吸收：" + lowered.Failure);
                if (lowered.Body is { } managed)
                {
                    checks.True(emitter.Emit([managed]).Count == 0, mode + " 数组写入 CIL 契约");
                    checks.True(skeleton.Method(method).Body.Instructions.Any(i => i.OpCode.Code is Mono.Cecil.Cil.Code.Stelem_Ref or Mono.Cecil.Cil.Code.Stelem_I4 or Mono.Cecil.Cil.Code.Stelem_Any), mode + " 输出元素存入指令");
                }
            }
        }
        // object[] array = new string[1]; array[1] = new object() 同时越界且类型不符。
        // ECMA-335 未规定 stelem 此时的异常优先级；IL2CPP 先检查类型，CLR 先检查越界。恢复仍输出原指令，由同一执行器对照。
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}

internal static class ArrayStoreCheckOnly
{
    public const string Command = "array-store-check";
    public static int Run()
    {
        string[] names = ["Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr", "UIntPtr", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference", "Void"];
        var definitions = names.Select((name, i) => new TypeDef { Index = i, Assembly = "mscorlib.dll", Namespace = "System", Name = name,
            Token = (uint)(0x02000001 + i), Attributes = TypeAttributes.Public, IsValueType = name is not ("Object" or "String"), IsEnum = false }).ToArray();
        var primitives = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = [], Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = [new AssemblyDef { Name = "mscorlib.dll", AssemblyName = "mscorlib", Version = new(1, 0), Culture = "", PublicKey = [], Types = definitions }] };
        var checks = new Assertions(); LoweringChecks.ArrayStoreChecks(checks, primitives); return checks.Finish("数组存入检查");
    }
}
