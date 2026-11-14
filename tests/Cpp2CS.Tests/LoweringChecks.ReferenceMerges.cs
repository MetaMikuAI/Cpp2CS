using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
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
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;
namespace Cpp2CS.Tests;
internal static partial class LoweringChecks
{
    private static void ReferenceMergeChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").Select(t => new TypeDef {
            Index = t.Index, Assembly = t.Assembly, Namespace = t.Namespace, Name = t.Name, Token = t.Token,
            Attributes = t.Attributes, IsValueType = t.IsValueType, IsEnum = false, PackingSize = 0, ClassSizeIsDefault = true,
            Size = t.Name == "Object" ? (int)spec.Layout.ObjectHeaderSize : t.Size }).ToList();
        TypeRef Type(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        TypeDef Define(string name, TypeRef? parent = null, bool itf = false)
        {
            var d = new TypeDef { Index = definitions.Count, Assembly = "ReferenceChecks.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = TypeAttributes.Public | (itf ? TypeAttributes.Interface | TypeAttributes.Abstract : 0),
                IsValueType = false, IsEnum = false, BaseType = parent, Size = 32, PackingSize = 0, ClassSizeIsDefault = true };
            definitions.Add(d); return d;
        }
        var owner = Define("Cases", Type("Object")); var common = Define("Error", Type("Object"));
        var first = Define("FirstError", Type("Error")); var second = Define("SecondError", Type("Error"));
        Define("IItem", itf: true);
        var methods = new List<MethodDef>();
        MethodDef Method(TypeDef type, string name, TypeRef result, TypeRef[] parameters, bool instance = false)
        {
            var m = new MethodDef { Index = methods.Count, Owner = type, Name = name, Token = (uint)(0x06000001 + methods.Count),
                Attributes = MethodAttributes.Public | (instance ? 0 : MethodAttributes.Static) | (name == ".ctor" ? MethodAttributes.SpecialName | MethodAttributes.RTSpecialName : 0), ImplAttributes = 0, Slot = -1,
                ReturnType = result, Parameters = parameters.Select((p, i) => new ParameterDef("p" + i, p, 0, null, false)).ToArray() };
            methods.Add(m); return m;
        }
        var use = Method(first, "Use", Type("Void"), [], true);
        var constructor1 = Method(first, ".ctor", Type("Void"), [], true);
        var constructor2 = Method(second, ".ctor", Type("Void"), [], true);
        string[] modes = ["Common", "Memory", "SameLiteral", "DifferentLiteral", "NullLiteral", "Null", "Interface", "Array", "SameInterface", "SameArray", "Untyped", "Receiver", "Mixed", "MixedNull", "SliceNull", "SliceZero", "ReturnSliceNull", "ReturnSliceZero", "OrZero", "OrNonzero", "AndZero", "Add", "Slice", "Throw"];
        var entries = modes.ToDictionary(n => n, n => Method(owner, n, Type(n == "SameLiteral" ? "String" : n == "Throw" || n == "Receiver" ? "Void" : n is "ReturnSliceNull" or "ReturnSliceZero" ? "Int32" : n is "OrZero" or "OrNonzero" or "AndZero" ? "Boolean" : n is "Mixed" or "MixedNull" or "SliceNull" or "SliceZero" or "ReturnSliceNull" or "ReturnSliceZero" or "Add" or "Slice" ? "Int64" : "Object"),
            [Type("Boolean"), n is "Interface" or "SameInterface" ? Type("IItem") : n is "Array" or "SameArray" ? new ArrayRef(Type("FirstError"), 1) : n == "Untyped" ? Type("String") : Type("FirstError"),
                n == "SameInterface" ? Type("IItem") : n == "SameArray" ? new ArrayRef(Type("FirstError"), 1) : Type(n == "Untyped" ? "String" : "SecondError")]));
        foreach (var d in definitions.Where(d => d.Assembly == "ReferenceChecks.dll")) d.Methods = methods.Where(m => m.Owner == d).ToArray();
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var runtime = new ReferenceRuntimeMap(catalog.Functions.First(f => f.Operation.Name == "AllocateObject" && f.Signature is not null), catalog.Functions.First(f => f.Operation.Name == "ThrowManaged" && f.Signature is not null));
        var calls = new CallNamingQuery(binder, new ReferenceCodeMap(use, constructor1, constructor2), runtime, catalog);
        using var executionSource = new CompiledSource("""
            public class Error : System.Exception { }
            public class FirstError : Error { }
            public class SecondError : Error { }
            public static class Cases {
                public static void Throw(bool c, FirstError a, SecondError b) { if (c) throw new FirstError(); throw new SecondError(); }
                public static void ThrowOut(bool c, FirstError a, SecondError b) { }
                public static bool OrZero(bool c, FirstError a, SecondError b) => a == null && b == null;
                public static bool OrZeroOut(bool c, FirstError a, SecondError b) => false;
                public static bool OrNonzero(bool c, FirstError a, SecondError b) => a != null || b != null;
                public static bool OrNonzeroOut(bool c, FirstError a, SecondError b) => false;
            }
            """);
        foreach (var mode in modes)
        {
            var t = new TermTable(); var head = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity(); var join = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
            var f = new FunctionBuilder(t, head, 64, new(frame)) { ImageBase = t.Atom(new RootAtom(AddressRoot.Image), 64) };
            var args = Enumerable.Range(0, 3).Select(i => t.Atom(new EntryAtom(new(SlotKind.Integer, i)), 64)).ToArray();
            for (int i = 0; i < 3; i++) f.Inputs.Add(new(new(SlotKind.Integer, i), args[i]));
            var condition = t.Slice(args[0], 0, 1); var facts = NamingFacts.Empty;
            Return Ret(Term value) => new([new(new(SlotKind.Integer), value.Width == 64 ? value : t.Concat(value, t.Constant(0, 64 - value.Width)))]);
            if (mode is "OrZero" or "OrNonzero" or "AndZero" or "Add" or "Slice")
            {
                var value = mode == "Slice" ? t.Slice(args[1], 0, 32) : t.Apply(new CoreOperator(mode == "Add" ? CoreOperation.Add : mode == "AndZero" ? CoreOperation.And : CoreOperation.Or), 64,
                    args[1], mode == "Add" ? t.Constant(8, 64) : args[2]);
                if (mode is "OrZero" or "OrNonzero" or "AndZero") value = t.Apply(new CoreOperator(mode == "OrNonzero" ? CoreOperation.NotEqual : CoreOperation.Equal), 1, value, t.Constant(0, 64));
                f.Blocks.Add(new(head, [], [], Ret(value)));
            }
            else if (mode is "ReturnSliceNull" or "ReturnSliceZero")
            {
                var part = t.Slice(args[1], 0, 32);
                f.Blocks.Add(new(head, [], [], new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1,
                    mode == "ReturnSliceNull" ? args[1] : part, t.Constant(0, mode == "ReturnSliceNull" ? 64 : 32)), left, right)));
                f.Blocks.Add(new(left, [], [], Ret(t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, part))));
                f.Blocks.Add(new(right, [], [], Ret(t.Constant(7, 64))));
            }
            else
            {
                var a = args[1]; var b = mode == "Null" ? t.Constant(0, 64) : mode is "Mixed" or "MixedNull" or "SliceNull" or "SliceZero" ? t.Constant(7, 64) : args[2];
                var ls = new List<Statement>(); var rs = new List<Statement>();
                if (mode is "SameLiteral" or "DifferentLiteral" or "NullLiteral")
                {
                    Term Literal(ulong slot, string text, List<Statement> statements)
                    {
                        var read = new ReadIdentity(); var value = t.Atom(new ResultAtom(read), 64);
                        statements.Add(new MemoryRead(read, t.Apply(new CoreOperator(CoreOperation.Add), 64, f.ImageBase!, t.Constant(slot, 64)), 64, value));
                        facts = facts with { Slots = facts.Slots.Add(slot, Outcome<MetadataEntity>.Success(new StringEntity(text))) };
                        return value;
                    }
                    a = Literal(256, "same", ls); b = mode == "NullLiteral" ? t.Constant(0, 64) : Literal(264, mode == "DifferentLiteral" ? "other" : "same", rs);
                }
                if (mode == "Untyped")
                {
                    var read = new ReadIdentity(); a = t.Atom(new ResultAtom(read), 64);
                    ls.Add(new MemoryRead(read, t.Apply(new CoreOperator(CoreOperation.Add), 64, f.ImageBase!, t.Constant(256, 64)), 64, a));
                    facts = facts with { Slots = facts.Slots.Add(256, Outcome<MetadataEntity>.Success(new StringEntity("text"))) };
                }
                if (mode == "Throw")
                {
                    Term New(TypeRef type, List<Statement> statements, ulong slot, ulong ctor)
                    {
                        var read = new ReadIdentity(); var klass = t.Atom(new ResultAtom(read), 64);
                        statements.Add(new MemoryRead(read, t.Apply(new CoreOperator(CoreOperation.Add), 64, f.ImageBase!, t.Constant(slot, 64)), 64, klass));
                        facts = facts with { Slots = facts.Slots.Add(slot, Outcome<MetadataEntity>.Success(new ClassEntity(type))) };
                        var allocation = new CallIdentity(); var value = t.Atom(new ResultAtom(allocation), 64);
                        statements.Add(new Call(allocation, new ImageFunction(20), [new(new(SlotKind.Integer), klass)], [new(new(SlotKind.Integer), value)]));
                        statements.Add(new Call(new(), new ImageFunction(ctor), [new(new(SlotKind.Integer), value), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [])); return value;
                    }
                    a = New(Type("FirstError"), ls, 256, 11); b = New(Type("SecondError"), rs, 264, 12);
                }
                f.Blocks.Add(new(head, [], [], new Branch(mode is "MixedNull" or "SliceNull" ? t.Apply(new CoreOperator(CoreOperation.Equal), 1, a, t.Constant(0, 64)) : mode == "SliceZero" ? t.Apply(new CoreOperator(CoreOperation.Equal), 1, t.Slice(a, 0, 32), t.Constant(0, 32)) : condition, left, right)));
                var memorySlot = t.Apply(new CoreOperator(CoreOperation.Add), 64, frame, t.Constant(unchecked((ulong)-16L), 64));
                if (mode is "Memory" or "SameLiteral" or "DifferentLiteral" or "NullLiteral") { ls.Add(new MemoryWrite(new(), memorySlot, 64, a)); rs.Add(new MemoryWrite(new(), memorySlot, 64, b)); }
                f.Blocks.Add(new(left, [], [.. ls], new Jump(join))); f.Blocks.Add(new(right, [], [.. rs], new Jump(join)));
                var id = new MergeIdentity(); var merged = mode is "SliceNull" or "SliceZero" ? t.Constant(0, 64) : t.Atom(new ResultAtom(id), 64);
                var statements = mode == "Throw" ? new Statement[] { new Call(new(), new ImageFunction(30), [new(new(SlotKind.Integer), merged), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [], true) }
                    : mode == "Receiver" ? [new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), merged), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], [])] : [];
                if (mode is "Memory" or "SameLiteral" or "DifferentLiteral" or "NullLiteral")
                {
                    var read = new ReadIdentity(); var value = t.Atom(new ResultAtom(read), 64);
                    f.Blocks.Add(new(join, [], [new MemoryRead(read, memorySlot, 64, value)], Ret(value)));
                }
                else if (mode is "SliceNull" or "SliceZero")
                {
                    var narrow = t.Atom(new ResultAtom(id), 32);
                    f.Blocks.Add(new(join, [new(id, narrow, [new(left, t.Slice(a, 0, 32)), new(right, t.Constant(7, 32))])], [], Ret(t.Apply(new CoreOperator(CoreOperation.ZeroExtend), 64, narrow))));
                }
                else f.Blocks.Add(new(join, [new(id, merged, [new(left, a), new(right, b)])], [.. statements], mode == "Throw" ? new Unreachable() : mode == "Receiver" ? new Return([]) : Ret(merged)));
            }
            var lowered = new IntegerLowering(f.Freeze(), MethodRef.Open(entries[mode]), binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            var code = mode switch { "Receiver" => "lowering.Merge.StaticType", "Mixed" => "lowering.Merge.Reference", "Add" or "AndZero" or "Slice" or "SliceZero" or "ReturnSliceZero" => "hole", _ => null };
            if (code is not null) { checks.True(code == "hole" ? lowered.Failure is not null : lowered.Failure?.Reason.Code == code, mode + " 引用边界：" + lowered.Failure); continue; }
            checks.True(lowered.Body is not null, mode + " 引用合流下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            checks.True(emitter.Emit([body]).Count == 0, mode + " 引用合流 CIL 校验");
            if (mode is "Throw" or "OrZero" or "OrNonzero")
            {
                var output = executionSource.Method("Cases", mode + "Out"); output.Body = skeleton.Method(entries[mode]).Body;
                var core = executionSource.Module.TypeSystem.Object.Resolve().Module;
                Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => executionSource.Module.ImportReference(executionSource.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
                foreach (var local in output.Body.Variables) local.VariableType = MapType(local.VariableType);
                foreach (var instruction in output.Body.Instructions)
                    instruction.Operand = instruction.Operand switch {
                        Mono.Cecil.MethodReference call => executionSource.Module.ImportReference(executionSource.Module.GetType(call.DeclaringType.FullName).Methods.Single(m => m.FullName == call.FullName)),
                        Mono.Cecil.TypeReference type => MapType(type),
                        Mono.Cecil.ParameterDefinition parameter => output.Parameters[parameter.Index],
                        _ => instruction.Operand };
                var comparison = CilComparison.Compare(executionSource.Method("Cases", mode), output);
                checks.True(comparison.Status == CilComparisonStatus.Match, mode + " 执行对照：" + comparison);
                if (mode == "Throw") checks.True(comparison.Coverage?.Branches.All(b => b.Directions.All(x => x)) == true, "合流后两条路径分别抛出原分配的异常类型");
            }
            if (mode == "SameLiteral") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value is StringValue { Text: "same" }, "同值字符串的合流仍能读取原字符串常量");
            if (mode is "DifferentLiteral" or "NullLiteral") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value is not StringValue, "不同字符串或空来源不能取得同值字符串视图");
            if (mode is "Common" or "Memory" or "Null") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value!.Type.Equals(Type(mode == "Null" ? "FirstError" : "Error")), mode + " 按定义取最近公共祖先，空不约束类型");
            if (mode == "Throw") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedThrow>().Single().Exception.Type.Equals(Type("Error")), "不同分配合流后以公共祖先抛出");
            if (mode is "Interface" or "Array") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value!.Type.Equals(types.Object), mode + " 合流取 object");
            if (mode == "Untyped") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value!.Type.Equals(types.String), "字符串实体与字符串形参合流保持 string 类型");
            if (mode is "SameInterface" or "SameArray") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedReturn>().Single().Value!.Type.Equals(mode == "SameInterface" ? Type("IItem") : new ArrayRef(Type("FirstError"), 1)), mode + " 同型的接口、数组合流保持原类型");
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
    private sealed class ReferenceCodeMap(params MethodDef[] methods) : IBindingCodeMap
    {
        public ImmutableArray<BindingEntry> At(ulong address) => address >= 10 && address < (ulong)(10 + methods.Length) ? [new(MethodRef.Open(methods[(int)address - 10]), BindingEntryKind.Ordinary)] : [];
    }
    private sealed class ReferenceRuntimeMap(RuntimeFunction allocation, RuntimeFunction throwing) : IRuntimeFunctionMap
    {
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction f ? f.EntryOffset switch { 20 => allocation, 30 => throwing, _ => null } : null;
    }
}
