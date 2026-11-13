using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
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
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void InlineTypeChecks(Assertions checks, ProgramModel primitives)
    {
        using var source = new CompiledSource("""
            public class Parent { }
            public sealed class Final : Parent { }
            public sealed class Other { }
            public static class TypeCases {
                public static Parent HierIs(object value) => value as Parent;
                public static Parent HierCast(object value) => (Parent)value;
                public static Final ExactIs(object value) => value as Final;
                public static Final ExactCast(object value) => (Final)value;
                public static Final Materialized(object value) => value as Final;
                public static Parent HierMaterialized(object value) => value as Parent;
                public static Parent HierIntervening(object value) => value as Parent;
                public static object ExactBoxed(object value) => value is int ? value : null;
                public static Final SelectedBranch(object value) => value as Final;
                public static bool ExactPredicate(object value) => value is Final;
                public static bool HierPredicate(object value) => value is Parent;
                public static Final CastAlternatives(object left, object right, bool takeLeft) => (Final)(takeLeft ? left : right);
            }
            """);
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var throwFunction = catalog.Functions.First(f => f.Operation.Name == "ThrowInvalidCast" && f.Signature is not null);
        var definitions = primitives.Types.Where(d => d.Assembly == "mscorlib.dll" && d.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(d => d.Name == name), []);
        TypeDef Define(string name, TypeAttributes attributes, TypeRef? parent = null)
        {
            var d = new TypeDef { Index = definitions.Count, Assembly = "InlineChecks.dll", Namespace = "", Name = name,
                Token = (uint)(0x02000001 + definitions.Count), Attributes = attributes, IsValueType = false, IsEnum = false, BaseType = parent ?? Primitive("Object") };
            definitions.Add(d); return d;
        }
        var parent = Define("Parent", TypeAttributes.Public); var parentType = new DefinitionRef(parent, []);
        var final = Define("Final", TypeAttributes.Public | TypeAttributes.Sealed, parentType); var finalType = new DefinitionRef(final, []);
        Define("Other", TypeAttributes.Public | TypeAttributes.Sealed);
        var iface = Define("IParent", TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract);
        var owner = Define("TypeCases", TypeAttributes.Public);
        string[] cases = ["HierIs", "HierCast", "ExactIs", "ExactCast", "Materialized", "HierMaterialized", "HierIntervening", "ExactBoxed", "SelectedBranch", "HierRepeatedDepth", "ExactPredicate", "HierPredicate", "CastAlternatives", "DepthConstant", "HierMaterializedOther", "Interface", "Array", "NonSealed", "Split", "NoNull", "WrongThrow", "ExtraEvent", "ForeignFailureRead", "Unwind"];
        var methods = cases.Select((name, index) => new MethodDef { Index = index, Owner = owner, Name = name,
            Token = (uint)(0x06000001 + index), Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1,
            ReturnType = name.Contains("Predicate", StringComparison.Ordinal) ? Primitive("Boolean") : name == "ExactBoxed" ? Primitive("Object") : name.StartsWith("Hier", StringComparison.Ordinal) ? parentType : finalType,
            Parameters = name == "CastAlternatives" ? [new("left", Primitive("Object"), 0, null, false), new("right", Primitive("Object"), 0, null, false), new("takeLeft", Primitive("Boolean"), 0, null, false)]
                : name == "ForeignFailureRead" ? [new("value", Primitive("Object"), 0, null, false), new("other", Primitive("Object"), 0, null, false)] : [new("value", Primitive("Object"), 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var program = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(program, layouts, 8); var skeleton = new Skeleton(program, 16); var emitter = new BodyEmitter(skeleton, types);
        foreach (var method in methods)
        {
            string mode = method.Name;
            bool hierarchy = mode.StartsWith("Hier", StringComparison.Ordinal) || mode is "DepthConstant" or "Interface" or "Split" or "ExtraEvent";
            bool cast = mode.EndsWith("Cast", StringComparison.Ordinal) || mode is "WrongThrow" or "Unwind" or "CastAlternatives" or "ForeignFailureRead";
            bool materialized = mode.Contains("Materialized", StringComparison.Ordinal);
            var t = new TermTable(); var entry = new BlockIdentity(); var check = new BlockIdentity(); var elementBlock = hierarchy ? new BlockIdentity() : check;
            var middle = new BlockIdentity(); var success = new BlockIdentity(); var failed = new BlockIdentity(); var different = new BlockIdentity(); var handler = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var slot = new AbstractSlot(SlotKind.Integer); var obj = t.Atom(new EntryAtom(slot), 64);
            var builder = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image }; builder.Inputs.Add(new(slot, obj));
            Term Op(CoreOperation operation, int width, params Term[] values) => t.Apply(new CoreOperator(operation), width, values);
            Term Offset(Term root, long offset) => Op(CoreOperation.Add, 64, root, t.Constant(offset, 64));
            Term Read(List<Statement> statements, Term address, int width = 64)
            {
                var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, value)); return value;
            }
            var prefix = new List<Statement>(); var klass = Read(prefix, Offset(image, 128));
            Term? oldDepth = null;
            if (mode == "HierRepeatedDepth")
            {
                oldDepth = Read(prefix, Offset(klass, spec.Layout.Field("Il2CppClass", "typeHierarchyDepth").ByteOffset), 8);
                prefix.Add(new Call(new(), new ComputedTarget(obj), [], []));
            }
            var first = new List<Statement>(); var objectClass = Read(first, Offset(obj, spec.Layout.Field("Il2CppObject", "klass").ByteOffset));
            var last = hierarchy ? new List<Statement>() : first;
            Term compare = Op(CoreOperation.Equal, 1, objectClass, klass);
            if (hierarchy)
            {
                var kd = Read(first, Offset(objectClass, spec.Layout.Field("Il2CppClass", "typeHierarchyDepth").ByteOffset), 8);
                var pd = mode == "DepthConstant" ? t.Constant(2, 8) : Read(first, Offset(klass, spec.Layout.Field("Il2CppClass", "typeHierarchyDepth").ByteOffset), 8);
                var table = Read(last, Offset(objectClass, spec.Layout.Field("Il2CppClass", "typeHierarchy").ByteOffset));
                var scaled = Op(CoreOperation.ShiftLeft, 64, Op(CoreOperation.ZeroExtend, 64, oldDepth ?? pd), t.Constant(3, 64));
                var element = Read(last, Op(CoreOperation.Subtract, 64, Op(CoreOperation.Add, 64, table, scaled), t.Constant(8, 64)));
                compare = Op(CoreOperation.Equal, 1, element, klass);
                if (mode == "ExtraEvent") first.Add(new Call(new(), new ComputedTarget(obj), [], []));
                builder.Blocks.Add(new(check, [], first.ToImmutableArray(), new Branch(Op(CoreOperation.UnsignedLess, 1, kd, pd), mode == "Split" ? different : failed, mode == "HierIntervening" ? middle : elementBlock)));
                if (mode == "HierIntervening") builder.Blocks.Add(new(middle, [], [], new Jump(elementBlock)));
            }
            builder.Blocks.Add(new(entry, [], prefix.ToImmutableArray(), mode == "NoNull" ? new Jump(check)
                : new Branch(Op(CoreOperation.Equal, 1, obj, t.Constant(0, 64)), cast || materialized ? success : failed, check)));
            if (materialized)
            {
                var selected = Op(CoreOperation.Select, 64, compare, obj, t.Constant(0, 64));
                builder.Blocks.Add(new(elementBlock, [], last.ToImmutableArray(), new Jump(success)));
                var mergeId = new MergeIdentity(); var result = t.Atom(new ResultAtom(mergeId), 64);
                builder.Blocks.Add(new(success, [new(mergeId, result, hierarchy
                    ? [new(entry, t.Constant(0, 64)), new(failed, t.Constant(0, 64)), new(elementBlock, selected)]
                    : [new(entry, t.Constant(0, 64)), new(elementBlock, selected)])], [], new Return([new(slot, result)])));
                if (mode == "HierMaterializedOther")
                {
                    var flagId = new MergeIdentity(); var flag = t.Atom(new ResultAtom(flagId), 32);
                    var block = builder.Blocks[^1];
                    builder.Blocks[^1] = block with { Merges = block.Merges.Add(new(flagId, flag,
                        [new(entry, t.Constant(0, 32)), new(failed, t.Constant(1, 32)), new(elementBlock, t.Constant(2, 32))])),
                        End = new Return([new(slot, Op(CoreOperation.Select, 64, Op(CoreOperation.Equal, 1, flag, t.Constant(1, 32)), result, t.Constant(0, 64)))]) };
                }
                if (hierarchy) builder.Blocks.Add(new(failed, [], [], new Jump(success)));
            }
            else
            {
                builder.Blocks.Add(new(elementBlock, [], last.ToImmutableArray(), mode.Contains("Predicate", StringComparison.Ordinal)
                    ? new Return([new(slot, t.Concat(compare, t.Constant(0, 63)))]) : mode == "SelectedBranch" ? new Branch(Op(CoreOperation.Equal, 1,
                    Op(CoreOperation.Select, 64, compare, obj, t.Constant(0, 64)), t.Constant(0, 64)), failed, success) : new Branch(compare, success, failed)));
                if (!mode.Contains("Predicate", StringComparison.Ordinal)) builder.Blocks.Add(new(success, [], [], new Return([new(slot, obj)])));
                builder.Blocks.Add(new(failed, [], cast
                    ? [new Call(new(), new ImageFunction(20), [new(slot, mode == "WrongThrow" ? t.Constant(0, 64) : obj), new(new(SlotKind.Integer, 1), klass)], [], true, mode == "Unwind" ? handler : null)] : [],
                    cast ? new Unreachable() : new Return([new(slot, t.Constant(0, 64))])));
            }
            if (mode == "Split") builder.Blocks.Add(new(different, [], [], new Return([new(slot, t.Constant(0, 64))])));
            if (mode == "ForeignFailureRead")
            {
                var otherSlot = new AbstractSlot(SlotKind.Integer, 1); var other = t.Atom(new EntryAtom(otherSlot), 64);
                builder.Inputs.Add(new(otherSlot, other));
                var statements = new List<Statement>(); Read(statements, Offset(other, spec.Layout.Field("Il2CppObject", "klass").ByteOffset));
                var failureIndex = builder.Blocks.FindIndex(b => b.Identity == failed);
                builder.Blocks[failureIndex] = builder.Blocks[failureIndex] with { Statements = statements.Concat(builder.Blocks[failureIndex].Statements).ToImmutableArray() };
            }
            if (mode == "Unwind")
            {
                var exception = t.Atom(new ExceptionAtom(handler), 64); var selector = t.Atom(new SelectorAtom(handler), 64);
                var mergeId = new MergeIdentity(); var saved = t.Atom(new ResultAtom(mergeId), 64);
                builder.Blocks.Add(new(handler, [new(mergeId, saved, [new(failed, obj)])],
                    [new Call(new(), new ComputedTarget(obj), [new(slot, saved)], [])], new ResumeUnwind(exception), new(exception, selector, [new(ClauseKind.Cleanup, [])])));
            }
            if (mode == "CastAlternatives")
            {
                var rightSlot = new AbstractSlot(SlotKind.Integer, 1); var choiceSlot = new AbstractSlot(SlotKind.Integer, 2);
                var right = t.Atom(new EntryAtom(rightSlot), 64); var choice = t.Atom(new EntryAtom(choiceSlot), 64);
                builder.Inputs.Add(new(rightSlot, right)); builder.Inputs.Add(new(choiceSlot, choice));
                var arms = new[] { new BlockIdentity(), new BlockIdentity() };
                var inputs = ImmutableArray.CreateBuilder<Incoming>();
                builder.Blocks.Clear();
                builder.Blocks.Add(new(entry, [], prefix.ToImmutableArray(), new Branch(t.Slice(choice, 0, 1), arms[0], arms[1])));
                for (int arm = 0; arm < 2; arm++)
                {
                    var value = arm == 0 ? obj : right; var checkedBlock = new BlockIdentity(); var throwBlock = new BlockIdentity();
                    builder.Blocks.Add(new(arms[arm], [], [], new Branch(Op(CoreOperation.Equal, 1, value, t.Constant(0, 64)), success, checkedBlock)));
                    var statements = new List<Statement>(); var actual = Read(statements, Offset(value, spec.Layout.Field("Il2CppObject", "klass").ByteOffset));
                    var continuation = new BlockIdentity();
                    builder.Blocks.Add(new(checkedBlock, [], statements.ToImmutableArray(), new Branch(Op(CoreOperation.Equal, 1, actual, klass), continuation, throwBlock)));
                    builder.Blocks.Add(new(continuation, [], [], new Jump(success)));
                    builder.Blocks.Add(new(throwBlock, [], [new Call(new(), new ImageFunction(20), [new(slot, value), new(new(SlotKind.Integer, 1), klass)], [], true)], new Unreachable()));
                    inputs.Add(new(arms[arm], value)); inputs.Add(new(continuation, value));
                }
                var mergeId = new MergeIdentity(); var chosen = t.Atom(new ResultAtom(mergeId), 64);
                builder.Blocks.Add(new(success, [new(mergeId, chosen, inputs.ToImmutable())], [], new Return([new(slot, chosen)])));
            }
            TypeRef target = mode == "ExactBoxed" ? Primitive("Int32") : mode == "Array" ? new ArrayRef(finalType, 1) : mode == "Interface" ? new DefinitionRef(iface, []) : mode == "NonSealed" ? parentType : hierarchy ? parentType : finalType;
            var facts = NamingFacts.Empty with { Slots = NamingFacts.Empty.Slots.Add(128, Outcome<MetadataEntity>.Success(new ClassEntity(target))) };
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(throwFunction), catalog);
            var state = new StateQueries(); var names = new ValueNamingQuery(state, calls, facts, spec, binder, binder.Entry(MethodRef.Open(method), BindingEntryKind.Ordinary).Value);
            var function = builder.Freeze();
            checks.True(ExitChecker.Check(function).IsValid, mode + " 内联模板输入契约");
            var transformed = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }).Run(function);
            checks.True(ExitChecker.Check(transformed.Function).IsValid, mode + " 折叠后原生契约");
            bool accepted = cases.Take(13).Contains(mode) || mode == "Unwind";
            var operations = transformed.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Target is NamedFunction).ToArray();
            checks.True(operations.Length == (accepted ? mode == "CastAlternatives" ? 2 : 1 : 0), mode + " 折叠数量：" + string.Join(';', transformed.Records.Where(r => r.Why is not null).Select(r => r.Why)));
            if (!accepted)
            {
                var code = mode == "DepthConstant" ? "depth" : mode is "Array" or "NonSealed" ? "exact" : mode == "NoNull" ? "null" : "shape";
                checks.True(transformed.Records.Any(r => r.Why?.Code == "structure.type-check." + code), mode + " 保留明确原因"); continue;
            }
            if (mode == "Unwind")
            {
                checks.True(operations.SingleOrDefault()?.Unwind == handler, "转换失败调用的展开边迁移到 CastClass");
                checks.True(transformed.Function.Blocks.Single(b => b.Identity == handler).Statements.OfType<Call>()
                    .Single().Arguments.Single().Value == obj, "展开合流沿用检查前的对象及新的前驱身份");
                continue;
            }
            if (mode == "HierRepeatedDepth") continue;
            var namedContext = names.CreateContext(transformed.Function);
            var returned = operations[0].Results.Single().Value;
            checks.True(namedContext.Get(names, returned).Value.StaticType == (mode == "ExactBoxed" ? null : target), mode + " 登记的引用结果类型进入共享查询");
            if (cast) checks.True(names.SameValue(namedContext, returned, operations[0].Arguments[0].Value).Value, mode + " 类型细化仍保留原对象的值身份");
            var lowered = new IntegerLowering(transformed.Function, MethodRef.Open(method), binder, types, calls: calls,
                effects: new ManagedCallEffects(calls), spec: spec, names: facts).Run();
            checks.True(lowered.Body is not null, mode + " 类型槽只被运行时操作消费即可下降：" + lowered.Failure);
            if (lowered.Body is not { } body) continue;
            checks.True(emitter.Emit([body]).Count == 0, mode + " CIL 写出契约");
            var executable = source.Method("TypeCases", mode); executable.Body = skeleton.Method(method).Body;
            foreach (var local in executable.Body.Variables) local.VariableType = local.VariableType.FullName switch
            { "Parent" => source.Module.GetType("Parent"), "Final" => source.Module.GetType("Final"), "System.Object" => source.Module.TypeSystem.Object, _ => local.VariableType };
            foreach (var instruction in executable.Body.Instructions)
                if (instruction.Operand is Mono.Cecil.TypeReference tr)
                    instruction.Operand = tr.FullName switch { "Parent" or "Final" => source.Module.GetType(tr.FullName), "System.Int32" => source.Module.TypeSystem.Int32, _ => tr };
            var model = new CecilModel(source.Module); var executionTypes = new ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8);
            var index = new WorldIndex(model.Program, executionTypes); var interpreter = new CilInterpreter(model, index) { BodyModule = source.Module };
            var tested = model.Method(executable);
            var nullRun = interpreter.Run(new World(index, 0, new Hints([], []), tested.DeclaringType), executable, tested, mode == "CastAlternatives" ? [StackValue.O(0), StackValue.O(0), StackValue.I4(0)] : [StackValue.O(0)]);
            checks.True(nullRun.Result == "return 0x0", mode + " 执行空对象直接返回空：" + nullRun.Result);
            foreach (var valid in mode == "ExactBoxed" ? new[] { false } : new[] { false, true })
            {
                var world = new World(index, 0, new Hints([], []), tested.DeclaringType);
                var valueType = model.Program.Types.Single(d => d.Name == (valid ? "Final" : "Other"));
                var address = world.Instance(new DefinitionRef(valueType, []), "object", 0);
                var right = mode == "CastAlternatives" ? world.Instance(new DefinitionRef(valueType, []), "right", 0) : 0;
                foreach (var left in mode == "CastAlternatives" ? new[] { true, false } : new[] { true })
                {
                    var run = interpreter.Run(world, executable, tested, mode == "CastAlternatives"
                        ? [StackValue.O(address), StackValue.O(right), StackValue.I4(left ? 1 : 0)] : [StackValue.O(address)]);
                    var selected = left ? address : right;
                    checks.True(valid ? run.Result == (mode.Contains("Predicate", StringComparison.Ordinal) ? "return 0x1" : $"return 0x{selected:x}") : cast ? run.Events.Any(e => e.Text.StartsWith("throw System.InvalidCastException ", StringComparison.Ordinal)) : run.Result == "return 0x0",
                        mode + (valid ? " 执行匹配对象" : " 执行不匹配对象") + "：" + run.Result);
                }
            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
