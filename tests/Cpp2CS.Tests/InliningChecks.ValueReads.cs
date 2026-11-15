using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Tests.Execution;
using Mono.Cecil.Cil;
using ManagedValues = Cpp2CS.Managed.ManagedValues;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    private static void ValueAccessorChecks(Assertions checks)
    {
        foreach (string mode in new[] { "Parameter", "CallResult", "Nested", "Readonly", "Generic", "Ambiguous", "Inaccessible", "Event", "Conditional", "NoGetter", "SplitReads" })
        {
            bool generic = mode == "Generic";
            var f = new Fixture(valueOwner: true, generic: generic, fieldOffset: 0);
            f.Owner.Size = 4;
            var instance = generic ? new DefinitionRef(f.Owner, [f.Integer]) : f.OwnerType;
            var getter = f.Method(f.Owner, "Fetch", false, false, accessible: mode != "Inaccessible");
            var create = f.Method(f.Caller, "Create", false, true); create.ReturnType = instance;
            var callerType = new DefinitionRef(f.Caller, []);
            var nested = new FieldDef { Index = 2, Owner = f.Caller, Name = "Nested", Type = instance,
                Attributes = FieldAttributes.Public | (mode == "Readonly" ? FieldAttributes.InitOnly : 0), Offset = 16, Token = 0x04000003 };
            f.Caller.Fields = [nested]; ((List<FieldDef>)f.Program.Fields).Add(nested);
            bool nesting = mode is "Nested" or "Readonly" or "SplitReads";
            var caller = f.Method(f.Caller, "Use", false, true, mode == "CallResult" ? [] : [nesting ? callerType : instance]);
            var self = new ArgumentValue(-1, new ByRefRef(f.OwnerType), 64);
            var field = new FieldValue(self, f.Field, f.Integer, 32);
            ManagedBody GetterBody(MethodDef m) => new(MethodRef.Open(m), [new(0, [new ManagedReturn(0, field)])]);
            var bodies = new Dictionary<MethodDef, ManagedBody> { [getter] = GetterBody(getter) };
            if (mode == "Event") bodies[getter] = new(MethodRef.Open(getter), [new(0, [
                new ManagedCall(0, new(MethodRef.Open(create), null, [], false), null), new ManagedReturn(1, field)])]);
            if (mode == "Conditional") bodies[getter] = new(MethodRef.Open(getter), [new(0, [new ManagedReturn(0,
                new ChoiceValue(new ComparisonValue(ComparisonKind.Equal, field, new ConstantValue(0, f.Integer, 32), f.Types.Boolean),
                    new ConstantValue(7, f.Integer, 32), field, f.Integer, 32))])]);
            if (mode == "Ambiguous")
            {
                var another = f.Method(f.Owner, "Another", false, false); bodies[another] = GetterBody(another);
            }
            if (mode == "NoGetter") f.Owner.Methods = [];
            var terms = new TermTable(); var entry = new BlockIdentity();
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var statements = new List<Statement>();
            var input = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            Term result = input;
            if (mode == "CallResult")
            {
                var id = new CallIdentity(); result = terms.Atom(new ResultAtom(id), 64);
                statements.Add(new Call(id, new ImageFunction(10), [new(new(SlotKind.Integer), terms.Constant(0, 64))], [new(new(SlotKind.Integer), result)]));
            }
            else builder.Inputs.Add(new(new(SlotKind.Integer), input));
            if (nesting)
            {
                var id = new ReadIdentity(); result = terms.Atom(new ResultAtom(id), 32);
                statements.Add(new MemoryRead(id, terms.Apply(new CoreOperator(CoreOperation.Add), 64, input, terms.Constant(16, 64)), 32, result));
            }
            result = result.Width == 32 ? result : terms.Slice(result, 0, 32);
            if (mode == "SplitReads")
            {
                var yes = new BlockIdentity(); var no = new BlockIdentity();
                var condition = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64); builder.Inputs.Add(new(new(SlotKind.Integer, 1), condition));
                caller.Parameters = [.. caller.Parameters, new("condition", f.Integer, 0, null, false)];
                builder.Blocks.Add(new(entry, [], [], new Branch(terms.Apply(new CoreOperator(CoreOperation.Equal), 1, terms.Slice(condition, 0, 32), terms.Constant(0, 32)), yes, no)));
                var first = (MemoryRead)statements.Single(); var secondId = new ReadIdentity();
                var second = new MemoryRead(secondId, first.Address, 32, terms.Atom(new ResultAtom(secondId), 32));
                builder.Blocks.Add(new(yes, [], [first], new Return([new(new(SlotKind.Integer), terms.Concat(first.Result, terms.Constant(0, 32)))])));
                builder.Blocks.Add(new(no, [], [second], new Return([new(new(SlotKind.Integer), terms.Concat(second.Result, terms.Constant(0, 32)))])));
            }
            else builder.Blocks.Add(new(entry, [], [.. statements], new Return([new(new(SlotKind.Integer), terms.Concat(result, terms.Constant(0, 32)))])));
            var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
            var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(create), BindingEntryKind.Ordinary)]), new NamingChecks.RuntimeMap(), catalog);
            var attempts = new List<AccessorAttempt>();
            var accessors = new AccessorQuery(f.Types, new CachedAccessorTemplates(bodies.GetValueOrDefault), attempts.Add);
            var lowered = new IntegerLowering(builder.Freeze(), MethodRef.Open(caller), f.Binder, f.Types, calls: calls, spec: f.Spec, accessors: accessors).Run();
            bool positive = mode is "Parameter" or "CallResult" or "Nested" or "Readonly" or "Generic";
            if (mode == "SplitReads")
            {
                checks.True(lowered.Body is null && lowered.Failure?.Reason.Code == "lowering.Access.ReadPlacement", "纯 getter 不绕过读取局部的支配要求：" + lowered.Failure);
                continue;
            }
            if (!positive)
            {
                checks.True(lowered.Body is null && attempts.Any(a => a.Answer.Failure is not null), "纯值读取反例保留查询原因：" + mode + " " + lowered.Failure);
                if (mode == "Ambiguous") checks.True(attempts.Any(a => a.Answer.Failure?.Code == "inline.Accessor.Ambiguous"), "纯值读取保持模板歧义");
                continue;
            }
            checks.True(lowered.Body is not null, "纯值读取下降：" + mode + " " + lowered.Failure);
            if (lowered.Body is not { } complete) continue;
            var recovered = complete.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
                .OfType<FieldValue>().Where(v => v.Accessor is not null).ToArray();
            checks.True(recovered.Length == 1 && recovered[0].Accessor!.Method.Method == getter
                && recovered[0].Accessor!.Method.DeclaringType.Equals(instance), "纯值读取采用接收者类型的唯一 getter：" + mode);
            using var skeleton = new SkeletonScope(f.Program);
            var emitter = new BodyEmitter(skeleton.Value, f.Types);
            var problems = emitter.Emit([.. bodies.Values, complete]);
            checks.True(problems.Count == 0, "纯值 getter 通过输出校验：" + mode + " " + string.Join("；", problems.Values));
            if (problems.Count != 0 || generic) continue;
            var emitted = skeleton.Value.Method(caller);
            if (mode == "Readonly") checks.True(emitted.Body.Instructions.Any(i => i.OpCode == OpCodes.Stloc), "只读字段值先复制到临时局部再调用 getter");
            checks.True(emitted.Body.Instructions.Any(i => i.OpCode == OpCodes.Call && i.Operand is Mono.Cecil.MethodReference m && m.Name == "Fetch"), "输出包含 getter call：" + mode);
            const string source = """
                public struct Owner { private int Value; public int Fetch() => Value; }
                public class Caller {
                    public Owner Nested;
                    public static Owner Create() => default;
                    public static int Parameter(Owner x) => x.Fetch();
                    public static int CallResult() => Create().Fetch();
                    public static int NestedRead(Caller x) => x.Nested.Fetch();
                }
                """;
            using var reference = new CompiledSource(source);
            using var tested = new CompiledSource(source);
            var selected = nesting ? "NestedRead" : mode;
            var actual = tested.Method("Caller", selected);
            actual.Body = emitted.Body;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => type is Mono.Cecil.ByReferenceType byref
                ? new Mono.Cecil.ByReferenceType(MapType(byref.ElementType))
                : tested.Module.GetType(type.FullName) ?? tested.Module.ImportReference(System.Type.GetType(type.FullName, throwOnError: true)!);
            foreach (var instruction in actual.Body.Instructions)
                if (instruction.Operand is Mono.Cecil.FieldReference member)
                    instruction.Operand = tested.Module.GetType(member.DeclaringType.FullName).Fields.Single(v => v.Name == member.Name);
                else if (instruction.Operand is Mono.Cecil.MethodReference called)
                    instruction.Operand = tested.Module.GetType(called.DeclaringType.FullName).Methods.Single(v => v.Name == called.Name);
                else if (instruction.Operand is Mono.Cecil.TypeReference type) instruction.Operand = MapType(type);
                else if (instruction.Operand is Mono.Cecil.ParameterDefinition parameter) instruction.Operand = actual.Parameters[parameter.Index];
            foreach (var variable in actual.Body.Variables) variable.VariableType = MapType(variable.VariableType);
            var comparison = CilComparison.Compare(reference.Method("Caller", selected), actual);
            checks.True(comparison.Status == CilComparisonStatus.Match, "纯值读取执行对照：" + mode + " " + comparison);
        }
    }

    private sealed class SkeletonScope(ProgramModel program) : IDisposable
    {
        public Skeleton Value { get; } = new(program, 16);
        public void Dispose() { foreach (var assembly in Value.Assemblies) assembly.Dispose(); }
    }
}
