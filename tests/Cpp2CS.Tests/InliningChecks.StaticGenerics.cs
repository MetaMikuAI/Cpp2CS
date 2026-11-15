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
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    private sealed class StaticInitializationMap(RuntimeFunction initialization) : IRuntimeFunctionMap
    {
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 20 } ? initialization : null;
    }

    private static void GenericStaticAccessorChecks(Assertions checks)
    {
        foreach (string mode in new[] { "Closed", "Method", "ArrayArgument", "Declaring", "Both", "Open", "Ambiguous", "Conflict", "Mismatch", "Inaccessible", "Unbound", "Invalid", "ForeignInitializer", "Initialization", "Barrier" })
        {
            var f = new Fixture(generic: mode is "Declaring" or "Both", externalCaller: true);
            GenericParameterDef Parameter(string name, int index = 0) => new() { Name = name, Position = index, Attributes = 0 };
            var hidden = new TypeDef { Index = f.Program.Types.Count, Assembly = f.Owner.Assembly, Namespace = "", Name = "Cache`1",
                Token = (uint)(0x02000001 + f.Program.Types.Count), Attributes = TypeAttributes.NotPublic, IsValueType = false, IsEnum = false,
                BaseType = f.Types.Object, Size = 16, PackingSize = 0, ClassSizeIsDefault = true,
                GenericParameters = mode is "Both" or "Conflict" ? [Parameter("A"), Parameter("B", 1)] : [Parameter("A")] };
            ((List<TypeDef>)f.Program.Types).Add(hidden);
            var assembly = f.Program.Assemblies.Single(a => a.Name == hidden.Assembly); assembly.Types = [.. assembly.Types, hidden];
            var field = new FieldDef { Index = f.Program.Fields.Count, Owner = hidden, Name = "Value",
                Type = new ArrayRef(new GenericParameterRef("A", false, 0) { Parameter = hidden.GenericParameters[0] }, 1),
                Attributes = FieldAttributes.Assembly | FieldAttributes.Static, Offset = 0, Token = (uint)(0x04000001 + f.Program.Fields.Count) };
            hidden.Fields = [field]; ((List<FieldDef>)f.Program.Fields).Add(field);
            var getter = f.Method(f.Owner, "Fetch", false, true, accessible: mode != "Inaccessible");
            if (mode is not ("Closed" or "Declaring")) getter.GenericParameters = mode == "Unbound" ? [Parameter("M"), Parameter("N", 1)] : [Parameter("M")];
            var open = MethodRef.Open(getter);
            var patternArguments = mode == "Both" ? open.TypeArguments.Concat(open.MethodArguments).ToArray()
                : mode == "Declaring" ? open.TypeArguments.ToArray() : open.MethodArguments.Take(1).ToArray();
            if (mode == "Closed") patternArguments = [f.Integer];
            if (mode == "Conflict") patternArguments = [patternArguments[0], patternArguments[0]];
            if (mode == "Mismatch") patternArguments = [new ArrayRef(patternArguments[0], 1)];
            var pattern = new FieldRef(field, new DefinitionRef(hidden, patternArguments));
            getter.ReturnType = field.Type.Substitute(patternArguments, []);
            ManagedBody Body(MethodDef method) => new(MethodRef.Open(method), [new(0, [new ManagedReturn(0,
                new StaticFieldValue(pattern, getter.ReturnType, 64))])]);
            var bodies = new Dictionary<MethodDef, ManagedBody> { [getter] = Body(getter) };
            if (mode == "Ambiguous")
            {
                var other = f.Method(f.Owner, "Other", false, true); other.GenericParameters = getter.GenericParameters;
                other.ReturnType = getter.ReturnType; bodies.Add(other, Body(other));
            }
            // 候选所在的类另有静态构造函数：调用它会多触发一次现场没有的初始化。
            if (mode == "ForeignInitializer") f.Method(f.Owner, ".cctor", true, true, []);
            var caller = f.Method(f.Caller, "Use", false, true);
            if (mode == "Open") caller.GenericParameters = [Parameter("U")];
            TypeRef argument = mode == "Open" ? MethodRef.Open(caller).MethodArguments[0]
                : mode == "Invalid" ? new PointerRef(f.Integer) : mode == "ArrayArgument" ? new ArrayRef(f.Integer, 1) : f.Integer;
            var actualArguments = mode is "Both" or "Conflict" ? new[] { argument, f.Types.String } : new[] { argument };
            var actual = new FieldRef(field, new DefinitionRef(hidden, actualArguments));
            caller.ReturnType = field.Type.Substitute(actualArguments, []);
            var query = new AccessorQuery(f.Types, new CachedAccessorTemplates(bodies.GetValueOrDefault));
            var answer = query.Resolve(new(MethodRef.Open(caller), 0, actual, null, AccessorKind.Getter, true));
            bool rejected = mode is "Ambiguous" or "Conflict" or "Mismatch" or "Inaccessible" or "Unbound" or "Invalid" or "ForeignInitializer";
            checks.True((answer.Method is null) == rejected, "静态字段类型合一：" + mode + " " + answer.Failure);
            if (rejected)
            {
                checks.True(answer.Failure?.Cause is not null, "失败保留锚点与推导原因：" + mode);
                if (mode == "Ambiguous") checks.True(answer is { Matches: 2, Failure.Code: "inline.Accessor.Ambiguous" }, "两个封闭实例保持歧义");
                if (mode is "Conflict" or "Mismatch" or "Unbound" or "Invalid") checks.True(answer.Failure?.Cause?.Code == "inline.Accessor.TypeArguments", "合一失败说明泛型实参缺口：" + mode);
                continue;
            }
            checks.True(answer.Method!.TypeArguments.SequenceEqual(mode is "Declaring" or "Both" ? [argument] : [])
                && answer.Method.MethodArguments.SequenceEqual(mode is "Closed" or "Declaring" ? [] : mode == "Both" ? [f.Types.String] : [argument]), "类与方法的泛型槽位独立绑定：" + mode);
            var (native, names) = f.Function(actual, false, width: 64);
            var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
            var runtime = catalog.Functions.First(r => r.Operation.Name == "InitializeClassPrecise" && r.Signature is not null);
            var touch = f.Method(f.Caller, "Touch", true, true, []);
            var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(touch), BindingEntryKind.Ordinary)]),
                new StaticInitializationMap(runtime), catalog);
            ManagedTypes types = mode == "Open" ? new(f.Program, new GenericWitness(MethodRef.Open(caller), new(caller, [], [f.Types.Object]), f.Types.Layouts), 8) : f.Types;
            if (mode is "Initialization" or "Barrier")
            {
                f.Method(hidden, ".cctor", true, true, []);
                var block = native.Blocks[0]; var statements = block.Statements.ToList();
                var klass = ((MemoryRead)statements[0]).Result;
                var init = new Call(new(), new ImageFunction(20), [new(new(SlotKind.Integer), klass)], []);
                statements.Insert(1, init);
                if (mode == "Barrier") statements.Insert(2, new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), native.Terms.Constant(0, 64))], []));
                var builder = new FunctionBuilder(native.Terms, native.Entry, 64, native.Frame) { ImageBase = native.ImageBase };
                builder.Inputs.AddRange(native.Inputs); builder.Blocks.Add(block with { Statements = statements.ToImmutableArray() }); native = builder.Freeze();
                var state = new StateQueries(new ManagedCallEffects(calls));
                var values = new ValueNamingQuery(state, calls, names, f.Spec, f.Binder);
                var locations = new ManagedLocationQuery(state, values, types.Layouts, f.Spec);
                var initialization = new ClassInitializationQuery(state, calls, values, locations, f.Spec);
                var proof = locations.CreateContext(native).Get(initialization, init.Identity);
                checks.True(proof.IsSuccess && proof.Value.CanAbsorb == (mode != "Barrier"), "沿用类初始化吸收查询：" + mode + " " + proof.Why);
                native = new UnobservableEffects(state, calls, values, new InputMemoryImage(), new HashSet<AbstractSlot>(), locations, initialization).Run(native).Function;
                checks.True(native.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(c => c.Identity == init.Identity) == (mode == "Barrier"), "其他事件阻止初始化被读取吸收：" + mode);
                if (mode == "Barrier") continue;
            }
            if (mode == "Open")
                checks.True(new IntegerLowering(native, MethodRef.Open(caller), f.Binder, f.Types, calls: calls,
                    spec: f.Spec, names: names, accessors: query).Run().Failure?.Reason.Code == "lowering.Generic.Witness",
                    "共享泛型现场没有见证时保留明确原因");
            var result = new IntegerLowering(native, MethodRef.Open(caller), f.Binder, types, calls: calls,
                effects: new ManagedCallEffects(calls), spec: f.Spec, names: names, accessors: query,
                witness: mode == "Open" ? new(caller, [], [f.Types.Object]) : null).Run(mode == "Open" ? BindingEntryKind.SharedGeneric : BindingEntryKind.Ordinary);
            checks.True(result.Body is not null, "泛型静态访问器下降：" + mode + " " + result.Failure);
            if (result.Body is not { } body) continue;
            var selected = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Single();
            checks.True(selected.Invocation.Method.Equals(answer.Method) && !selected.Invocation.Virtual && selected.Invocation.Receiver is null,
                "现场换成合一所得普通静态调用：" + mode);
            using var emission = new EmissionFixture(f);
            checks.True(emission.Emitter.Emit([body]).Count == 0, "泛型静态调用通过 IL 写出校验：" + mode);
            if (mode is "Method" or "Initialization") GenericStaticAccessorExecution(checks, f, caller, body);
        }
    }

    private static void GenericStaticAccessorExecution(Assertions checks, Fixture fixture, MethodDef caller, ManagedBody body)
    {
        using var source = new CompiledSource("""
            internal static class Cache<T> {
                internal static readonly T[] Value;
                static Cache() { Value = new T[0]; }
            }
            public static class Owner { public static T[] Fetch<T>() => Cache<T>.Value; }
            public static class Caller { public static int[] Reference() => Owner.Fetch<int>(); public static int[] Output() => null; }
            """);
        var skeleton = new Skeleton(fixture.Program, 16);
        var problems = new BodyEmitter(skeleton, fixture.Types).Emit([body]);
        checks.True(problems.Count == 0, "执行对照体通过写出契约");
        var candidate = source.Method("Caller", "Output"); candidate.Body = skeleton.Method(caller).Body;
        foreach (var instruction in candidate.Body.Instructions)
            if (instruction.Operand is Mono.Cecil.MethodReference)
            {
                var target = new Mono.Cecil.GenericInstanceMethod(source.Method("Owner", "Fetch"));
                target.GenericArguments.Add(source.Module.TypeSystem.Int32); instruction.Operand = target;
            }
        foreach (var local in candidate.Body.Variables) local.VariableType = new Mono.Cecil.ArrayType(source.Module.TypeSystem.Int32);
        var compared = CilComparison.Compare(source.Method("Caller", "Reference"), candidate);
        checks.True(compared is { Status: CilComparisonStatus.Match, CompletedCases: 32 }, "实际恢复的泛型静态访问器执行对照：" + compared.Reason);
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
