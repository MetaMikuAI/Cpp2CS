using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Exceptions;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class ClassInitializationChecks
{
    private static void ExceptionRegions(Assertions checks, RuntimeSpec spec, FieldLayouts layouts, MethodBinder binder,
        RuntimeFunctionCatalog catalog, RuntimeFunction runtime, TypeDef owner, TypeRef nothing, NamingFacts facts)
    {
        var objectType = new DefinitionRef(new TypeDef { Index = 10, Assembly = "mscorlib.dll", Namespace = "System", Name = "Object", Token = 0,
            Attributes = System.Reflection.TypeAttributes.Public, IsValueType = false, IsEnum = false }, []);
        var use = new MethodDef { Index = 8, Owner = owner, Name = "Use", Token = 0, Attributes = System.Reflection.MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1, ReturnType = nothing, Parameters = [] };
        foreach (var mode in new[] { "CallSame", "CallOutside", "CallOther", "ReadSame", "WriteSame", "ReadOutside", "ReadOther", "ReadOnly", "ReadTransparent", "CallTransparent", "ReadCatchPrefix", "ReadPrelude" })
        {
            var calls = new CallNamingQuery(binder, new NamingChecks.Map([new(MethodRef.Open(use), BindingEntryKind.Ordinary)]),
                new RuntimeMap(runtime, catalog.Functions.First(f => f.Operation.Name == "AllocateObject" && f.Signature is not null),
                    catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is not null)), catalog);
            var t = new TermTable(); var entry = new BlockIdentity(); var access = new BlockIdentity(); var h1 = new BlockIdentity(); var h2 = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var slot = new AbstractSlot(SlotKind.Integer); var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
            var before = new List<Statement>();
            Term Read(List<Statement> statements, Term address, int width)
            { var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), width); statements.Add(new MemoryRead(id, address, width, value)); return value; }
            Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(unchecked((ulong)offset), 64));
            var klass = Read(before, Add(image, 256), 64);
            var init = new Call(new(), new ImageFunction(20), [new(slot, klass)], [], Unwind: mode == "ReadPrelude" ? null : h1); before.Add(init);
            BlockIdentity? target = (mode.EndsWith("Outside", StringComparison.Ordinal) || mode.EndsWith("Transparent", StringComparison.Ordinal)) ? null : mode.EndsWith("Other", StringComparison.Ordinal) ? h2 : h1;
            var statements = new List<Statement>();
            Term? value = null;
            if (!mode.StartsWith("Call", StringComparison.Ordinal))
            {
                var fields = Read(statements, Add(klass, spec.Layout.Field("Il2CppClass", "static_fields").ByteOffset), 64);
                if (mode == "WriteSame") statements.Add(new MemoryWrite(new(), fields, 32, t.Constant(5, 32)));
                else value = Read(statements, fields, 32);
            }
            if (mode != "ReadOnly") statements.Add(new Call(new(), new ImageFunction(10), [new(slot, t.Constant(0, 64))], [], Unwind: target));
            if (mode.EndsWith("Same", StringComparison.Ordinal) || mode == "ReadOnly" || mode.EndsWith("Transparent", StringComparison.Ordinal) || mode == "ReadPrelude")
                f.Blocks.Add(new(entry, [], [.. before, .. statements], new Return(value is null ? [] : [new(slot, value)])));
            else
            {
                f.Blocks.Add(new(entry, [], [.. before], new Jump(access)));
                f.Blocks.Add(new(access, [], [.. statements], new Return(value is null ? [] : [new(slot, value)])));
            }
            foreach (var handler in target == h2 ? new[] { h1, h2 } : new[] { h1 })
            {
                var exception = t.Atom(new ExceptionAtom(handler), 64); var beginId = new CallIdentity(); var payload = t.Atom(new ResultAtom(beginId), 64);
                if (mode.EndsWith("Transparent", StringComparison.Ordinal))
                {
                    f.Blocks.Add(new(handler, [], [], new ResumeUnwind(exception), new(exception,
                        t.Atom(new SelectorAtom(handler), 64), [new(ClauseKind.Cleanup, [])])));
                    continue;
                }
                var capture = new BlockIdentity();
                f.Blocks.Add(new(handler, [], [], new Jump(capture),
                    new(exception, t.Atom(new SelectorAtom(handler), 64), [new(ClauseKind.CatchAll, [])])));
                f.Blocks.Add(new(capture, [], [new Call(beginId, new ImportedTarget(new("__cxa_begin_catch")), [new(slot, exception)], [new(slot, payload)]),
                    new Call(new(), new ImportedTarget(new("__cxa_end_catch")), [], [])], new Return([])));
            }
            if (mode == "ReadCatchPrefix")
            {
                // 初始化在 catch 前缀中；删除之后，现有异常计划会把只剩读取的前缀略去。
                f.Blocks.Clear();
                var capture = new BlockIdentity(); var body = new BlockIdentity();
                init = init with { Unwind = h2 };
                f.Blocks.Add(new(entry, [], [before[0], new Call(new(), new ImageFunction(10), [new(slot, t.Constant(0, 64))], [], Unwind: h1)], new Return([])));
                var exception = t.Atom(new ExceptionAtom(h1), 64); var begin = new CallIdentity(); var payload = t.Atom(new ResultAtom(begin), 64);
                f.Blocks.Add(new(h1, [], [], new Jump(capture), new(exception, t.Atom(new SelectorAtom(h1), 64), [new(ClauseKind.CatchAll, [])])));
                f.Blocks.Add(new(capture, [], [new Call(begin, new ImportedTarget(new("__cxa_begin_catch")), [new(slot, exception)], [new(slot, payload)]),
                    init, .. statements.Where(s => s is not Call), new Call(new(), new ImportedTarget(new("__cxa_end_catch")), [], [])], new Jump(body)));
                f.Blocks.Add(new(body, [], [new Call(new(), new ImageFunction(10), [new(slot, t.Constant(0, 64))], [])], new Return([new(slot, value!)])));
                var cleanupException = t.Atom(new ExceptionAtom(h2), 64);
                f.Blocks.Add(new(h2, [], [], new ResumeUnwind(cleanupException),
                    new(cleanupException, t.Atom(new SelectorAtom(h2), 64), [new(ClauseKind.Cleanup, [])])));
            }
            var function = f.Freeze();
            if (mode == "ReadPrelude") function = ExceptionScaffolding.Project(function, calls, splitEntries: true);
            var state = new StateQueries(); var names = new ValueNamingQuery(state, calls, facts, spec, binder);
            var locations = new ManagedLocationQuery(state, names, layouts, spec);
            var regions = new ExceptionRegionQuery(state, calls, names, spec, objectType, nested: true);
            var query = new ClassInitializationQuery(state, calls, names, locations, spec, regions);
            var result = locations.CreateContext(function).Get(query, init.Identity);
            bool same = mode.EndsWith("Same", StringComparison.Ordinal) || mode == "ReadOnly" || mode.EndsWith("Transparent", StringComparison.Ordinal) || mode is "ReadCatchPrefix" or "ReadPrelude";
            checks.True(ExitChecker.Check(function).IsValid, mode + " 受保护初始化输入契约");
            checks.True(result.IsSuccess && result.Value.CanAbsorb == same, mode + " 比较初始化与访问的展开目标：" + (result.Why ?? result.Value.Why));
            var output = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { slot }, locations, query).Run(function);
            checks.True(ExitChecker.Check(output.Function).IsValid, mode + " 受保护初始化输出契约");
            checks.True(output.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(c => c.Identity == init.Identity) == (!same || mode is "ReadOnly" or "ReadCatchPrefix"),
                mode + " 吸收后保留访问的原保护，缺少展开锚点时保持洞");
            if (!same || mode is "ReadOnly" or "ReadCatchPrefix") checks.True(output.Records.Any(r => !r.Removed && r.Reason?.Code == "structure.class-init.exception-region"),
                mode + " 保留展开目标不同或保护丢失的具体原因");
        }
    }
}
