using System.Collections.Immutable;
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
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void ExceptionChecks(Assertions checks, ProgramModel program)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8);
        var types = new ManagedTypes(program, layouts, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var method = MethodRef.Open(program.Methods.Single(m => m.Name == "Add" && m.Owner.Name == "Cases"));
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        foreach (var mode in new[] { "Catch", "Rethrow", "Transparent", "TransparentBegin", "State", "Typed", "TwoClauses", "Fault", "EscapingFrame", "WrongResume", "SelectorUse", "OtherCxxType" })
        {
            var terms = new TermTable(); var entry = new BlockIdentity(); var handler = new BlockIdentity(); var body = new BlockIdentity();
            var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(terms, entry, 64, new(frame));
            var exception = terms.Atom(new ExceptionAtom(handler), 64);
            var selector = terms.Atom(new SelectorAtom(handler), 64);
            var slot = new AbstractSlot(SlotKind.Integer);
            var parameter = terms.Atom(new EntryAtom(slot), 64); builder.Inputs.Add(new(slot, parameter));
            var other = new AbstractSlot(SlotKind.Integer, 1); builder.Inputs.Add(new(other, terms.Atom(new EntryAtom(other), 64)));
            Call System(string symbol, Term[] args, out Term result, bool noReturn = false)
            {
                var id = new CallIdentity(); result = terms.Atom(new ResultAtom(id), 64);
                return new(id, new ImportedTarget(new ImportSymbol(symbol)), args.Select((a, i) => new SlotValue(new(SlotKind.Integer, i), a)).ToImmutableArray(),
                    noReturn || symbol == "__cxa_end_catch" ? [] : [new(slot, result)], noReturn);
            }
            var begin = System("__cxa_begin_catch", [exception], out var payload);
            var end = System("__cxa_end_catch", [], out _);
            var rethrow = System("__cxa_rethrow", [], out _, true);
            var callIdentity = new CallIdentity(); var callResult = terms.Atom(new ResultAtom(callIdentity), 64);
            var protectedCall = new Call(callIdentity, new ImageFunction(10), [new(slot, parameter), new(other, parameter),
                new(new(SlotKind.Integer, 2), terms.Constant(0, 64))], [new(slot, callResult)], Unwind: handler);
            if (mode == "EscapingFrame") protectedCall = protectedCall with
            { Target = new ImportedTarget(new ImportSymbol("external_observer")), Arguments = [new(slot, frame)] };
            var map = new ExceptionRuntimeMap();
            var namedCalls = new CallNamingQuery(binder, new NamingChecks.Map([new(method, BindingEntryKind.Ordinary)]), map, catalog);
            var defining = terms.Slice(parameter, 0, 32);
            var writes = new List<Statement>();
            if (mode == "State") writes.Add(new MemoryWrite(new(), frame, 32, defining));
            writes.Add(protectedCall);
            builder.Blocks.Add(new(entry, [], [.. writes], new Return([new(slot, terms.Constant(1, 32))])));
            builder.Blocks.Add(new(handler, [], [], new Jump(body), new(exception, selector, mode == "OtherCxxType" ? [new(ClauseKind.Catch, [new PointerTarget.Internal(100)]) { Selector = 1, TypeName = "other" }]
                : [new(ClauseKind.CatchAll, [])])));
            if (mode == "Transparent") builder.Blocks.Add(new(body, [], [], new ResumeUnwind(exception)));
            else if (mode == "WrongResume") builder.Blocks.Add(new(body, [], [], new ResumeUnwind(parameter)));
            else if (mode == "TransparentBegin") builder.Blocks.Add(new(body, [], [begin, end], new ResumeUnwind(exception)));
            else if (mode == "EscapingFrame") builder.Blocks.Add(new(body, [], [new MemoryWrite(new(), frame, 64, parameter)], new ResumeUnwind(exception)));
            else if (mode == "Fault") builder.Blocks.Add(new(body, [], [], new Return([new(slot, terms.Constant(7, 32))])));
            else
            {
                var statements = new List<Statement> { begin };
                var readId = new ReadIdentity(); var captured = terms.Atom(new ResultAtom(readId), 64);
                statements.Add(new MemoryRead(readId, payload, 64, captured));
                if (mode == "Typed" || mode == "TwoClauses")
                {
                    // 类型实体由元数据槽命名；类型判断只依赖被捕获对象的 klass。
                    var accepted = new BlockIdentity(); var rejected = new BlockIdentity();
                    var image = terms.Atom(new RootAtom(AddressRoot.Image), 64); builder.ImageBase = image;
                    var targetId = new ReadIdentity(); var target = terms.Atom(new ResultAtom(targetId), 64);
                    statements.Add(new MemoryRead(targetId, image, 64, target));
                    var classId = new ReadIdentity(); var klass = terms.Atom(new ResultAtom(classId), 64);
                    statements.Add(new MemoryRead(classId, captured, 64, klass));
                    var typeCall = new CallIdentity(); var tested = terms.Atom(new ResultAtom(typeCall), 64);
                    var isAssignable = catalog.Functions.Single(x => x.Operation.Name == "IsAssignableFrom"); map.TypeTest = isAssignable;
                    statements.Add(new Call(typeCall, new ImageFunction(2), [new(slot, target), new(other, klass)], [new(slot, tested)]));
                    builder.Blocks.Add(new(body, [], [.. statements], new Branch(terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, terms.Slice(tested, 0, 1), terms.Constant(0, 1)), accepted, rejected)));
                    builder.Blocks.Add(new(accepted, [], [end], new Return([new(slot, terms.Constant(7, 32))])));
                    if (mode == "TwoClauses")
                    {
                        var second = new BlockIdentity(); var miss = new BlockIdentity();
                        var secondCall = new CallIdentity(); var test2 = terms.Atom(new ResultAtom(secondCall), 64);
                        builder.Blocks.Add(new(rejected, [], [new Call(secondCall, new ImageFunction(2), [new(slot, target), new(other, klass)], [new(slot, test2)])],
                            new Branch(terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, terms.Slice(test2, 0, 1), terms.Constant(0, 1)), second, miss)));
                        builder.Blocks.Add(new(second, [], [end with { Identity = new() }], new Return([new(slot, terms.Constant(8, 32))])));
                        builder.Blocks.Add(new(miss, [], [rethrow], new Unreachable()));
                    }
                    else builder.Blocks.Add(new(rejected, [], [rethrow], new Unreachable()));
                }
                else
                {
                    Term value = mode == "SelectorUse" ? terms.Slice(selector, 0, 32) : terms.Constant(7, 32);
                    if (mode == "Rethrow") statements.Add(rethrow);
                    else if (mode == "State")
                    { var id = new ReadIdentity(); value = terms.Atom(new ResultAtom(id), 32); statements.Add(new MemoryRead(id, frame, 32, value)); }
                    else statements.Add(end);
                    builder.Blocks.Add(new(body, [], [.. statements], mode == "Rethrow" ? new Unreachable() : new Return([new(slot, value)])));
                }
            }
            var names = mode is "Typed" or "TwoClauses" ? new NamingFacts(ImmutableDictionary<ulong, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>>.Empty.Add(0,
                Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(types.Object))), ImmutableDictionary<ulong, FlagEvidence>.Empty, true) : NamingFacts.Empty;
            var function = builder.Freeze();
            if (mode == "EscapingFrame")
            {
                var state = new StateQueries();
                checks.True(state.CreateContext(function).Get(state.Escapes, 0) is { IsSuccess: true, Value.Any: true }, "反例帧地址确实逃逸");
            }
            var result = new IntegerLowering(function, method, binder, types, calls: namedCalls, effects: new ManagedCallEffects(namedCalls), spec: spec, names: names).Run();
            if (mode is "SelectorUse" or "OtherCxxType")
            { checks.True(result.Failure?.Reason.Code == "lowering.Exception.Selector", "选择值其他用法和其他 C++ 类型均报 Selector 洞"); continue; }
            if (mode is "Fault" or "EscapingFrame" or "WrongResume") { checks.True(result.Failure?.Reason.Code == "lowering.Exception.Fault", "没有包装对象的可观察清理报 fault 洞"); continue; }
            checks.True(result.Body is not null, "异常下降 " + mode + ": " + result.Failure);
            if (result.Body is null) continue;
            checks.True(result.Body.Regions.Count == (mode is "Transparent" or "TransparentBegin" ? 0 : mode == "TwoClauses" ? 2 : 1), "异常子句数量 " + mode);
            if (mode == "Rethrow") checks.True(result.Body.Blocks.SelectMany(b => b.Statements).OfType<ManagedRethrow>().Any(), "当前捕获对象下降为 rethrow");
            var emitter = new BodyEmitter(new Skeleton(program, 16), types);
            var problems = emitter.Emit([result.Body]); checks.True(problems.Count == 0, "异常 CIL 契约 " + mode + ": " + string.Join(';', problems.Values));
        }
    }
    private sealed class ExceptionRuntimeMap : IRuntimeFunctionMap
    {
        public RuntimeFunction? TypeTest { get; set; }
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 2 } ? TypeTest : null;
    }
}
