using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class StructureChecks
{
    private static void ExceptionClosureCases(Assertions checks)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var nothing = new TypeDef { Index = 0, Assembly = "mscorlib.dll", Namespace = "System", Name = "Void", Token = 0,
            Attributes = System.Reflection.TypeAttributes.Public, IsValueType = true, IsEnum = false };
        var method = new MethodDef { Index = 0, Owner = nothing, Name = "Use", Token = 0,
            Attributes = System.Reflection.MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = new DefinitionRef(nothing, []) };
        var model = new ProgramModel { MetadataVersion = 31, Assemblies = [], Types = [nothing], Methods = [method],
            Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [] };
        var code = new CodeEntry(10, EntryKind.Method, MethodRef.Open(method), 0, null);
        var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = [code],
            ByAddress = new Dictionary<ulong, ImmutableArray<CodeEntry>> { [10] = [code] }, Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(),
            MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(), InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
        var image = new InputMemoryImage();
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var metadata = catalog.Functions.First(f => f.Operation.Name == "InitializeMetadata" && f.Signature is { ReturnType.Size: 0 });
        var facts = new GlobalFacts(image, model, map, spec, "arm64") { Symbols = [new(metadata.MangledName, 20, 4)] };
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        foreach (var mode in new[] { "Forward", "Blocked", "NoHandlers" })
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var next = new BlockIdentity();
            var h1 = new BlockIdentity(); var h2 = new BlockIdentity(); var join = new BlockIdentity(); var caught = new BlockIdentity(); var resume = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var imageRoot = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var address = t.Apply(new CoreOperator(CoreOperation.Add), 64, frame, t.Constant(unchecked((ulong)-8L), 64));
            var slot = new AbstractSlot(SlotKind.Integer); var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = imageRoot };
            if (mode == "NoHandlers")
            {
                f.Blocks.Add(new(entry, [], [new Call(new(), new ImageFunction(10), [], [])], new Jump(next)));
                f.Blocks.Add(new(next, [], [new Call(new(), new ImageFunction(10), [], [])], new Jump(caught)));
            }
            else
            {
                f.Blocks.Add(new(entry, [], [new MemoryWrite(new(), address, 64, t.Constant(7, 64)),
                    new Call(new(), new ImageFunction(20), [new(slot, imageRoot)], []),
                    new Call(new(), new ImageFunction(10), [new(slot, t.Constant(0, 64))], [], Unwind: h1)], new Jump(next)));
                f.Blocks.Add(new(next, [], [new Call(new(), new ImageFunction(10), [new(slot, t.Constant(0, 64))], [], Unwind: h2)], new Jump(caught)));
                foreach (var h in new[] { h1, h2 })
                {
                    var exception = t.Atom(new ExceptionAtom(h), 64); var selector = t.Atom(new SelectorAtom(h), 64);
                    var read = new ReadIdentity(); var value = t.Atom(new ResultAtom(read), 64);
                    var statements = new List<Statement> { new MemoryRead(read, address, 64, value) };
                    if (mode == "Blocked") statements.Add(new MemoryFence(new(), "observable"));
                    f.Blocks.Add(new(h, [], [.. statements], new Jump(join), new(exception, selector,
                        [new(ClauseKind.Catch, [new PointerTarget.Internal(100)]) { Selector = 1, TypeName = spec.ManagedExceptionWrapperTypeName }, new(ClauseKind.Cleanup, [])])));
                }
                var exId = new MergeIdentity(); var selId = new MergeIdentity(); var ex = t.Atom(new ResultAtom(exId), 64); var sel = t.Atom(new ResultAtom(selId), 64);
                var left = new BlockIdentity(); var right = new BlockIdentity(); var test = new BlockIdentity();
                f.Blocks.Add(new(join, [new(exId, ex, [new(h1, t.Atom(new ExceptionAtom(h1), 64)), new(h2, t.Atom(new ExceptionAtom(h2), 64))]),
                    new(selId, sel, [new(h1, t.Atom(new SelectorAtom(h1), 64)), new(h2, t.Atom(new SelectorAtom(h2), 64))])], [], new Branch(t.Constant(1, 1), left, right)));
                f.Blocks.Add(new(left, [], [], new Jump(test))); f.Blocks.Add(new(right, [], [], new Jump(test)));
                var outerExId = new MergeIdentity(); var outerSelId = new MergeIdentity();
                var outerEx = t.Atom(new ResultAtom(outerExId), 64); var outerSel = t.Atom(new ResultAtom(outerSelId), 64);
                f.Blocks.Add(new(test, [new(outerExId, outerEx, [new(left, ex), new(right, ex)]), new(outerSelId, outerSel, [new(left, sel), new(right, sel)])], [],
                    new Branch(t.Apply(new CoreOperator(CoreOperation.Equal), 1, outerSel, t.Constant(1, 64)), caught, resume)));
                f.Blocks.Add(new(resume, [], [], new ResumeUnwind(outerEx)));
            }
            f.Blocks.Add(new(caught, [], [], new Return([])));
            var input = f.Freeze();
            checks.True(ExitChecker.Check(input).IsValid, mode + " 闭合输入契约");
            if (mode != "NoHandlers")
            {
                checks.True(ReferenceEquals(ExceptionEntries.Run(input).Function, input) && ReferenceEquals(ExceptionSelectors.Run(input, spec).Function, input),
                    mode + " 初始帧读取阻止入口归一与选择值折叠");
            }
            var result = StructureRecovery.Run(input, new(method, code, facts), binder, BindingEntryKind.Ordinary);
            checks.True(ExitChecker.Check(result.Function).IsValid, mode + " 闭合输出契约");
            checks.True(result.Function.Blocks.Count(b => b.Handler is not null) == (mode == "NoHandlers" ? 0 : mode == "Forward" ? 1 : 2), mode + " 闭合后的逻辑入口数");
            if (mode == "Forward")
            {
                checks.True(result.Function.Blocks.All(b => b.End is not Branch), "效果消去后归一折叠选择值测试");
                checks.True(result.Records.Count(r => r.Removed && r.Kind == "forwarded-read") == 2, "闭合保留前轮已应用的消去记录");
                checks.True(ReferenceEquals(ExceptionEntries.Run(result.Function).Function, result.Function)
                    && ReferenceEquals(ExceptionSelectors.Run(result.Function, spec).Function, result.Function), "结构出口已经闭合");
            }
            if (mode == "Blocked") checks.True(result.Function.Blocks.SelectMany(b => b.Statements).OfType<MemoryFence>().Count() == 2,
                "入口不能收缩时终止，保留可观察屏障");
            if (mode == "NoHandlers") checks.True(ReferenceEquals(input, result.Function), "没有处理入口时不触发闭合改写");
        }
        var t2 = new TermTable(); var b2 = new BlockIdentity(); var f2 = new FunctionBuilder(t2, b2, 64, new(t2.Constant(0, 64)));
        f2.Blocks.Add(new(b2, [], [], new Return([]))); var identity = f2.Freeze();
        var before = new StructureResult(identity, [new("applied", 1, "", true), new("rejected", 2, "旧原因", false)], ["甲"])
            { Timings = ImmutableDictionary<string, double>.Empty.Add("效果", 2) };
        var after = new StructureResult(identity, [new("applied", 3, "", true), new("rejected", 2, "新原因", false)], ["乙", "甲"])
            { Timings = ImmutableDictionary<string, double>.Empty.Add("效果", 3) };
        var accumulated = after.Accumulate(before);
        checks.True(accumulated.Records.Count(r => r.Removed) == 2 && accumulated.Records.Single(r => !r.Removed).Evidence == "新原因"
            && accumulated.Assumptions.Length == 2 && accumulated.Timings["效果"] == 5, "各轮消去累计记录、假设与用时，拒绝原因取末轮");
    }
}
