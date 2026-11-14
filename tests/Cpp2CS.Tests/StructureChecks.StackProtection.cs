using System.Collections.Immutable;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static partial class StructureChecks
{
    private static void StackProtectionCases(Assertions checks)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var binder = new MethodBinder(new(new FieldLayouts(spec, 8, 8)), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        foreach (var mode in new[] { "Normal", "OtherEvent", "Write", "OtherSource", "SharedFailure", "MixedFailure" })
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var head = new BlockIdentity(); var other = new BlockIdentity();
            var good = new BlockIdentity(); var bad = new BlockIdentity(); var mixed = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var thread = t.Atom(new RootAtom(AddressRoot.Thread), 64);
            var flag = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var f = new FunctionBuilder(t, entry, 64, new(frame)) { ThreadPointer = thread }; f.Inputs.Add(new(new(SlotKind.Integer), flag));
            Term Add(Term root, long offset) => t.Apply(new CoreOperator(CoreOperation.Add), 64, root, t.Constant(unchecked((ulong)offset), 64));
            Term Read(List<Statement> statements, Term address)
            { var id = new ReadIdentity(); var result = t.Atom(new ResultAtom(id), 64); statements.Add(new MemoryRead(id, address, 64, result)); return result; }
            var first = new List<Statement>(); var source = Read(first, Add(thread, 24));
            var save = new MemoryWrite(new(), Add(frame, -8), 64, source); first.Add(save);
            first.Add(new Call(new(), new ImageFunction(999), [], []));
            f.Blocks.Add(new(entry, [], [.. first], mode is "SharedFailure" or "MixedFailure" ? new Branch(t.Slice(flag, 0, 1), head, other) : new Jump(head)));
            foreach (var id in mode is "SharedFailure" or "MixedFailure" ? new[] { head, other } : new[] { head })
            {
                var statements = new List<Statement>(); var current = Read(statements, Add(thread, mode == "OtherSource" ? 32 : 24));
                var copy = Read(statements, Add(frame, -8));
                f.Blocks.Add(new(id, [], [.. statements], new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual), 1, current, copy), mode == "MixedFailure" && id == other ? mixed : bad, good)));
            }
            f.Blocks.Add(new(good, [], [], new Return([new(new(SlotKind.Integer), t.Constant(7, 64))])));
            var failed = new List<Statement>();
            if (mode == "OtherEvent") failed.Add(new Call(new(), new ImageFunction(998), [], []));
            if (mode == "Write") failed.Add(new MemoryWrite(new(), flag, 64, t.Constant(1, 64)));
            failed.Add(new Call(new(), new ImportedTarget(new("__stack_chk_fail")), [], [], true));
            f.Blocks.Add(new(bad, [], [.. failed], new Unreachable()));
            if (mode == "MixedFailure") f.Blocks.Add(new(mixed, [], [new Call(new(), new ImageFunction(998), [], []),
                new Call(new(), new ImportedTarget(new("__stack_chk_fail")), [], [], true)], new Unreachable()));
            var state = new StateQueries(); var names = new ValueNamingQuery(state, calls, NamingFacts.Empty, spec, binder);
            var result = new UnobservableEffects(state, calls, names, new InputMemoryImage(), new HashSet<AbstractSlot> { new(SlotKind.Integer) }).Run(f.Freeze());
            checks.True(ExitChecker.Check(result.Function).IsValid, mode + " 栈保护输出契约");
            bool removed = mode is "Normal" or "SharedFailure";
            checks.True(result.Assumptions.Contains(UnobservableEffects.StackProtectionAssumption) == (removed || mode == "MixedFailure"), mode + " 栈保护假设仅在证明后登记");
            checks.True(result.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(call => call.Target is ImportedTarget) != removed,
                mode + " 只删除没有其他事件的不可达失败臂");
            if (removed) checks.True(!result.Function.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>().Any(), "保护值读取和帧副本随比较删除");
            if (mode == "MixedFailure") checks.True(result.Function.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>().Any(w => w.Identity == save.Identity),
                "未消去的检查仍读取帧副本，不能删除共享保存");
        }
    }
}
