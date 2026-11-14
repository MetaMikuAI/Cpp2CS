using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Structure;

namespace Cpp2CS.Tests;

internal static partial class StructureChecks
{
    private static void ExceptionEntryCases(Assertions checks)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        foreach (var mode in new[] { "Merge", "Statements", "Clauses", "Normal", "SelectorUse", "OtherType" })
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var second = new BlockIdentity(); var third = new BlockIdentity();
            var hs = Enumerable.Range(0, 3).Select(_ => new BlockIdentity()).ToArray();
            var jumps = Enumerable.Range(0, 2).Select(_ => new BlockIdentity()).ToArray(); var join = new BlockIdentity();
            var caught = new BlockIdentity(); var resume = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64);
            var f = new FunctionBuilder(t, entry, 64, new(frame));
            var slot = new AbstractSlot(SlotKind.Integer); var parameter = t.Atom(new EntryAtom(slot), 64); f.Inputs.Add(new(slot, parameter));
            var es = hs.Select(h => t.Atom(new ExceptionAtom(h), 64)).ToArray();
            var ss = hs.Select(h => t.Atom(new SelectorAtom(h), 64)).ToArray();
            var clause = new ExceptionClause(ClauseKind.Catch, [new PointerTarget.Internal(100)])
            { Selector = 3, TypeName = mode == "OtherType" ? "other" : spec.ManagedExceptionWrapperTypeName };
            var ps = new[] { entry, second, third };
            for (int i = 0; i < 3; i++)
            {
                f.Blocks.Add(new(ps[i], [], [new Call(new(), new ImageFunction(20), [], [], Unwind: hs[i])],
                    i < 2 ? new Jump(ps[i + 1]) : mode == "Normal" ? new Branch(t.Slice(parameter, 0, 1), join, caught) : new Jump(caught)));
                f.Blocks.Add(new(hs[i], [], [], new Jump(i < 2 ? jumps[i] : join), new(es[i], ss[i],
                    [i == 2 && mode == "Clauses" ? clause with { Selector = 4 } : clause, new(ClauseKind.Cleanup, [])])));
                if (i < 2) f.Blocks.Add(new(jumps[i], [], mode == "Statements" && i == 0
                    ? [new MemoryWrite(new(), frame, 64, parameter)] : [], new Jump(join)));
            }
            Merge M(Term[] values)
            {
                var id = new MergeIdentity(); return new(id, t.Atom(new ResultAtom(id), 64),
                    values.Select((v, i) => new Incoming(i < 2 ? jumps[i] : hs[i], v)).ToImmutableArray());
            }
            var ex = M(es); var sel = M(ss); var state = M([t.Constant(10, 64), t.Constant(20, 64), t.Constant(30, 64)]);
            if (mode == "Normal")
            {
                ex = ex with { Inputs = ex.Inputs.Add(new(third, parameter)) };
                sel = sel with { Inputs = sel.Inputs.Add(new(third, parameter)) };
                state = state with { Inputs = state.Inputs.Add(new(third, parameter)) };
            }
            var condition = t.Apply(new CoreOperator(CoreOperation.NotEqual), 1, t.Slice(sel.Result, 0, 32), t.Constant(3, 32));
            f.Blocks.Add(new(join, [ex, sel, state], [], new Branch(condition, resume, caught)));
            // 捕获出口不使用合流，避免普通流进入该块时的无定义使用。
            f.Blocks.Add(new(caught, [], [], new Return([])));
            f.Blocks.Add(new(resume, [], [], new ResumeUnwind(ex.Result)));
            var input = f.Freeze();
            if (mode is "Merge" or "Clauses" or "Normal")
            {
                var projected = ExceptionSelectors.Run(input,spec);
                checks.True(mode == "Merge" ? projected.Folded.Count == 3 : projected.Folded.Count == 0,
                    "逐入边投影仅折叠全部匹配同一包装选择值的测试");
            }
            checks.True(ExitChecker.Check(input).IsValid, mode + " 归一输入契约");
            var normalized = ExceptionEntries.Run(input);
            checks.True(ExitChecker.Check(normalized.Function).IsValid, mode + " 归一输出契约");
            bool valid = mode is "Merge" or "SelectorUse" or "OtherType";
            checks.True(normalized.After == (valid ? 1 : 3), mode + " 入口数量");
            if (!valid) continue;
            var h = normalized.Function.Blocks.Single(b => b.Handler is not null);
            checks.True(h.Identity == join && h.Merges.Single().Inputs.Select(i => i.Predecessor).ToHashSet().SetEquals(ps), "三个入口两种跳板路径的状态直接取展开边");
            checks.True(h.Merges.Single().Inputs.Select(i => i.Value.ConstantValue).SequenceEqual(new System.Numerics.BigInteger?[] { 10, 20, 30 }), "展开状态逐边保持");
            var folded = ExceptionSelectors.Run(normalized.Function, spec);
            checks.True(mode == "OtherType" ? folded.Failures.Count == 1 && folded.Folded.Count == 0
                : folded.Folded.Count == 1 && folded.Function.Blocks.Single(b => b.Identity == join).End is Jump { Target: var target } && target == caught,
                "选择值按子句过滤序号折叠，其他 C++ 类型保留洞");
        }
    }
}
