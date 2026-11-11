using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
namespace Cpp2CS.Tests;
internal static class PathFactChecks
{
    public const string Command = "path-facts";
    public static int Run()
    {
        var a = new Assertions();
        void Check(bool falseArm, bool extraPredecessor, bool negate)
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var yes = new BlockIdentity(); var no = new BlockIdentity(); var end = new BlockIdentity();
            var x = t.Atom(new EntryAtom(new(SlotKind.Integer)),64); var y = t.Constant(3,64);
            var condition = t.Apply(new CoreOperator(CoreOperation.Equal),1,x,y);
            var branch = negate ? t.Apply(new CoreOperator(CoreOperation.Not),1,condition) : condition;
            var f = new FunctionBuilder(t,entry,64,new(t.Atom(new RootAtom(AddressRoot.Frame),64)));
            f.Blocks.Add(new(entry,[],[],new Branch(branch,yes,no)));
            f.Blocks.Add(new(yes,[],[],new Jump(end)));
            f.Blocks.Add(new(no,[],[],extraPredecessor ? new Jump(yes) : new Return([])));
            f.Blocks.Add(new(end,[],[],new Return([])));
            var state = new StateQueries(); var q = new PathFactQuery(state);
            var result = state.CreateContext(f.Freeze()).Get(q,new(new(falseArm?no:end,0),t.Apply(new CoreOperator(CoreOperation.Equal),1,y,x)));
            var expected = extraPredecessor ? PathTruth.Unknown : falseArm == negate ? PathTruth.True : PathTruth.False;
            a.True(result.IsSuccess && result.Value == expected,$"路径事实 false={falseArm} extra={extraPredecessor} not={negate} {result.Value}");
        }
        Check(false,false,false); Check(true,false,false); Check(false,true,false); Check(false,false,true);
        return a.Finish("路径事实快速检查");
    }
}
