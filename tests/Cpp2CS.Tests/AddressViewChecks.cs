using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
namespace Cpp2CS.Tests;

internal static class AddressViewChecks
{
    public const string Command = "address-views";
    public static int Run()
    {
        var a = new Assertions();
        foreach (var step in new[] { 16, 32, 8 })
        foreach (var otherBase in new[] { false, true })
        {
            var t = new TermTable(); var start = new BlockIdentity(); var loop = new BlockIdentity(); var exit = new BlockIdentity();
            var root = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var other = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            var id = new MergeIdentity(); var pointer = t.Atom(new ResultAtom(id), 64);
            Term Add(Term x, long n) => t.Apply(new CoreOperator(CoreOperation.Add), 64, x, t.Constant(unchecked((ulong)n), 64));
            var f = new FunctionBuilder(t, start, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            f.Blocks.Add(new(start, [], [], new Jump(loop)));
            f.Blocks.Add(new(loop, [new(id, pointer, [new(start, Add(root, 8)), new(loop, Add(otherBase ? other : pointer, step))])], [],
                new Branch(t.Atom(new EntryAtom(new(SlotKind.Integer, 2)), 1), loop, exit)));
            f.Blocks.Add(new(exit, [], [], new Return([])));
            var state = new StateQueries(); var c = state.CreateContext(f.Freeze());
            var matching = new ExistingMergeQuery(state);
            var inputs = f.Blocks[1].Merges[0].Inputs;
            a.True(c.Get(matching, new(loop, inputs)).Value == pointer, "逐边匹配已有合流");
            a.True(!c.Get(matching, new(loop, [new(start, inputs[1].Value),new(loop, inputs[0].Value)])).IsSuccess, "交换来源不能匹配合流");
            var indexed=t.Apply(new CoreOperator(CoreOperation.Add),64,root,
                t.Apply(new CoreOperator(CoreOperation.Multiply),64,other,t.Constant(16,64)));
            var indexedOrigin=c.Get(new StridedAddressQuery(state),new(indexed,16));
            a.True(indexedOrigin.IsSuccess && indexedOrigin.Value.Base==root && indexedOrigin.Value.Remainder==0,"变量下标的对齐表项来源");
            var found = c.Get(new StridedAddressQuery(state), new(Add(pointer, -8), 16));
            a.True(found.IsSuccess == (!otherBase && step % 16 == 0), $"步长 {step} 异基址 {otherBase}");
            if (found.IsSuccess) a.True(found.Value.Base == root && found.Value.Remainder == 0, "表项基址与余数");
        }
        foreach (var overwrite in new[] { false, true })
        {
            var t = new TermTable(); var start = new BlockIdentity(); var loop = new BlockIdentity(); var exit = new BlockIdentity();
            var root = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64);
            var readId = new ReadIdentity(); var read = t.Atom(new ResultAtom(readId), 64);
            var f = new FunctionBuilder(t, start, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            f.Blocks.Add(new(start, [], [], new Jump(loop)));
            Statement write = overwrite ? new MemoryWrite(new(), root, 64, t.Constant(123, 64)) : new Call(new(), new ImageFunction(1), [], []);
            f.Blocks.Add(new(loop, [], [new MemoryRead(readId, root, 64, read), write], new Branch(t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 1), loop, exit)));
            f.Blocks.Add(new(exit, [], [], new Return([])));
            var state = new StateQueries(); var c = state.CreateContext(f.Freeze());
            var resolved = c.Get(state.Resolve, read);
            var found = c.Get(new ReadLocationQuery(state), read);
            a.True(found.IsSuccess == !overwrite, $"循环读取视图不接受写入值 {overwrite}");
            if (found.IsSuccess) a.True(found.Value.Root == root && resolved.Value.Identity is MemoryMerge, "读取视图保留内存合流版本");
        }
        {
            var t=new TermTable(); var start=new BlockIdentity(); var left=new BlockIdentity(); var right=new BlockIdentity(); var end=new BlockIdentity();
            var f=new FunctionBuilder(t,start,64,new(t.Atom(new RootAtom(AddressRoot.Frame),64)));
            var x=t.Atom(new EntryAtom(new(SlotKind.Integer)),64); var y=t.Atom(new EntryAtom(new(SlotKind.Integer,1)),64);
            var id=new MergeIdentity(); var pointer=t.Atom(new ResultAtom(id),64);
            var readId=new ReadIdentity(); var read=t.Atom(new ResultAtom(readId),32);
            f.Blocks.Add(new(start,[],[],new Branch(t.Atom(new EntryAtom(new(SlotKind.Integer,2)),1),left,right)));
            f.Blocks.Add(new(left,[],[],new Jump(end))); f.Blocks.Add(new(right,[],[],new Jump(end)));
            f.Blocks.Add(new(end,[new(id,pointer,[new(left,x),new(right,y)])],[new MemoryRead(readId,pointer,32,read)],new Return([])));
            var state=new StateQueries(); var c=state.CreateContext(f.Freeze());
            var value=t.Apply(new CoreOperator(CoreOperation.Add),32,read,t.Constant(1,32));
            var sources=c.Get(new IncomingValuesQuery(state),new(value,end));
            a.True(sources.IsSuccess && sources.Value.Length==2,"共享块的读取表达式逐入边投影");
            foreach (var input in sources.Value)
            {
                var projected=input.Value.Operands[0];
                var location=c.Get(new ReadLocationQuery(state),projected);
                a.True(location.IsSuccess && location.Value.Root==(input.Predecessor==left?x:y),"读取地址与入边对应");
                a.True(projected.Identity is EdgeReadAtom && projected!=c.Get(state.Resolve,read).Value,"投影保留原读取与边身份");
            }
        }
        return a.Finish("地址视图检查");
    }
}
