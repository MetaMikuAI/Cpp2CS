using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Checks;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;
internal static class CheckQuickChecks
{
    public const string Command = "checks";
    private sealed class RuntimeMap(RuntimeFunction function) : IRuntimeFunctionMap
    { public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 1 } ? function : null; }
    public static int Run()
    {
        var a = new Assertions();
        void Frontier(int shape, int count, bool exit, bool cycle)
        {
            var t = new TermTable(); var start = new BlockIdentity(); var left = new BlockIdentity(); var right = new BlockIdentity(); var join = new BlockIdentity();
            var f = new FunctionBuilder(t, start, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var flag = t.Atom(new EntryAtom(new(SlotKind.Integer)), 1);
            f.Inputs.Add(new(new(SlotKind.Integer), flag));
            Statement Stop() => new TrapWhen(new(), t.Constant(1, 1));
            f.Blocks.Add(new(start, [], shape == 0 ? [Stop()] : [], shape == 0 ? new Return([]) : new Branch(flag, left, right)));
            f.Blocks.Add(new(left, [], shape is 1 or 2 ? [Stop()] : [], shape == 3 ? new Jump(start) : new Jump(join)));
            f.Blocks.Add(new(right, [], shape == 1 ? [Stop()] : [], new Jump(join)));
            f.Blocks.Add(new(join, [], shape == 4 ? [Stop()] : [], new Return([])));
            var query = new EventFrontierQuery((c, p) => Outcome<bool>.Success(c.Snapshot.Blocks.Single(b => b.Identity == p.Block).Statements.ElementAtOrDefault(p.Before) is TrapWhen));
            var result = new QueryContext(f.Freeze()).Get(query, new(new(start, 0)));
            a.True(result.IsSuccess && result.Value.Stops.Count == count && result.Value.ReachesExit == exit && result.Value.HasCycle == cycle, $"前沿 {shape}");
        }
        Frontier(0, 1, false, false); Frontier(1, 2, false, false); Frontier(2, 1, true, false); Frontier(3, 0, true, true); Frontier(4, 1, false, false);
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var integer = new DefinitionRef(new TypeDef { Index=0, Assembly="mscorlib.dll", Namespace="System", Name="Int64", Token=0, Attributes=TypeAttributes.Public, IsValueType=true, IsEnum=false }, []);
        var owner = new TypeDef { Index=0, Assembly="test", Namespace="", Name="Owner", Token=0, Attributes=TypeAttributes.Public, IsValueType=false, IsEnum=false, PackingSize=0, ClassSizeIsDefault=true, Size=(int)spec.Layout.ObjectHeaderSize+8 };
        owner.Fields = [new FieldDef { Index=0, Owner=owner, Name="Value", Type=integer, Offset=(int)spec.Layout.ObjectHeaderSize, Attributes=FieldAttributes.Public }];
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        void Check(string operation, bool barrier, bool expected, bool recognized = true, bool addressUse = false, bool firstDifferent = false)
        {
            var t = new TermTable(); var start = new BlockIdentity(); var good = new BlockIdentity(); var bad = new BlockIdentity();
            var x = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); var index = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            bool bounds = operation == "ThrowBounds", divide = operation == "ThrowDivideByZero";
            var type = bounds ? (TypeRef)new ArrayRef(integer, 1) : divide ? integer : new DefinitionRef(owner, []);
            var method = new MethodRef(new MethodDef { Index=0, Owner=owner, Name="Read", Token=0, Attributes=MethodAttributes.Static, ImplAttributes=0, Slot=-1, ReturnType=integer,
                Parameters=[new("value", type, 0, null, false), new("index",integer,0,null,false)] }, [], []);
            var f = new FunctionBuilder(t, start, 64, new(t.Atom(new RootAtom(AddressRoot.Frame),64)));
            f.Inputs.Add(new(new(SlotKind.Integer),x)); f.Inputs.Add(new(new(SlotKind.Integer,1),index));
            Term Add(Term v, long n) => t.Apply(new CoreOperator(CoreOperation.Add), 64, v, t.Constant(n,64));
            var first = new List<Statement>();
            var condition = t.Apply(new CoreOperator(CoreOperation.Equal),1,x,t.Constant(0,64));
            if (bounds)
            {
                var id = new ReadIdentity(); var length = t.Atom(new ResultAtom(id),64);
                first.Add(new MemoryRead(id, Add(x,spec.Layout.Field("Il2CppArray","max_length").ByteOffset),64,length));
                condition = t.Apply(new CoreOperator(CoreOperation.UnsignedLess),1,index,length);
            }
            f.Blocks.Add(new(start,[],[..first],bounds ? new Branch(condition,good,bad) : new Branch(condition,bad,good)));
            var body = new List<Statement>();
            if (barrier) body.Add(new Call(new(),new ImageFunction(2),[],[]));
            Term result;
            if (divide) result = t.Apply(new CoreOperator(CoreOperation.SignedDivide),64,t.Constant(10,64),x);
            else
            {
                var address = Add(x,bounds ? spec.Layout.ArrayDataStart : spec.Layout.ObjectHeaderSize);
                if(bounds) address = t.Apply(new CoreOperator(CoreOperation.Add),64,address,t.Apply(new CoreOperator(CoreOperation.Multiply),64,index,t.Constant(8,64)));
                if (addressUse)
                {
                    body.Add(new Call(new(), new ImageFunction(10), firstDifferent
                        ? [new(new(SlotKind.Integer), Add(address, 8)), new(new(SlotKind.Integer, 1), address), new(new(SlotKind.Integer, 2), t.Constant(0, 64))]
                        : [new(new(SlotKind.Integer), address), new(new(SlotKind.Integer, 1), t.Constant(0, 64))], []));
                    result = t.Constant(0, 64);
                }
                else { var id=new ReadIdentity(); result=t.Atom(new ResultAtom(id),64); body.Add(new MemoryRead(id,address,64,result)); }
            }
            f.Blocks.Add(new(good,[],[..body],new Return([new(new(SlotKind.Integer),result)])));
            f.Blocks.Add(new(bad,[],[new Call(new(),new ImageFunction(1),[],[],true)],new Unreachable()));
            var target = new MethodRef(new MethodDef { Index=1, Owner=owner, Name="Take", Token=0,
                Attributes=MethodAttributes.Public | MethodAttributes.Static, ImplAttributes=0, Slot=-1,
                ReturnType=new DefinitionRef(new TypeDef { Index=2, Assembly="mscorlib.dll", Namespace="System", Name="Void", Token=0,
                    Attributes=TypeAttributes.Public, IsValueType=true, IsEnum=false },[]),
                Parameters=firstDifferent ? [new("first",new ByRefRef(integer),0,null,false),new("second",new ByRefRef(integer),0,null,false)] : [new("value",new ByRefRef(integer),0,null,false)] },[],[]);
            var calls = new CallNamingQuery(binder,new NamingChecks.Map(addressUse ? [new(target, BindingEntryKind.Ordinary)] : []),new RuntimeMap(catalog.Functions.First(f=>f.Operation.Name==operation)),catalog);
            var state = new StateQueries(); var names = new ValueNamingQuery(state,calls,NamingFacts.Empty,spec,binder,binder.Entry(method,BindingEntryKind.Ordinary).Value);
            var locations = new ManagedLocationQuery(state,names,layouts,spec); var checks = new CheckQueries(state,calls,locations);
            var r = locations.CreateContext(f.Freeze()).Get(checks.Checks,new(start,bad));
            a.True(r.IsSuccess && (recognized ? r.Value is { } check && check.CanAbsorb==expected : r.Value is null), $"{operation} barrier={barrier}: {r.Why} { (r.IsSuccess ? r.Value?.ExplicitReason : null)}");
        }
        Check("ThrowNullReference",false,true); Check("ThrowNullReference",true,false); Check("ThrowBounds",false,true); Check("ThrowDivideByZero",false,true); Check("ThrowManaged",false,false,false);
        Check("ThrowNullReference", false, true, addressUse: true);
        Check("ThrowNullReference", true, false, addressUse: true);
        Check("ThrowBounds", false, true, addressUse: true);
        Check("ThrowBounds", true, false, addressUse: true);
        Check("ThrowBounds", false, false, addressUse: true, firstDifferent: true);
        return a.Finish("事件前沿与条件抛出");
    }
}
