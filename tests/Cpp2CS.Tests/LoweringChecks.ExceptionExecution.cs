using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Exceptions;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void ExceptionExecutionChecks(Assertions checks, ProgramModel original)
    {
        using var source = new CompiledSource("""
            public class E : System.Exception { public int Value; }
            public static class Cases {
                public static int Add(int a,int b) => a+b;
                public static int SharedFinally(int a,int b) { try { Add(a,b); } finally { Add(b,a); } return 7; }
                public static int SharedBranch(int a,int b) { try { Add(a,b); } finally { if(a!=0) Add(b,a); } return 7; }
                public static int CopiedFinally(int a,int b) { try { Add(a,b); } finally { Add(b,a); } return 7; }
                public static int CopiedGuarded(int a,int b) { try { Add(a,b); } finally { Add(b,a); } return 7; }
                public static int CopiedUnknownGuard(int a,int b) { try { Add(a,b); } catch { Add(b,a); if(a!=0) throw; return 7; } Add(b,a); return 7; }
                public static int CopiedGuardedOut(int a,int b) => 0;
                public static int CopiedUnknownGuardOut(int a,int b) => 0;
                public static int CopiedEmpty(int a,int b) { try { Add(a,b); } finally { } return 7; }
                public static int CopiedEmptyOut(int a,int b) => 0;
                public static int CopiedSharedEntry(int a,int b) { if(a==0) { Add(b,a); return 7; } try { Add(a,b); } finally { Add(b,a); } return 7; }
                public static int CopiedSharedEntryOut(int a,int b) => 0;
                public static int CopiedMismatch(int a,int b) { try { Add(a,b); } catch { Add(b,a); throw; } Add(a,a); return 7; }
                public static int CopiedFinallyOut(int a,int b) => 0;
                public static int CopiedMismatchOut(int a,int b) => 0;
                public static int SharedMulti(int a,int b) { try { Add(a,b); if(a!=0) return 11; return 22; } finally { Add(b,a); } }
                public static int SharedThrow(int a,int b) { try { Add(a,b); } finally { if(b==0) throw null; Add(b,a); } return 7; }
                public static int FinallyInFinally(int a,int b) { try { Add(a,b); } finally { try { Add(b,a); } finally { Add(a,a); } } return 7; }
                public static int FinallyInTry(int a,int b) { try { try { Add(a,b); } finally { Add(b,a); } Add(a,a); } catch { return 3; } return 7; }
                public static int SharedMultiOut(int a,int b) => 0;
                public static int SharedThrowOut(int a,int b) => 0;
                public static int FinallyInFinallyOut(int a,int b) => 0;
                public static int FinallyInTryOut(int a,int b) => 0;
                public static int SharedRaise(int a,int b) => 0;
                public static int ThrowCaptured(int a,int b) { try { Add(a,b);return 0; } catch(System.Exception e) { throw e; } }
                public static int ThrowCapturedOut(int a,int b) => 0;
                public static int SharedUse(int a,int b) => 0;
                public static int SharedWrongThrow(int a,int b) => 0;
                public static int SharedFinallyOut(int a,int b) => 0;
                public static int SharedBranchOut(int a,int b) => 0;
                public static object ReadCaptured(int a,int b) { try { Add(a,b);return null; } catch(System.Exception e) { return e; } }
                public static int IncomingState(int a,int b) { int value=a; try { Add(a,b);value=b;Add(a,b);return 0; } catch { return value; } }
                public static int TypedFieldSplit(int a,int b) { try { Add(a,b);return 0; } catch(E e) { return e.Value; } }
                public static int TypedFieldSplitOut(int a,int b) => 0;
                public static int TypedField(int a,int b) { try { Add(a,b);return 0; } catch(E e) { return e.Value; } }
                public static int RethrowState(int a,int b) { int value=a; try { try { Add(a,b); } catch { value=b; throw; } Add(a,b); return 0; } catch { return value; } }
                public static int RethrowStateOut(int a,int b) => 0;
                public static int NestedTry(int a,int b) { try { Add(a,b); try { Add(a,b); } catch { return 2; } Add(a,b); return 0; } catch { return 1; } }
                public static int NestedTryOut(int a,int b) => 0;
                public static int NestedInCatch(int a,int b) { try { Add(a,b); } catch { try { Add(a,b); } catch { return 2; } return 1; } return 0; }
                public static int Disjoint(int a,int b) { try { Add(a,b); } catch { return 1; } try { Add(a,b); } catch { return 2; } return 0; }
                public static int NestedInCatchOut(int a,int b) => 0;
                public static int DisjointOut(int a,int b) => 0;
                public static object ReadCapturedOut(int a,int b) => null;
                public static int IncomingStateOut(int a,int b) => 0;
                public static int TypedFieldOut(int a,int b) => 0;
            }
            """);
        var defs = original.Types.Select(d => new TypeDef { Index = d.Index, Assembly = d.Assembly, Namespace = d.Namespace,
            Name = d.Name, Token = d.Token, Attributes = d.Attributes, IsValueType = d.IsValueType, IsEnum = false,
            PackingSize = 0, ClassSizeIsDefault = true }).ToList();
        TypeRef Type(string name) => new DefinitionRef(defs.Single(d => d.Name == name), []);
        defs.Single(d => d.Name == "Object").Size = 16;
        var ex = new TypeDef { Index = defs.Count, Assembly = "mscorlib.dll", Namespace = "System", Name = "Exception", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, PackingSize = 0, ClassSizeIsDefault = true,
            BaseType = Type("Object"), Size = 16 }; defs.Add(ex);
        var e = new TypeDef { Index = defs.Count, Assembly = "LoweringChecks.dll", Namespace = "", Name = "E", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, PackingSize = 0, ClassSizeIsDefault = true,
            BaseType = Type("Exception"), Size = 24 }; defs.Add(e);
        var field = new FieldDef { Index = 0, Owner = e, Name = "Value", Type = Type("Int32"), Attributes = FieldAttributes.Public, Offset = 16 };
        e.Fields = [field];
        var owner = defs.Single(d => d.Name == "Cases");
        var methods = new[] { "Add", "ReadCaptured", "IncomingState", "TypedField", "NestedInCatch", "Disjoint", "NestedTry", "TypedFieldSplit", "RethrowState", "SharedFinally", "SharedBranch", "SharedUse", "SharedWrongThrow", "SharedRaise", "ThrowCaptured", "CopiedFinally", "CopiedGuarded", "CopiedUnknownGuard", "CopiedMismatch", "CopiedEmpty", "CopiedSharedEntry", "SharedMulti", "SharedThrow", "FinallyInFinally", "FinallyInTry" }.Select((name, i) => new MethodDef {
            Index = i, Owner = owner, Name = name, Token = 0, Attributes = MethodAttributes.Public | MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1, ReturnType = Type(name == "ReadCaptured" ? "Object" : "Int32"),
            Parameters = [new("a", Type("Int32"), 0, null, false), new("b", Type("Int32"), 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var program = new ProgramModel { MetadataVersion = 0, Types = defs, Methods = methods, Fields = [field], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = defs.GroupBy(d => d.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1,0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var spec = InputCorpusChecks.Spec("arm64-v8a"); var layouts = new FieldLayouts(spec, 8, 8);
        var types = new ManagedTypes(program, layouts, 8); var binder = new MethodBinder(new(layouts), new Aapcs64());
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        foreach (var name in new[] { "ReadCaptured", "IncomingState", "TypedField", "NestedInCatch", "Disjoint", "NestedTry", "TypedFieldSplit", "RethrowState", "SharedFinally", "SharedBranch", "SharedUse", "SharedWrongThrow", "SharedRaise", "ThrowCaptured", "CopiedFinally", "CopiedGuarded", "CopiedUnknownGuard", "CopiedMismatch", "CopiedEmpty", "CopiedSharedEntry", "SharedMulti", "SharedThrow", "FinallyInFinally", "FinallyInTry" })
        {
            var t = new TermTable(); var entry = new BlockIdentity(); var second = new BlockIdentity(); var h = new BlockIdentity(); var body = new BlockIdentity();
            var frame = t.Atom(new RootAtom(AddressRoot.Frame), 64); var image = t.Atom(new RootAtom(AddressRoot.Image), 64);
            var f = new FunctionBuilder(t, entry, 64, new(frame)) { ImageBase = image };
            var slot = new AbstractSlot(SlotKind.Integer); var other = new AbstractSlot(SlotKind.Integer, 1);
            var a = t.Atom(new EntryAtom(slot), 64); var b = t.Atom(new EntryAtom(other), 64); f.Inputs.Add(new(slot,a)); f.Inputs.Add(new(other,b));
            var exception = t.Atom(new ExceptionAtom(h), 64); var selector = t.Atom(new SelectorAtom(h), 64);
            Call Runtime(string symbol, Term[] args, out Term result, bool noReturn = false)
            {
                var id = new CallIdentity(); result = t.Atom(new ResultAtom(id), 64);
                return new(id, new ImportedTarget(new(symbol)), args.Select((v,i) => new SlotValue(new(SlotKind.Integer,i),v)).ToImmutableArray(),
                    symbol == "__cxa_end_catch" || noReturn ? [] : [new(slot,result)], noReturn);
            }
            Call Protected() { var id = new CallIdentity(); return new(id,new ImageFunction(10),[new(slot,a),new(other,b),new(new(SlotKind.Integer,2),t.Constant(0,64))],
                [new(slot,t.Atom(new ResultAtom(id),64))],Unwind:h); }
            var first = Protected(); var next = Protected();
            f.Blocks.Add(new(entry,[],[first], name is "IncomingState" or "Disjoint" or "NestedTry" or "RethrowState" ? new Jump(second) : new Return([new(slot,t.Constant(0,name == "ReadCaptured" ? 64 : 32))])));
            if (name == "IncomingState") f.Blocks.Add(new(second,[],[next],new Return([new(slot,t.Constant(0,32))])));
            var mergeId = new MergeIdentity(); var merged = t.Atom(new ResultAtom(mergeId),32);
            f.Blocks.Add(new(h,name == "IncomingState" ? [new(mergeId,merged,[new(entry,t.Slice(a,0,32)),new(second,t.Slice(b,0,32))])] : [],[],new Jump(body),
                new(exception,selector,[new(ClauseKind.CatchAll,[])])));
            var begin = Runtime("__cxa_begin_catch",[exception],out var payload); var readId = new ReadIdentity(); var captured = t.Atom(new ResultAtom(readId),64);
            var read = new MemoryRead(readId,payload,64,captured); var end = Runtime("__cxa_end_catch",[],out _);
            var runtimeMap = new ExceptionRuntimeMap();
            var facts = NamingFacts.Empty;
            if (name.StartsWith("Shared", StringComparison.Ordinal) || name is "FinallyInFinally" or "FinallyInTry")
            {
                var cleanup = new BlockIdentity(); var test = new BlockIdentity(); var thrown = new BlockIdentity(); var continuation = new BlockIdentity();
                var savedId = new MergeIdentity(); var saved = t.Atom(new ResultAtom(savedId),64);
                f.Blocks[0] = f.Blocks[0] with { End = new Jump(cleanup) };
                f.Blocks.Add(new(body,[],[begin,read,end],new Jump(cleanup)));
                var clean = Protected() with { Arguments = [new(slot,b),new(other,a),new(new(SlotKind.Integer,2),t.Constant(0,64))], Unwind = null };
                var decision = new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual),1,saved,t.Constant(0,64)),thrown,continuation);
                var merge = new Merge(savedId,saved,[new(entry,t.Constant(0,64)),new(body,captured)]);
                if (name is "SharedBranch" or "SharedUse" or "SharedThrow")
                {
                    var action = new BlockIdentity();
                    var condition = name == "SharedUse" ? saved : t.Slice(name == "SharedThrow" ? b : a,0,32);
                    f.Blocks.Add(new(cleanup,[merge],[],new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual),1,condition,t.Constant(0,condition.Width)),action,test)));
                    f.Blocks.Add(new(action,[],[clean],new Jump(test)));
                    if (name == "SharedThrow")
                    {
                        var fail = new BlockIdentity(); var raiseId = new CallIdentity();
                        runtimeMap.Raise = catalog.Functions.Single(x=>x.Operation.Name=="ThrowManaged");
                        f.Blocks[^2] = f.Blocks[^2] with { End = new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual),1,t.Slice(b,0,32),t.Constant(0,32)),action,fail) };
                        f.Blocks.Add(new(fail,[],[new Call(raiseId,new ImageFunction(4),[new(slot,t.Constant(0,64)),new(other,t.Constant(0,64))],[],true)],new Unreachable()));
                    }
                    f.Blocks.Add(new(test,[],[],decision));
                }
                else f.Blocks.Add(new(cleanup,[merge],[clean],decision));
                var throwId = new CallIdentity();
                runtimeMap.Rethrow = catalog.Functions.Single(x => x.Operation.Name == "Rethrow");
                runtimeMap.Raise = catalog.Functions.Single(x=>x.Operation.Name=="ThrowManaged");
                f.Blocks.Add(new(thrown,[],[new Call(throwId,new ImageFunction(name == "SharedRaise" ? 4UL : 3UL),
                    name == "SharedRaise" ? [new(slot,saved),new(other,t.Constant(0,64))] : [new(slot,name == "SharedWrongThrow" ? a : saved)],[],true)],new Unreachable()));
                f.Blocks.Add(new(continuation,[],[],new Return([new(slot,t.Constant(7,32))])));
                if (name == "SharedMulti")
                {
                    var left = new BlockIdentity(); var right = new BlockIdentity(); var dispatch = new BlockIdentity(); var returnLeft = new BlockIdentity(); var returnRight = new BlockIdentity();
                    var selectorId = new MergeIdentity(); var selected = t.Atom(new ResultAtom(selectorId),32);
                    f.Blocks[0] = f.Blocks[0] with { End = new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual),1,t.Slice(a,0,32),t.Constant(0,32)),left,right) };
                    f.Blocks.Add(new(left,[],[],new Jump(cleanup))); f.Blocks.Add(new(right,[],[],new Jump(cleanup)));
                    var at = f.Blocks.FindIndex(block=>block.Identity==cleanup);
                    var savedMerge = merge with { Inputs = [new(left,t.Constant(0,64)),new(right,t.Constant(0,64)),new(body,captured)] };
                    f.Blocks[at] = f.Blocks[at] with { Merges = [savedMerge,new(selectorId,selected,[new(left,t.Constant(1,32)),new(right,t.Constant(2,32)),new(body,t.Undefined(32))])],
                        End = decision with { False = dispatch } };
                    f.Blocks.RemoveAll(block=>block.Identity==continuation);
                    f.Blocks.Add(new(dispatch,[],[],new Branch(t.Apply(new CoreOperator(CoreOperation.Equal),1,selected,t.Constant(1,32)),returnLeft,returnRight)));
                    f.Blocks.Add(new(returnLeft,[],[],new Return([new(slot,t.Constant(11,32))])));
                    f.Blocks.Add(new(returnRight,[],[],new Return([new(slot,t.Constant(22,32))])));
                }
                if (name is "FinallyInFinally" or "FinallyInTry")
                {
                    var innerHandler = new BlockIdentity(); var innerCapture = new BlockIdentity();
                    var innerException = t.Atom(new ExceptionAtom(innerHandler),64); var innerSelector = t.Atom(new SelectorAtom(innerHandler),64);
                    var at = f.Blocks.FindIndex(block=>block.Identity==cleanup);
                    var raised = f.Blocks.FindIndex(block=>block.Identity==thrown);
                    var after = f.Blocks.FindIndex(block=>block.Identity==continuation);
                    var innerBegin = Runtime("__cxa_begin_catch",[innerException],out var innerPayload);
                    f.Blocks.Add(new(innerHandler,[],[],new Jump(innerCapture),new(innerException,innerSelector,[new(ClauseKind.CatchAll,[])])));
                    if (name == "FinallyInTry")
                    {
                        f.Blocks[at] = f.Blocks[at] with { Statements = [clean with { Unwind = innerHandler }] };
                        f.Blocks[raised] = f.Blocks[raised] with { Statements = f.Blocks[raised].Statements.Select(statement=>statement is Call call ? (Statement)(call with { Unwind = innerHandler }) : statement).ToImmutableArray() };
                        f.Blocks[after] = f.Blocks[after] with { Statements = [Protected() with { Arguments = [new(slot,a),new(other,a),new(new(SlotKind.Integer,2),t.Constant(0,64))], Unwind = innerHandler }] };
                        f.Blocks.Add(new(innerCapture,[],[innerBegin,Runtime("__cxa_end_catch",[],out _)],new Return([new(slot,t.Constant(3,32))])));
                    }
                    else
                    {
                        var innerCleanup = new BlockIdentity(); var innerThrown = new BlockIdentity();
                        var innerSavedId = new MergeIdentity(); var innerSaved = t.Atom(new ResultAtom(innerSavedId),64);
                        var innerReadId = new ReadIdentity(); var innerCaught = t.Atom(new ResultAtom(innerReadId),64);
                        f.Blocks[at] = f.Blocks[at] with { Statements = [clean with { Unwind = innerHandler }], End = new Jump(innerCleanup) };
                        f.Blocks.Add(new(test,[],[],decision));
                        f.Blocks.Add(new(innerCapture,[],[innerBegin,new MemoryRead(innerReadId,innerPayload,64,innerCaught),Runtime("__cxa_end_catch",[],out _)],new Jump(innerCleanup)));
                        f.Blocks.Add(new(innerCleanup,[new(innerSavedId,innerSaved,[new(cleanup,t.Constant(0,64)),new(innerCapture,innerCaught)])],
                            [Protected() with { Arguments = [new(slot,a),new(other,a),new(new(SlotKind.Integer,2),t.Constant(0,64))], Unwind = null }],
                            new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual),1,innerSaved,t.Constant(0,64)),innerThrown,test)));
                        f.Blocks.Add(new(innerThrown,[],[new Call(new(),new ImageFunction(3),[new(slot,innerSaved)],[],true)],new Unreachable()));
                    }
                }
            }
            else if (name == "ThrowCaptured")
            {
                runtimeMap.Raise = catalog.Functions.Single(x=>x.Operation.Name=="ThrowManaged");
                f.Blocks.Add(new(body,[],[begin,read,end,new Call(new(),new ImageFunction(4),[new(slot,captured),new(other,t.Constant(0,64))],[],true)],new Unreachable()));
            }
            else if (name is "CopiedFinally" or "CopiedGuarded" or "CopiedUnknownGuard" or "CopiedMismatch" or "CopiedEmpty" or "CopiedSharedEntry")
            {
                var normal = new BlockIdentity();
                f.Blocks[0] = f.Blocks[0] with { End = new Jump(normal) };
                int methodInformation = 0;
                Call Clean(bool mismatch = false) => Protected() with { Arguments = [new(slot,mismatch ? a : b),new(other,a),new(new(SlotKind.Integer,2),t.Constant(++methodInformation,64))], Unwind = null };
                var cleanupStatements = new List<Statement> { begin,read,end };
                if (name != "CopiedEmpty") cleanupStatements.Add(Clean());
                cleanupStatements.Add(Runtime("__cxa_rethrow",[],out _,true));
                f.Blocks.Add(new(body,[],[..cleanupStatements],new Unreachable()));
                f.Blocks.Add(new(normal,[],name == "CopiedEmpty" ? [] : [Clean(name == "CopiedMismatch")],new Return([new(slot,t.Constant(7,32))])));
                if (name is "CopiedGuarded" or "CopiedUnknownGuard")
                {
                    var thrown = new BlockIdentity(); var swallowed = new BlockIdentity(); var normalAction = new BlockIdentity();
                    var at = f.Blocks.FindIndex(block=>block.Identity==body);
                    var guard = name == "CopiedGuarded" ? captured : t.Slice(a,0,32);
                    f.Blocks[at] = f.Blocks[at] with { Statements = f.Blocks[at].Statements.RemoveAt(f.Blocks[at].Statements.Length-1),
                        End = new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual),1,guard,t.Constant(0,guard.Width)),thrown,swallowed) };
                    f.Blocks.Add(new(thrown,[],[Runtime("__cxa_rethrow",[],out _,true)],new Unreachable()));
                    f.Blocks.Add(new(swallowed,[],[],new Return([new(slot,t.Constant(7,32))])));
                    f.Blocks.Add(new(normalAction,[],[Clean()],new Return([new(slot,t.Constant(7,32))])));
                    var normalAt = f.Blocks.FindIndex(block=>block.Identity==normal);
                    f.Blocks[normalAt] = f.Blocks[normalAt] with { Statements = [], End = new Jump(normalAction) };
                    if (name == "CopiedGuarded")
                    {
                        var join = new BlockIdentity(); var test = new BlockIdentity(); var valueId = new MergeIdentity(); var value = t.Atom(new ResultAtom(valueId),32);
                        var actionAt = f.Blocks.FindIndex(block=>block.Identity==normalAction);
                        var swallowedAt = f.Blocks.FindIndex(block=>block.Identity==swallowed);
                        f.Blocks[actionAt] = f.Blocks[actionAt] with { End = new Jump(join) };
                        f.Blocks[swallowedAt] = f.Blocks[swallowedAt] with { End = new Jump(join) };
                        f.Blocks[at] = f.Blocks[at] with { End = ((Branch)f.Blocks[at].End) with { True = test } };
                        f.Blocks.Add(new(test,[],[],new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual),1,captured,t.Constant(0,64)),thrown,join)));
                        f.Blocks.Add(new(join,[new(valueId,value,[new(normalAction,t.Constant(7,32)),new(swallowed,t.Constant(99,32)),new(test,t.Constant(98,32))])],[],new Return([new(slot,value)])));
                    }
                }
                if (name == "CopiedSharedEntry")
                {
                    var protectedEntry = new BlockIdentity();
                    f.Blocks[0] = f.Blocks[0] with { Statements = [], End = new Branch(t.Apply(new CoreOperator(CoreOperation.Equal),1,t.Slice(a,0,32),t.Constant(0,32)),normal,protectedEntry) };
                    f.Blocks.Add(new(protectedEntry,[],[first],new Jump(normal)));
                }
            }
            else if (name is "TypedField" or "TypedFieldSplit")
            {
                var accepted = new BlockIdentity(); var rejected = new BlockIdentity();
                var ti = new ReadIdentity(); var target = t.Atom(new ResultAtom(ti),64); var ci = new ReadIdentity(); var klass = t.Atom(new ResultAtom(ci),64);
                var testId = new CallIdentity(); var tested = t.Atom(new ResultAtom(testId),64);
                runtimeMap.TypeTest = catalog.Functions.Single(x => x.Operation.Name == "IsAssignableFrom");
                var test = new Call(testId,new ImageFunction(2),[new(slot,target),new(other,klass)],[new(slot,tested)]);
                var decision = new Branch(t.Apply(new CoreOperator(CoreOperation.NotEqual),1,t.Slice(tested,0,1),t.Constant(0,1)),accepted,rejected);
                var decisionBlock = new BlockIdentity();
                f.Blocks.Add(new(body,[],[begin,read,new MemoryRead(ti,image,64,target),new MemoryRead(ci,captured,64,klass),test],
                    name == "TypedFieldSplit" ? new Jump(decisionBlock) : decision));
                if (name == "TypedFieldSplit") f.Blocks.Add(new(decisionBlock,[],[],decision));
                var fieldId = new ReadIdentity(); var value = t.Atom(new ResultAtom(fieldId),32);
                f.Blocks.Add(new(accepted,[],[new MemoryRead(fieldId,t.Apply(new CoreOperator(CoreOperation.Add),64,captured,t.Constant(16,64)),32,value),end],new Return([new(slot,value)])));
                f.Blocks.Add(new(rejected,[],[Runtime("__cxa_rethrow",[],out _,true)],new Unreachable()));
                facts = facts with { Slots = facts.Slots.Add(0,Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new ClassEntity(Type("E")))) };
            }
            else if (name == "RethrowState")
            {
                var outer = new BlockIdentity(); var outerBody = new BlockIdentity();
                var outerException = t.Atom(new ExceptionAtom(outer),64); var outerSelector = t.Atom(new SelectorAtom(outer),64);
                var rethrow = Runtime("__cxa_rethrow",[],out _,true) with { Unwind = outer };
                f.Blocks.Add(new(body,[],[begin,read,rethrow],new Unreachable()));
                f.Blocks.Add(new(second,[],[next with { Unwind = outer }],new Return([new(slot,t.Constant(0,32))])));
                f.Blocks.Add(new(outer,[new(mergeId,merged,[new(second,t.Slice(a,0,32)),new(body,t.Slice(b,0,32))])],[],new Jump(outerBody),
                    new(outerException,outerSelector,[new(ClauseKind.CatchAll,[])])));
                f.Blocks.Add(new(outerBody,[],[Runtime("__cxa_begin_catch",[outerException],out _),Runtime("__cxa_end_catch",[],out _)],new Return([new(slot,merged)])));
            }
            else if (name is "NestedInCatch" or "Disjoint" or "NestedTry")
            {
                var inner = new BlockIdentity(); var innerBody = new BlockIdentity();
                var innerException = t.Atom(new ExceptionAtom(inner),64); var innerSelector = t.Atom(new SelectorAtom(inner),64);
                var innerBegin = Runtime("__cxa_begin_catch",[innerException],out _);
                if (name == "NestedInCatch") f.Blocks.Add(new(body,[],[begin,read,end],new Jump(second)));
                else f.Blocks.Add(new(body,[],[begin,read,end],new Return([new(slot,t.Constant(1,32))])));
                var third = new BlockIdentity();
                f.Blocks.Add(new(second,[],[next with { Unwind = inner }],name == "NestedTry" ? new Jump(third) : new Return([new(slot,t.Constant(name == "NestedInCatch" ? 1 : 0,32))])));
                if (name == "NestedTry") f.Blocks.Add(new(third,[],[Protected()],new Return([new(slot,t.Constant(0,32))])));
                f.Blocks.Add(new(inner,[],[],new Jump(innerBody),new(innerException,innerSelector,[new(ClauseKind.CatchAll,[])])));
                f.Blocks.Add(new(innerBody,[],[innerBegin,Runtime("__cxa_end_catch",[],out _)],new Return([new(slot,t.Constant(2,32))])));
            }
            else f.Blocks.Add(new(body,[],[begin,read,end],new Return([new(slot,name == "ReadCaptured" ? captured : merged)])));
            var calls = new CallNamingQuery(binder,new NamingChecks.Map([new(MethodRef.Open(methods[0]),BindingEntryKind.Ordinary)]),runtimeMap,catalog);
            var function = f.Freeze(); checks.True(ExitChecker.Check(function).IsValid,name + " 原生契约");
            if (name is "SharedUse" or "SharedWrongThrow" or "SharedRaise")
            {
                var state = new StateQueries(new ManagedCallEffects(calls));
                var naming = new ValueNamingQuery(state,calls,facts,spec,binder,binder.Definition(MethodRef.Open(methods.Single(m=>m.Name==name)),BindingEntryKind.Ordinary,null).Value,exceptionType:types.Object);
                var plan = naming.CreateContext(function).Get(new ExceptionRegionQuery(state,calls,naming,spec,types.Object,true),0);
                checks.True(plan.IsSuccess && plan.Value.Regions.SelectMany(r=>r.Clauses).All(clause=>clause.Finally is null),name + " 不接受不满足使用条件的共享清理");
                continue;
            }
            var result = new IntegerLowering(function,MethodRef.Open(methods.Single(m => m.Name == name)),binder,types,calls:calls,
                effects:new ManagedCallEffects(calls),spec:spec,names:facts).Run();
            checks.True(result.Body is not null,name + " 异常下降：" + result.Failure); if (result.Body is null) continue;
            var skeleton = new Skeleton(program,16); var problems = new BodyEmitter(skeleton,types).Emit([result.Body]);
            checks.True(problems.Count == 0,name + " 输出契约：" + string.Join(';',problems.Values)); if (problems.Count != 0) continue;
            if (name is "SharedFinally" or "SharedBranch" or "CopiedFinally" or "CopiedGuarded" or "SharedMulti" or "SharedThrow" or "CopiedEmpty")
                checks.True(result.Body.Regions is [{ Kind: ManagedRegionKind.Finally }] && result.Body.Blocks.SelectMany(b=>b.Statements).OfType<ManagedEndFault>().Count()==1,
                    name + " 输出真正 finally 和 endfinally");
            if (name == "ThrowCaptured") checks.True(result.Body.Blocks.SelectMany(block=>block.Statements).OfType<ManagedThrow>().Any()
                && !result.Body.Blocks.SelectMany(block=>block.Statements).OfType<ManagedRethrow>().Any(), "显式抛出捕获对象保留新的抛出事件");
            if (name is "FinallyInFinally" or "FinallyInTry") checks.True(result.Body.Regions.Count==2 && result.Body.Regions.Count(r=>r.Kind==ManagedRegionKind.Finally)==(name=="FinallyInFinally"?2:1),name + " 嵌套区域");
            if (name == "SharedMulti") checks.True(result.Body.Blocks.SelectMany(block=>block.Statements).OfType<ManagedJump>().Select(j=>j.Edge.Target).Distinct().Count()>=2, "常量分派还原多个正常续点");
            if (name is "CopiedMismatch" or "CopiedSharedEntry" or "CopiedUnknownGuard") checks.True(result.Body.Regions is [{ Kind: ManagedRegionKind.Catch }], "不等价的复制清理保留展开形式");
            if (name is "NestedInCatch" or "Disjoint" or "NestedTry") checks.True(result.Body.Regions.Count == 2, name + " 两个区域");
            if (name == "NestedTry") checks.True(result.Body.Regions[0].Try.Count < result.Body.Regions[1].Try.Count, "内层异常子句先于外层写出");
            if (name == "NestedInCatch")
            {
                var emitted = skeleton.Method(result.Body.Method.Method);
                checks.True(emitted.Body.ExceptionHandlers.All(parent => emitted.Body.ExceptionHandlers.All(child => child == parent
                    || child.TryStart != parent.HandlerStart)), "内层 try 从外层 catch 保存异常对象之后开始");
            }
            var testedMethod = source.Method("Cases", name + "Out");
            testedMethod.Body = skeleton.Method(result.Body.Method.Method).Body;
            var core = source.Module.TypeSystem.Object.Resolve().Module;
            Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => source.Module.ImportReference(
                source.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
            foreach (var local in testedMethod.Body.Variables) local.VariableType = MapType(local.VariableType);
            foreach (var clause in testedMethod.Body.ExceptionHandlers)
                if (clause.CatchType is not null) clause.CatchType = MapType(clause.CatchType);
            foreach (var instruction in testedMethod.Body.Instructions)
                instruction.Operand = instruction.Operand switch
                {
                    Mono.Cecil.MethodReference call => source.Module.ImportReference(source.Module.GetType(call.DeclaringType.FullName).Methods.Single(m => m.FullName == call.FullName)),
                    Mono.Cecil.FieldReference access => source.Module.ImportReference(source.Module.GetType(access.DeclaringType.FullName).Fields.Single(f => f.Name == access.Name)),
                    Mono.Cecil.TypeReference type => MapType(type),
                    Mono.Cecil.ParameterDefinition parameter => testedMethod.Parameters[parameter.Index],
                    _ => instruction.Operand,
                };
            var comparison = CilComparison.Compare(source.Method("Cases",name),testedMethod);
            checks.True(comparison.Status == CilComparisonStatus.Match,name + " 执行对照：" + comparison);
            if (name == "IncomingState") checks.True(result.Body.Blocks.Sum(block => block.Statements.Count(s => s is ManagedAssignment { ExceptionArrival: true })) == 4,
                "两条展开边在各自调用之前完成并行赋值");
        }
    }
}
