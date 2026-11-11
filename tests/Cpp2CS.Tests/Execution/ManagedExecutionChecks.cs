namespace Cpp2CS.Tests.Execution;
internal static class ManagedExecutionChecks
{
    public const string Command = "cil-execution";
    public static int Run()
    {
        using var source = new CompiledSource("""
            public interface I { int Read(); }
            public class B : I { public int X; public virtual int Read() => X; }
            public class D : B { public override int Read() => X + 1; }
            public class N : B { public new virtual int Read() => 8; }
            public class O : N { public override int Read() => 9; }
            public class G { public virtual T Echo<T>(T x) => x; }
            public class H : G { public override T Echo<T>(T x) => x; }
            public struct Pair { public int X; public int Y; }
            public static class Cases {
                public static int Add(int x) => x + 7;
                public static int Same(int x) => 7 + x;
                public static int Different(int x) => x + 8;
                public static int Arithmetic() => unchecked(int.MaxValue + 1);
                public static int Overflow(int x) => checked(x + 1);
                public static int Loop(int x) { int s = 0; for(int i=0;i<(x & 7);i++) s += i; return s; }
                public static int Fields() { var b=new B(); b.X=9; var a=new int[2]; a[1]=b.X; return a[1]; }
                public static int Virtual() { B b=new D(); b.X=4; return b.Read(); }
                public static int Interface() { I b=new D(); return b.Read(); }
                public static int Box() { object x=17; return x is int ? (int)x : 0; }
                public static int Div(int x) => 12/x;
                public static int Null() { B b=null; return b.X; }
                public static int Bounds() => (new int[1])[2];
                public static int Finally() { int x=0; try { x=3; } finally { x+=5; } return x; }
                public static int CatchFinally() { int x=0; try { try { x=12/x; } finally { x=5; } } catch(System.DivideByZeroException) { x+=7; } return x; }
                public static int Struct() { Pair p=default; p.X=3; p.Y=8; Pair q=p; q.X++; return p.X+q.Y; }
                public static void Calls(System.Action a, System.Action b) { a(); b(); }
                public static void Swapped(System.Action a, System.Action b) { b(); a(); }
                public static int CallbackFinally(System.Action a) { int x=0; try { a(); } catch(System.Exception) { x=5; } finally { x+=3; } return x; }
                public static int NewSlot() { B b=new O(); b.X=4; return b.Read(); }
                public static int GenericVirtual() { G g=new H(); return g.Echo(23); }
                public static bool Reflection() { object x=new B(); return x.GetType().IsInstanceOfType(x); }
                public static int Text() => "abc".Length;
                public static void Heap(B b, System.Action a) { b.X=1; a(); b.X=0; }
                public static void HeapChanged(B b, System.Action a) { b.X=2; a(); b.X=0; }
                public static unsafe int Unsupported() { int* p=stackalloc int[2]; return *p; }
                public static int Forever() { while(true) {} }
            }
            """);
        var a = new Assertions();
        var model = new CecilModel(source.Module);
        var types = new Cpp2CS.Model.ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8);
        var index = new WorldIndex(model.Program, types);
        var interpreter = new CilInterpreter(model, index) { BodyModule = source.Module };
        CilSide Run(string name, params StackValue[] values)
        {
            var method = source.Method("Cases", name); var reference = model.Method(method);
            return interpreter.Run(new World(index, 0, new Hints([], []), reference.DeclaringType), method, reference, values);
        }
        foreach (var (name, expected) in new[] { ("Arithmetic", "80000000"), ("Fields", "9"), ("Virtual", "5"), ("Interface", "1"),
            ("NewSlot", "4"), ("GenericVirtual", "17"), ("Reflection", "1"), ("Text", "3"), ("Box", "11"), ("Finally", "8"), ("CatchFinally", "c"), ("Struct", "b") })
        {
            var side = Run(name);
            a.True(side.Result == $"return 0x{expected}", $"{name} 结果：{side.Result}");
        }
        var callback = source.Method("Cases", "CallbackFinally");
        var callbackRef = model.Method(callback);
        var callbackWorld = new World(index, 0, new Hints([], []), callbackRef.DeclaringType) { ThrowPlan = new(0, types.Corlib("System.InvalidOperationException")) };
        var callbackValue = callbackWorld.Object(callbackRef.Method.Parameters[0].Type, "callback", 0);
        var callbackSide = interpreter.Run(callbackWorld, callback, callbackRef, [StackValue.O(callbackValue)]);
        a.True(callbackSide.PlannedThrowReached && callbackSide.Result == "return 0x8" && callbackSide.Events.Any(e => e.Text.StartsWith("throw ", StringComparison.Ordinal)), "注入调用异常经过 catch/finally 且记录抛出事件");
        a.True(Run("Fields").Events.Count(e => e.Text.StartsWith("new ", StringComparison.Ordinal)) == 2, "字段与数组分配事件");
        a.True(Run("Loop", StackValue.I4(5)).Result == "return 0xa", "分支循环结果");
        foreach (var (name, exception, args) in new[] { ("Div", "DivideByZeroException", new[] { StackValue.I4(0) }),
            ("Null", "NullReferenceException", Array.Empty<StackValue>()), ("Bounds", "IndexOutOfRangeException", Array.Empty<StackValue>()),
            ("Overflow", "OverflowException", new[] { StackValue.I4(int.MaxValue) }) })
            a.True(Run(name, args).Events.Any(e => e.Text.Contains(exception, StringComparison.Ordinal)), $"{name} 异常事件");
        foreach (var (left, right, status) in new[] { ("CallbackFinally", "CallbackFinally", CilComparisonStatus.Match), ("Add", "Add", CilComparisonStatus.Match), ("Add", "Same", CilComparisonStatus.Match),
            ("Add", "Different", CilComparisonStatus.Mismatch), ("Calls", "Swapped", CilComparisonStatus.Mismatch), ("Heap", "HeapChanged", CilComparisonStatus.Mismatch), ("Unsupported", "Unsupported", CilComparisonStatus.Inconclusive), ("Forever", "Forever", CilComparisonStatus.Inconclusive) })
        {
            var result = CilComparison.Compare(source.Method("Cases", left), source.Method("Cases", right));
            a.True(result.Status == status && (status == CilComparisonStatus.Match || !string.IsNullOrEmpty(result.Reason)), $"{left}/{right}：{result}");
        }
        using var other = new CompiledSource("public static class Cross { public static int Add(int x) => x + 7; }");
        using var same = new CompiledSource("public static class Cross { public static int Add(int x) => 7 + x; }");
        using var changed = new CompiledSource("public static class Cross { public static int Add(int x) => x + 8; }");
        a.True(CilComparison.Compare(other.Method("Cross", "Add"), same.Method("Cross", "Add")).Status == CilComparisonStatus.Match, "跨程序集一致");
        a.True(CilComparison.Compare(other.Method("Cross", "Add"), changed.Method("Cross", "Add")).Status == CilComparisonStatus.Mismatch, "跨程序集常量变化");
        return a.Finish(Command);
    }
}
