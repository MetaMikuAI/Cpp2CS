using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceIteratorDisposeCheck
{
    [Command("source-iterator-dispose", "迭代器有界状态位掩码的精确分派与拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var owner = new TypeDef { Index = 0, Assembly = "Sample", Namespace = "Tests", Name = "Iterator", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var type = new DefinitionRef(owner, []);
        var integer = new PrimitiveRef("I4");
        var boolean = new PrimitiveRef("Boolean");
        var self = new ArgumentValue(-1, type, 64);
        MethodRef Method(string name) => new(new MethodDef { Index = 0, Owner = owner, Name = name, Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = new PrimitiveRef("void") }, [], []);
        var field = new FieldValue(self, new(new FieldDef { Index = 0, Owner = owner, Name = "<>1__state", Type = integer,
            Attributes = FieldAttributes.Private, Offset = 16 }, type), integer, 32);
        var shifted = new LocalValue(new(Storage.Gpr(8), 1), integer, 32);
        ConstantValue C(uint value) => new(value, integer, 32);
        var assign = new ManagedAssignment(0, shifted, new BinaryValue(BinOp.Add, field, C(9), integer, 32));
        var guard = new ManagedBranch(0, new ComparisonValue(Cond.Ugt, shifted, C(6), boolean), new(3, []), new(1, []));
        var bits = new BinaryValue(BinOp.And, new BinaryValue(BinOp.Shl, C(1), shifted, integer, 32), C(0x45), integer, 32);
        var select = new ManagedBranch(1, new ComparisonValue(Cond.Eq, bits, C(0), boolean), new(3, []), new(2, []));
        var cleanup = new ManagedCall(2, new(Method("<>m__Finally1"), self, [], false), null, true);
        var original = new ManagedBody(Method("System.IDisposable.Dispose"),
            [new(0, [assign, guard]), new(1, [select]), new(2, [cleanup]), new(3, [new ManagedReturn(3, null)])]);
        int Run(ManagedBody body, uint state)
        {
            var locals = new Dictionary<Variable, uint>();
            Expr Value(ManagedValue v) => v switch
            {
                FieldValue f when f == field => Expr.C(state, 32),
                LocalValue l => Expr.C(locals[l.Variable], 32),
                ConstantValue c => Expr.C(c.Bits, c.Width),
                BinaryValue b => new Binary(b.Op, Value(b.Left), Value(b.Right), b.Width),
                ComparisonValue c => new Compare(c.Condition, Value(c.Left), Value(c.Right)),
                _ => throw new NotSupportedException(v.ToString()),
            };
            uint Eval(ManagedValue value)
            {
                var evaluator = new Evaluator();
                var result = (uint)evaluator.Eval(Value(value));
                if (evaluator.Failure is not null) throw new InvalidOperationException(evaluator.Failure);
                return result;
            }
            var blocks = body.Blocks.ToDictionary(b => b.Address);
            var current = body.Blocks[0].Address;
            var count = 0;
            for (var steps = 0; steps < 64; steps++)
                foreach (var statement in blocks[current].Statements)
                    switch (statement)
                    {
                        case ManagedAssignment assignment: locals[assignment.Target.Variable] = Eval(assignment.Value); break;
                        case ManagedBranch branch: current = Eval(branch.Condition) != 0 ? branch.Taken.Target : branch.Fallthrough.Target; break;
                        case ManagedSwitch selection: current = selection.Cases[(int)Eval(selection.Index)].Target; break;
                        case ManagedCall call: count++; if (call.Tail) return count; break;
                        case ManagedReturn: return count;
                        default: throw new NotSupportedException(statement.ToString());
                    }
            throw new InvalidOperationException("状态分派未终止");
        }
        var rewritten = SourceIteratorDispose.Rewrite(original);
        a.True(!ReferenceEquals(original, rewritten) && !rewritten.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of)
            .SelectMany(ManagedValues.Walk).OfType<BinaryValue>().Any(v => v.Op == BinOp.Shl), "范围内位掩码转成等值分派");
        foreach (var state in Enumerable.Range(-40, 100).Select(i => unchecked((uint)i)).Concat(new uint[] { int.MaxValue, 0x80000000, uint.MaxValue - 8 }))
        {
            var expected = state is unchecked((uint)-9) or unchecked((uint)-7) or unchecked((uint)-3) ? 1 : 0;
            a.Equal(expected, Run(original, state), "原分派的有界状态集合");
            a.Equal(expected, Run(rewritten, state), "改写后的状态、溢出边界与清理次数一致");
        }
        var unguarded = original with { Blocks = [new(0, [assign, select]), .. original.Blocks.Skip(2)] };
        a.Equal(unguarded, SourceIteratorDispose.Rewrite(unguarded), "未受范围保护的周期位掩码不能枚举");
        var changed = original with { Blocks = [.. original.Blocks.Take(2), new(2, [cleanup with { Tail = false }, guard]), original.Blocks[3]] };
        a.Equal(changed, SourceIteratorDispose.Rewrite(changed), "调用可能修改状态，不能用旧值解释后续分派");
        var copied = original with { Blocks = [new(0, [assign, guard with { Fallthrough = new(1, [new(shifted, C(0))]) }]), .. original.Blocks.Skip(1)] };
        a.Equal(copied, SourceIteratorDispose.Rewrite(copied), "带边赋值时保持原图");
        var mutated = original with { Blocks = [new(0, [assign, new ManagedStore(0, field, C(0)), guard]), .. original.Blocks.Skip(1)] };
        a.Equal(mutated, SourceIteratorDispose.Rewrite(mutated), "分派中的状态写入不能丢弃");
        var table = original with { Blocks = [original.Blocks[0], new(1, [new ManagedSwitch(1, shifted,
            [new(2, []), new(3, []), new(2, []), new(3, []), new(3, []), new(3, []), new(2, [])])]), .. original.Blocks.Skip(2)] };
        var tableResult = SourceIteratorDispose.Rewrite(table);
        a.True(!tableResult.Blocks.SelectMany(b => b.Statements).OfType<ManagedSwitch>().Any(), "已有范围守卫的跳转表归并为状态分派");
        foreach (var state in Enumerable.Range(-40, 100).Select(i => unchecked((uint)i)).Append(uint.MaxValue))
            a.Equal(Run(table, state), Run(tableResult, state), "跳转表与改写分派的清理次数一致");
        var unbounded = table with { Blocks = [new(0, [assign, new ManagedJump(0, new(1, []))]), .. table.Blocks.Skip(1)] };
        a.Equal(unbounded, SourceIteratorDispose.Rewrite(unbounded), "没有范围守卫的 switch 不改写");
        return a.Finish("source-iterator-dispose");
    }
}
