using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// IL2CPP 把判空、越界和数组存入的类型检查写成显式代码，恢复层只吸收机器层能证明的部分，其余写成 if (条件) throw。
    /// 写出的 C# 里实例访问、ldelem 和 stelem.ref 自己就做这些检查（ECMA-335 III.4）。检查成立时随后的访问必定抛同一异常，
    /// 中间又没有可观察的动作时，检查是多余的：删去后抛出的异常和时机不变，反编译器才能把局部内联回表达式。
    /// 多个检查都失败时抛哪个也要保持：判空之前只能隔着最多抛空引用的读取，其他检查之前不能隔着可能抛出的求值。
    /// </summary>
    private sealed class ImplicitChecks : IILTransform
    {
        private const int WalkBudget = 16;
        private const string NullReference = "System.NullReferenceException";
        private const string IndexOutOfRange = "System.IndexOutOfRangeException";
        private const string ArrayTypeMismatch = "System.ArrayTypeMismatchException";

        private enum First { Pure, Covered, Blocked }

        private readonly record struct Element(ILInstruction Array, ILInstruction Index);

        /// <summary>待删的检查由什么访问代替：经 NullOf 的访问、Bounds 的元素访问或把 Stored 存入数组。Proven 是已经查过下标、不会再抛出的元素。</summary>
        private sealed record Guard(ILVariable? NullOf = null, Element? Bounds = null, ILVariable? Stored = null, Element? Proven = null)
        {
            public bool Uses(ILVariable variable) =>
                variable == NullOf || variable == Stored || Mentions(Bounds, variable) || Mentions(Proven, variable);

            private static bool Mentions(Element? element, ILVariable variable) =>
                element is { } e && e.Array.Descendants.Concat(e.Index.Descendants).Any(i => i is LdLoc load && load.Variable == variable || i is LdLoca address && address.Variable == variable);
        }

        private readonly record struct Test(ILInstruction Condition, bool ThrowsWhen, Block Next, Block Thrower);

        public void Run(ILFunction function, ILTransformContext context)
        {
            var containers = function.Descendants.OfType<BlockContainer>().ToArray();
            void Each(Action<Block> action)
            {
                foreach (var container in containers)
                    foreach (var block in container.Blocks.ToArray())
                        if (block.Parent is not null) action(block);
            }
            // 类型检查在前：它们隔开了数组的判空和存入。
            Each(StoreCheck);
            Each(Collapse);
            Each(BoundsCheck);
            Each(NullCheck);
        }

        /// <summary>块只抛出给定的异常。这个阶段带初始值的局部还没有内联，异常对象可能先存进局部。</summary>
        private static bool Throws(Block block, string exception) => block.Instructions switch
        {
            [Throw { Argument: NewObj created }] => Creates(created, exception),
            [StLoc { Value: NewObj created } store, Throw { Argument: var thrown }] => thrown.MatchLdLoc(store.Variable) && Creates(created, exception),
            _ => false,
        };

        private static bool Creates(NewObj created, string exception) => created.Arguments.Count == 0 && created.Method.DeclaringType.FullName == exception;

        /// <summary>块尾的 if：一边抛给定的异常，另一边继续。</summary>
        private static Test? Terminator(Block block, string exception)
        {
            var count = block.Instructions.Count;
            if (count < 2 || block.Instructions[count - 2] is not IfInstruction { TrueInst: Branch taken } test || !test.FalseInst.MatchNop() || block.Instructions[count - 1] is not Branch other) return null;
            var (condition, when) = Unnegated(test.Condition);
            if (Throws(taken.TargetBlock, exception)) return new(condition, when, other.TargetBlock, taken.TargetBlock);
            return Throws(other.TargetBlock, exception) ? new(condition, !when, taken.TargetBlock, other.TargetBlock) : null;
        }

        /// <summary>恢复出的取反是 ceq、ldc.i4.0、ceq，这个阶段还没有化简。</summary>
        private static (ILInstruction Condition, bool When) Unnegated(ILInstruction condition)
        {
            var when = true;
            while (condition.MatchLogicNot(out var inner))
            {
                condition = inner;
                when = !when;
            }
            return (condition, when);
        }

        private static void Remove(Block block, Test test)
        {
            var count = block.Instructions.Count;
            var jump = new Branch(test.Next);
            jump.AddILRange(block.Instructions[count - 1]);
            block.Instructions.RemoveAt(count - 2);
            block.Instructions[count - 2] = jump;
            ClosureValues.RemoveIfOrphan(test.Thrower);
        }

        private static ILVariable? NullTested(Test test)
        {
            ILInstruction? tested = null;
            var matches = test.ThrowsWhen ? test.Condition.MatchCompEqualsNull(out tested) : test.Condition.MatchCompNotEqualsNull(out tested);
            return matches && tested!.MatchLdLoc(out var value) && value.Type.IsReferenceType == true ? value : null;
        }

        private static void NullCheck(Block block)
        {
            if (Terminator(block, NullReference) is { } test && NullTested(test) is { } value && Reached(test.Next, new Guard(NullOf: value), null)) Remove(block, test);
        }

        private static void BoundsCheck(Block block)
        {
            if (Terminator(block, IndexOutOfRange) is not { } test || OutOfBounds(test) is not { } element) return;
            var alongside = new List<(Block Block, Test Test)>();
            if (!Reached(test.Next, new Guard(Bounds: element), alongside)) return;
            Remove(block, test);
            foreach (var (other, check) in alongside) Remove(other, check);
        }

        /// <summary>isinst 的结果和空比较，抛出的那一边表示存入的值类型不符。这个异常只来自数组存入的检查。</summary>
        private static void StoreCheck(Block block)
        {
            if (Terminator(block, ArrayTypeMismatch) is not { } test) return;
            ILInstruction? tested = null;
            var matches = test.ThrowsWhen ? test.Condition.MatchCompEqualsNull(out tested) : test.Condition.MatchCompNotEqualsNull(out tested);
            if (!matches) return;
            // 判断结果可能先存进同一块里只读一次的局部。
            StLoc? saved = null;
            if (tested!.MatchLdLoc(out var result) && result.LoadCount == 1 && result.AddressCount == 0 && result.StoreInstructions is [StLoc { Value: IsInst, Parent: var parent } definition] && parent == block)
                (saved, tested) = (definition, definition.Value);
            if (tested is not IsInst { Argument: var argument } || !argument.MatchLdLoc(out var value) || !Reached(test.Next, new Guard(Stored: value), null)) return;
            Remove(block, test);
            if (saved is not null && saved.Variable.LoadCount == 0) block.Instructions.Remove(saved);
        }

        /// <summary>两边去同一个块的判断，条件没有副作用时只留跳转。</summary>
        private static void Collapse(Block block)
        {
            var count = block.Instructions.Count;
            if (count < 2 || block.Instructions[count - 2] is not IfInstruction { TrueInst: Branch taken } test || !test.FalseInst.MatchNop() || block.Instructions[count - 1] is not Branch other) return;
            var (first, second) = (taken.TargetBlock, other.TargetBlock);
            var target = Forwarded(second);
            if (Forwarded(first) != target || !Comparison(Unnegated(test.Condition).Condition)) return;
            var jump = new Branch(target);
            jump.AddILRange(other);
            block.Instructions.RemoveAt(count - 2);
            block.Instructions[count - 2] = jump;
            ClosureValues.RemoveIfOrphan(first);
            ClosureValues.RemoveIfOrphan(second);
        }

        private static Block Forwarded(Block block)
        {
            for (var budget = WalkBudget; budget > 0 && block.Instructions is [Branch next]; budget--) block = next.TargetBlock;
            return block;
        }

        private static bool Comparison(ILInstruction condition) => condition is Comp { Left: var left, Right: var right } && Operand(left) && Operand(right);

        private static bool Operand(ILInstruction value) => value is LdLoc or LdNull or LdcI4 or LdcI8 || value is IsInst { Argument: LdLoc };

        /// <summary>沿跳转向前走，判断第一个可观察的动作是不是 guard 要的访问。</summary>
        private static bool Reached(Block start, Guard guard, List<(Block Block, Test Test)>? alongside)
        {
            var block = start;
            for (var budget = WalkBudget; budget > 0; budget--)
            {
                var check = Terminator(block, NullReference) is { } test && NullTested(test) is not null ? test : (Test?)null;
                var end = block.Instructions.Count - (check is null ? 0 : 2);
                Block? following = null;
                for (var i = 0; i < end; i++)
                {
                    var instruction = block.Instructions[i];
                    if (instruction is Branch branch)
                    {
                        following = branch.TargetBlock;
                        break;
                    }
                    switch (Effect(instruction, guard))
                    {
                        case First.Covered: return true;
                        case First.Blocked: return false;
                    }
                }
                if (check is { } nullCheck)
                {
                    // 判空之前隔着另一处判空：都失败时抛的还是同一异常。
                    // 越界检查和存入之间隔着判空时，判空要能一起删去，抛出的次序才和原来相同。
                    if (guard.NullOf is null)
                    {
                        if (guard.Bounds is not { } bounds || alongside is null || !Reached(nullCheck.Next, new Guard(NullOf: NullTested(nullCheck), Proven: bounds), null)) return false;
                        alongside.Add((block, nullCheck));
                    }
                    following = nullCheck.Next;
                }
                if (following is null) return false;
                block = following;
            }
            return false;
        }

        /// <summary>按求值次序，这条指令第一个可观察的动作。</summary>
        private static First Effect(ILInstruction instruction, Guard guard)
        {
            switch (instruction)
            {
                case LdLoc or LdLoca or LdStr or LdcI4 or LdcI8 or LdcF4 or LdcF8 or LdNull or DefaultValue or LdTypeToken or Nop:
                    return First.Pure;
                case StLoc store:
                    return guard.Uses(store.Variable) ? First.Blocked : Effect(store.Value, guard);
                case Call or CallVirt:
                    return Invocation((CallInstruction)instruction, guard);
                case LdObj load:
                    return Access(load.Target, guard, null);
                case StObj write:
                    return Access(write.Target, guard, write.Value);
                case LdFlda or LdElema:
                    return Access(instruction, guard, null);
                case LdLen length:
                    if (guard.NullOf is { } tested && length.Array.MatchLdLoc(tested)) return First.Covered;
                    return guard.NullOf is null ? First.Blocked : Effect(length.Array, guard);
                case IfInstruction branch:
                    return Effect(branch.Condition, guard) == First.Covered ? First.Covered : First.Blocked;
                case Conv { CheckForOverflow: false } or Comp or IsInst or Box:
                    return Sequence(instruction.Children, guard);
                case BinaryNumericInstruction { CheckForOverflow: false, Operator: not (BinaryNumericOperator.Div or BinaryNumericOperator.Rem) }:
                    return Sequence(instruction.Children, guard);
                default:
                    return First.Blocked;
            }
        }

        private static First Sequence(IEnumerable<ILInstruction> instructions, Guard guard)
        {
            foreach (var instruction in instructions)
                if (Effect(instruction, guard) is var effect and not First.Pure) return effect;
            return First.Pure;
        }

        /// <summary>接收者和实参依次求值，判空在调用时才发生。可覆盖方法的非虚调用写出来可能不判空。</summary>
        private static First Invocation(CallInstruction call, Guard guard)
        {
            if (Sequence(call.Arguments, guard) is var arguments and not First.Pure) return arguments;
            var checksReceiver = call is CallVirt || !call.Method.IsVirtual;
            return guard.NullOf is { } value && !call.Method.IsStatic && !call.Method.IsConstructor && checksReceiver && call.Arguments[0].MatchLdLoc(value) ? First.Covered : First.Blocked;
        }

        private static First Access(ILInstruction target, Guard guard, ILInstruction? written)
        {
            switch (target)
            {
                case LdFlda { Target: var owner }:
                    if (guard.NullOf is { } value && owner.MatchLdLoc(value)) return Through(written, guard);
                    if (owner is LdFlda) return Access(owner, guard, written);
                    if (Effect(owner, guard) is var through and not First.Pure) return through;
                    if (written is not null) return First.Blocked;
                    // 读别的对象的字段最多抛空引用，只有判空才能隔着它。
                    return guard.NullOf is not null || owner.MatchLdThis() || owner is LdLoca ? First.Pure : First.Blocked;
                case LdElema { Array: var array, Indices: [var index] }:
                    if (Effect(index, guard) != First.Pure) return First.Blocked;
                    if (guard.NullOf is { } tested && array.MatchLdLoc(tested)) return Through(written, guard);
                    if (guard.Bounds is { } bounds && Same(array, bounds.Array) && Same(index, bounds.Index)) return Through(written, guard);
                    if (guard.Proven is { } proven && Same(array, proven.Array) && Same(index, proven.Index)) return written is null ? First.Pure : First.Blocked;
                    return guard.Stored is { } stored && written is not null && written.MatchLdLoc(stored) && FreshElement(array, index) ? First.Covered : First.Blocked;
                case LdLoca:
                    return written is null ? First.Pure : Effect(written, guard);
                default:
                    return First.Blocked;
            }
        }

        /// <summary>经 guard 要的位置访问：写入时先求值，值里更早的动作优先。</summary>
        private static First Through(ILInstruction? written, Guard guard)
        {
            if (written is null) return First.Covered;
            var effect = Effect(written, guard);
            return effect == First.Pure ? First.Covered : effect;
        }

        /// <summary>局部只赋值一次，是定长的新数组，下标是范围内的常量：这次存入不会越界，类型检查就是第一个可能失败的地方。</summary>
        private static bool FreshElement(ILInstruction array, ILInstruction index) =>
            array.MatchLdLoc(out var local) && local.AddressCount == 0 && local.StoreInstructions is [StLoc { Value: NewArr { Indices: [var length] } }]
            && Constant(Widened(length)) is { } size && Constant(Widened(index)) is { } at && at >= 0 && at < size;

        /// <summary>条件成立时给定的元素访问必定越界：下标不小于长度、等于长度，或长度等于常量下标。</summary>
        private static Element? OutOfBounds(Test test)
        {
            // 和 0 比较也是取反的形态，长度等于 0 到这里只剩长度本身。
            if (test.Condition is not Comp comparison) return !test.ThrowsWhen && Length(test.Condition) is { } empty ? new Element(empty, new LdcI4(0)) : null;
            var kind = test.ThrowsWhen ? comparison.Kind : Negated(comparison.Kind);
            var (left, right) = (comparison.Left, comparison.Right);
            var found = kind switch
            {
                ComparisonKind.GreaterThanOrEqual when Length(right) is { } array => new Element(array, Widened(left)),
                ComparisonKind.LessThanOrEqual when Length(left) is { } array => new Element(array, Widened(right)),
                ComparisonKind.Equality when Length(right) is { } array => new Element(array, Widened(left)),
                ComparisonKind.Equality when Length(left) is { } array => new Element(array, Widened(right)),
                _ => (Element?)null,
            };
            return found is { } element && Effect(element.Index, new Guard()) == First.Pure ? element : null;
        }

        private static ComparisonKind Negated(ComparisonKind kind) => kind switch
        {
            ComparisonKind.Equality => ComparisonKind.Inequality,
            ComparisonKind.Inequality => ComparisonKind.Equality,
            ComparisonKind.LessThan => ComparisonKind.GreaterThanOrEqual,
            ComparisonKind.LessThanOrEqual => ComparisonKind.GreaterThan,
            ComparisonKind.GreaterThan => ComparisonKind.LessThanOrEqual,
            ComparisonKind.GreaterThanOrEqual => ComparisonKind.LessThan,
            _ => kind,
        };

        /// <summary>数组长度的读取，或只赋值一次、存着长度的局部（数组也只赋值一次才不会过期）。</summary>
        private static ILInstruction? Length(ILInstruction value)
        {
            while (value is Conv { CheckForOverflow: false } conversion) value = conversion.Argument;
            if (value is LdLen length) return length.Array;
            if (!value.MatchLdLoc(out var local) || local.AddressCount != 0 || local.StoreInstructions is not [StLoc { Value: var stored }]) return null;
            while (stored is Conv { CheckForOverflow: false } conversion) stored = conversion.Argument;
            return stored is LdLen { Array: var array } && array.MatchLdLoc(out var source) && source.AddressCount == 0 && source.StoreInstructions.Count == 1 ? array : null;
        }

        /// <summary>扩展和同宽转换不改变下标是否越界：检查是 32 位的，访问时扩展成本机宽度。</summary>
        private static ILInstruction Widened(ILInstruction value)
        {
            while (value is Conv { CheckForOverflow: false, Kind: ConversionKind.Nop or ConversionKind.SignExtend or ConversionKind.ZeroExtend } conversion) value = conversion.Argument;
            return value;
        }

        private static long? Constant(ILInstruction value) => value.MatchLdcI4(out var small) ? small : value.MatchLdcI8(out var large) ? large : null;

        private static bool Same(ILInstruction a, ILInstruction b)
        {
            (a, b) = (Widened(a), Widened(b));
            if (a.MatchLdLoc(out var x)) return b.MatchLdLoc(out var y) && x == y;
            if (Constant(a) is { } constant) return Constant(b) == constant;
            if (a is BinaryNumericInstruction { CheckForOverflow: false } left && b is BinaryNumericInstruction { CheckForOverflow: false } right)
                return left.Operator == right.Operator && Same(left.Left, right.Left) && Same(left.Right, right.Right);
            return a is LdObj { Target: LdFlda { Field: var field, Target: var owner } } && b is LdObj { Target: LdFlda { Field: var other, Target: var otherOwner } }
                && field.MemberDefinition.Equals(other.MemberDefinition) && Same(owner, otherOwner);
        }
    }
}
