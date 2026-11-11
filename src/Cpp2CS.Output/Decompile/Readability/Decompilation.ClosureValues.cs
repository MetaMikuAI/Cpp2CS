using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// 闭包对象由编译器用 newobj 创建，外层闭包的引用（CS$&lt;&gt;8__locals）只在创建时写一次，所以闭包值不为空，同一个引用字段总读到同一个对象。
    /// IL2CPP 在访问前留下判空，clang 又把各路径上对引用字段的读取合并到一个局部。反编译器不认识这两种用法，就放弃折叠整个方法的闭包。
    /// 这里删去闭包值的判空，把这类局部换回字段读取，把闭包的局部副本换回原局部；被删的分支不可达，换回前后读到的是同一个对象。
    /// 捕获的局部全被优化掉时，闭包创建后没有读者，构造函数是编译器生成的空方法，创建也一并删去。
    /// 状态机的 MoveNext 由反编译器单独读取，提升之后才能看到它的局部，所以这个变换在提升前后各运行一次。
    /// </summary>
    private sealed class ClosureValues : IILTransform
    {
        public void Run(ILFunction function, ILTransformContext context)
        {
            foreach (var container in function.Descendants.OfType<BlockContainer>().ToArray())
                foreach (var block in container.Blocks.ToArray())
                    NullCheck(block, context.TypeSystem);
            MergedReads(function);
            Copies(function);
            UnusedClosures(function);
        }

        /// <summary>局部函数的结构体闭包按值复制、经 ref 传递，这里的推理都不成立。</summary>
        private static bool IsClosure(IType type) => type.IsReferenceType == true && type.GetDefinition()?.Name.StartsWith("<>c__DisplayClass", StringComparison.Ordinal) == true;

        /// <summary>块尾的 if (闭包 == null) 跳到抛空引用的块，或 if (闭包 != null) 跳走、否则抛空引用：只留不抛的那条边。</summary>
        private static void NullCheck(Block block, ICompilation compilation)
        {
            var count = block.Instructions.Count;
            if (count < 2 || block.Instructions[count - 2] is not IfInstruction { TrueInst: Branch taken } test || !test.FalseInst.MatchNop()) return;
            var isNull = test.Condition.MatchCompEqualsNull(out var value);
            if (!isNull && !test.Condition.MatchCompNotEqualsNull(out value)) return;
            if (!IsClosure(value!.InferType(compilation))) return;
            if (isNull)
            {
                // 不抛的路径可能是 br，也可能是 leave，留着。
                if (ThrowsNullReference(taken.TargetBlock))
                {
                    var thrower = taken.TargetBlock;
                    block.Instructions.RemoveAt(count - 2);
                    RemoveIfOrphan(thrower);
                }
                return;
            }
            if (block.Instructions[count - 1] is not Branch other || !ThrowsNullReference(other.TargetBlock)) return;
            var jump = new Branch(taken.TargetBlock);
            jump.AddILRange(other);
            var unreached = other.TargetBlock;
            block.Instructions.RemoveAt(count - 2);
            block.Instructions[count - 2] = jump;
            RemoveIfOrphan(unreached);
        }

        /// <summary>抛异常的块没有入口后留着会排在方法末尾，写出来是死语句，方法尾部还要多一个 return。</summary>
        internal static void RemoveIfOrphan(Block block)
        {
            if (block.IncomingEdgeCount == 0 && block.Parent is BlockContainer container) container.Blocks.Remove(block);
        }

        internal static bool ThrowsNullReference(Block block) =>
            block.Instructions is [Throw { Argument: NewObj { Method.DeclaringType.FullName: "System.NullReferenceException", Arguments.Count: 0 } }];

        /// <summary>闭包类型的局部，每次赋值都读 this 的同一个字段或同一个只赋值一次的闭包局部：读局部换成读来源，赋值去掉。</summary>
        private static void MergedReads(ILFunction function)
        {
            foreach (var variable in function.Variables.ToArray())
            {
                if (variable.Kind == VariableKind.Parameter || variable.StoreCount < 2 || variable.AddressCount != 0 || !IsClosure(variable.Type)) continue;
                var stores = variable.StoreInstructions.OfType<StLoc>().ToArray();
                if (stores.Length != variable.StoreCount || stores.Any(s => s.Parent is not Block || !StableSource(s.Value, variable, function))) continue;
                var read = stores[0].Value;
                if (stores.Any(s => !s.Value.Match(read).Success)) continue;
                foreach (var load in variable.LoadInstructions.ToArray()) load.ReplaceWith(read.Clone());
                foreach (var store in stores) ((Block)store.Parent!).Instructions.Remove(store);
            }
        }

        /// <summary>来源是只赋值一次的闭包局部，或这个函数不写的 this 字段（循环里的闭包每轮重建，字段会变）。</summary>
        private static bool StableSource(ILInstruction value, ILVariable variable, ILFunction function)
        {
            if (value.MatchLdLoc(out var source)) return source != variable && source.StoreInstructions.Count == 1 && source.StoreCount == 1 && source.AddressCount == 0 && IsClosure(source.Type);
            if (!value.MatchLdFld(out var target, out var field) || !target.MatchLdThis()) return false;
            return !function.Descendants.OfType<LdFlda>().Any(address => address.Parent is not LdObj && address.Field.MemberDefinition.Equals(field.MemberDefinition));
        }

        /// <summary>只赋值一次的闭包局部，值是另一个只赋值一次的闭包局部：读副本换成读原局部。</summary>
        private static void Copies(ILFunction function)
        {
            foreach (var copy in function.Variables.ToArray())
            {
                if (copy.Kind == VariableKind.Parameter || copy.StoreCount != 1 || copy.AddressCount != 0 || !IsClosure(copy.Type)) continue;
                if (copy.StoreInstructions is not [StLoc { Parent: Block block } store] || !store.Value.MatchLdLoc(out var source)) continue;
                if (source == copy || source.StoreInstructions.Count != 1 || source.StoreCount != 1 || source.AddressCount != 0 || !IsClosure(source.Type)) continue;
                foreach (var load in copy.LoadInstructions.ToArray()) load.ReplaceWith(new LdLoc(source));
                block.Instructions.Remove(store);
            }
        }

        private static void UnusedClosures(ILFunction function)
        {
            foreach (var variable in function.Variables.ToArray())
            {
                if (variable.Kind == VariableKind.Parameter || variable.LoadCount != 0 || variable.AddressCount != 0 || variable.StoreCount != 1 || !IsClosure(variable.Type)) continue;
                if (variable.StoreInstructions is [StLoc { Parent: Block block, Value: NewObj { Arguments.Count: 0 } } store]) block.Instructions.Remove(store);
            }
        }

    }
}
