using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// clang 把各分支共同的 InitializeArray 下沉到合流块，字段句柄放在局部里，而 C# 无法写出 ldtoken 字段。
    /// 把调用复制回写句柄的分支（语义不变），反编译器就能按字段数据还原成数组初始化器。
    /// </summary>
    private sealed class MergedArrayInitializers : IILTransform
    {
        public void Run(ILFunction function, ILTransformContext context)
        {
            foreach (var container in function.Descendants.OfType<BlockContainer>().ToArray())
            {
                foreach (var block in container.Blocks.ToArray())
                {
                    var count = block.Instructions.Count;
                    if (count < 2 || !block.Instructions[count - 2].MatchStLoc(out var handle, out var token) || token is not LdMemberToken { Member: IField }
                        || !block.Instructions[count - 1].MatchBranch(out var join) || join.Instructions.Count < 2
                        || join.Instructions[0] is not Call { Arguments.Count: 2 } call
                        || call.Method is not { Name: "InitializeArray", DeclaringType.FullName: "System.Runtime.CompilerServices.RuntimeHelpers" }
                        || !call.Arguments[0].MatchLdLoc(out _) || !call.Arguments[1].MatchLdLoc(handle)) continue;
                    if (join.Instructions.Count != 2 || !join.Instructions[1].MatchBranch(out var rest))
                    {
                        rest = new Block();
                        rest.AddILRange(join.Instructions[1]);
                        foreach (var moved in join.Instructions.Skip(1).ToArray()) rest.Instructions.Add(moved.Clone());
                        join.Instructions.RemoveRange(1, join.Instructions.Count - 1);
                        join.Instructions.Add(new Branch(rest));
                        container.Blocks.Add(rest);
                    }
                    var copy = (Call)call.Clone();
                    copy.Arguments[1] = token.Clone();
                    block.Instructions[count - 2] = copy;
                    block.Instructions[count - 1] = new Branch(rest);
                }
            }
        }
    }

    /// <summary>
    /// clang 把各分支等长的数组分配提到分支之前，分支里只剩 InitializeArray。从分配到 InitializeArray 的每条路径上都没有读过数组时，
    /// 它还没有别处引用，在 InitializeArray 前重新分配同样的数组语义不变，反编译器就能还原成数组初始化器。
    /// 读到原数组的路径之后不能再有 InitializeArray；没有路径读到原数组时去掉原分配。
    /// </summary>
    private sealed class HoistedArrayInitializers : IILTransform
    {
        public void Run(ILFunction function, ILTransformContext context)
        {
            foreach (var container in function.Descendants.OfType<BlockContainer>().ToArray())
                foreach (var block in container.Blocks.ToArray())
                    for (var i = 0; i < block.Instructions.Count; i++)
                        if (block.Instructions[i] is StLoc { Variable: { StoreCount: 1, AddressCount: 0 } array, Value: NewArr { Indices.Count: 1 } creation } allocation
                            && creation.Indices[0].MatchLdcI4(out _) && Reallocate(container, allocation, array, creation)) i--;
        }

        /// <summary>改写成功且去掉了原分配时返回 true。</summary>
        private static bool Reallocate(BlockContainer container, StLoc allocation, ILVariable array, NewArr creation)
        {
            var start = (Block)allocation.Parent!;
            var initializers = new List<ILInstruction>();
            var read = false;
            var visited = new HashSet<(Block, bool)>();
            var pending = new Stack<(Block Block, int Index, bool Read)>();
            pending.Push((start, allocation.ChildIndex + 1, false));
            while (pending.Count > 0)
            {
                var (block, index, escaped) = pending.Pop();
                for (; index < block.Instructions.Count; index++)
                {
                    var statement = block.Instructions[index];
                    if (statement == allocation) break;
                    if (statement is Call { Method: { Name: "InitializeArray", DeclaringType.FullName: "System.Runtime.CompilerServices.RuntimeHelpers" }, Arguments: [var target, LdMemberToken { Member: IField }] }
                        && target.MatchLdLoc(array))
                    {
                        if (escaped) return false;
                        if (!initializers.Contains(statement)) initializers.Add(statement);
                        break;
                    }
                    if (statement.Descendants.OfType<IInstructionWithVariableOperand>().Any(u => u.Variable == array)) read = escaped = true;
                    foreach (var branch in statement.Descendants.OfType<Branch>().Where(b => b.TargetContainer == container))
                        if (visited.Add((branch.TargetBlock, escaped))) pending.Push((branch.TargetBlock, 0, escaped));
                }
            }
            // 紧跟在分配之后的 InitializeArray 就是反编译器认识的形式。
            if (initializers.Count == 0 || initializers is [{ } only] && only.Parent == start && only.ChildIndex == allocation.ChildIndex + 1) return false;
            foreach (var initializer in initializers)
                ((Block)initializer.Parent!).Instructions.Insert(initializer.ChildIndex, new StLoc(array, creation.Clone()));
            if (read) return false;
            start.Instructions.RemoveAt(allocation.ChildIndex);
            return true;
        }
    }

    /// <summary>
    /// 表达式树留下的 GetMethodFromHandle(ldtoken 方法) 没有 C# 写法（反编译器写成 __ldtoken）。
    /// 改成按名称和形参类型的反射查找，得到同一个方法。
    /// </summary>
    private sealed class MemberTokens : IAstTransform
    {
        private const int AnyMember = 60; // BindingFlags.Instance | Static | Public | NonPublic

        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var token in rootNode.Descendants.OfType<InvocationExpression>().Where(i => i.Target is IdentifierExpression { Identifier: "__ldtoken" }).ToArray())
            {
                if (token.Annotation<LdMemberToken>()?.Member is not IMethod method
                    || token.Parent is not InvocationExpression { Target: MemberReferenceExpression { MemberName: "GetMethodFromHandle" } } lookup) continue;
                if (Reflection(method, context) is { } reflection) lookup.ReplaceWith(reflection);
            }
        }

        internal static Expression? Reflection(IMethod method, TransformContext context)
        {
            var builder = QualifiedTypes;
            var parameters = method.Parameters.Select(p => p.Type).ToArray();
            if (parameters.Any(p => p.Kind is ICSharpCode.Decompiler.TypeSystem.TypeKind.ByReference or ICSharpCode.Decompiler.TypeSystem.TypeKind.Pointer)) return null;
            if (method.TypeArguments.Count > 0)
            {
                // 泛型方法没有按实参查找的反射接口：静态方法经委托取得构造后的方法。
                if (!method.IsStatic) return null;
                var isAction = method.ReturnType.Kind == ICSharpCode.Decompiler.TypeSystem.TypeKind.Void;
                if (isAction && parameters.Length == 0) return null;
                var delegateType = (MemberType)GlobalType("System", isAction ? "Action" : "Func");
                foreach (var parameter in parameters) delegateType.TypeArguments.Add(builder.ConvertType(parameter));
                if (!isAction) delegateType.TypeArguments.Add(builder.ConvertType(method.ReturnType));
                var target = new MemberReferenceExpression(new TypeReferenceExpression(builder.ConvertType(method.DeclaringType)), method.Name);
                foreach (var argument in method.TypeArguments) target.TypeArguments.Add(builder.ConvertType(argument));
                return new MemberReferenceExpression(new ObjectCreateExpression(delegateType, target), "Method");
            }
            var types = new ArrayCreateExpression { Type = GlobalType("System", "Type"), Initializer = new ArrayInitializerExpression(parameters.Select(p => (Expression)new TypeOfExpression(builder.ConvertType(p)))) };
            types.AdditionalArraySpecifiers.Add(new ArraySpecifier());
            var flags = new CastExpression(GlobalType("System", "Reflection", "BindingFlags"), new PrimitiveExpression(AnyMember));
            var owner = new TypeOfExpression(builder.ConvertType(method.DeclaringType));
            return method.IsConstructor
                ? new InvocationExpression(new MemberReferenceExpression(owner, "GetConstructor"), flags, new NullReferenceExpression(), types, new NullReferenceExpression())
                : new InvocationExpression(new MemberReferenceExpression(owner, "GetMethod"), new PrimitiveExpression(method.Name), flags, new NullReferenceExpression(), types, new NullReferenceExpression());
        }
    }

    /// <summary>
    /// 反编译器把 x?.M(a) 的扩展方法写回静态调用时留下 Enumerable.M(x?, a)，不是合法语法。还原成 x?.M(a)。
    /// </summary>
    private sealed class NullConditionalReceivers : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var call in rootNode.Descendants.OfType<InvocationExpression>().ToArray())
            {
                if (call.Arguments.FirstOrDefault() is not UnaryOperatorExpression { Operator: UnaryOperatorType.NullConditional } first
                    || call.Target is not MemberReferenceExpression { Target: TypeReferenceExpression } target) continue;
                var member = new MemberReferenceExpression(first.Clone(), target.MemberName);
                foreach (var argument in target.TypeArguments) member.TypeArguments.Add(argument.Clone());
                call.ReplaceWith(new InvocationExpression(member, call.Arguments.Skip(1).Select(a => a.Clone())));
            }
        }
    }
}
