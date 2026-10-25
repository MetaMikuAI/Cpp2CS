using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        // ---------- 注册：形态在自己的部分类文件里用属性声明分析、下降规则与证明，中心代码不再随形态改动 ----------

        /// <summary>分析步骤 <c>void M()</c>。按 After 拓扑排序，同时可运行的按 Order 从小到大。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class AnalysisAttribute(string name, int order) : Attribute
        {
            public string Name => name;
            public int Order => order;
            public string[] After { get; init; } = [];
        }

        /// <summary>语句级下降规则 <c>bool M(Block, Stmt, List&lt;ManagedStatement&gt;)</c>，在通用翻译之前尝试；返回 true 表示已处理。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class StatementRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>定义的下降规则 <c>bool M(Define, List&lt;ManagedStatement&gt;)</c>，在运行时引用、内联与对象类指针之后、普通赋值之前。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class DefineRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>存储的下降规则 <c>bool M(Store, List&lt;ManagedStatement&gt;)</c>，在解析写入位置之前。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class StoreRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>写入位置已解析后的存储规则 <c>bool M(Store, ManagedValue, List&lt;ManagedStatement&gt;)</c>。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class StoreTargetRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>调用的下降规则 <c>bool M(Call, List&lt;ManagedStatement&gt;)</c>，在删去的运行时操作与通用分派之前。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class CallRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>托管调用的下降规则 <c>bool M(Call, List&lt;ManagedStatement&gt;)</c>，在解析调用目标之前。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class InvocationRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>实参已恢复后的调用写出规则 <c>bool M(Call, AbiSignature, Dictionary&lt;Storage, Expr&gt;, ManagedInvocation, List&lt;ManagedStatement&gt;)</c>。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class InvocationOutputRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>按 ABI 传递的实参 <c>ManagedValue? M(AbiValue, ArgumentSite)</c>；返回 null 表示不归它处理。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class ArgumentRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>调用结果的局部 <c>LocalValue? M(Call, AbiValue)</c>；返回 null 表示不归它处理。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class ResultRuleAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>入口参数的绑定 <c>bool M(AbiValue, int)</c>；返回 true 表示已绑定。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class ParameterBindingAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>方法体证明 <c>void M(ManagedBody)</c>：方法体建成之后逐个检查，失败时登记洞。</summary>
        [AttributeUsage(AttributeTargets.Method)]
        private sealed class BodyProofAttribute(int order) : Attribute { public int Order => order; }

        /// <summary>实参规则看到的调用现场：<c>Argument</c> 取单个寄存器传递的实参（不是时登记洞）。</summary>
        private sealed record ArgumentSite(Call Call, MethodRef Callee, string Name, Dictionary<Storage, Expr> Registers, Func<AbiValue, string, Expr> Argument)
        {
            public int Index { get; init; }
        }

        private static class Registry
        {
            private const BindingFlags Members = BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;
            private static readonly MethodInfo[] Methods = typeof(Context).GetMethods(Members);

            public static readonly (string Name, Action<Context> Run)[] Analyses = OrderAnalyses();
            public static readonly Func<Context, Block, Stmt, List<ManagedStatement>, bool>[] Statements = Rules<StatementRuleAttribute, Func<Context, Block, Stmt, List<ManagedStatement>, bool>>(a => a.Order);
            public static readonly Func<Context, Define, List<ManagedStatement>, bool>[] Defines = Rules<DefineRuleAttribute, Func<Context, Define, List<ManagedStatement>, bool>>(a => a.Order);
            public static readonly Func<Context, Store, List<ManagedStatement>, bool>[] Stores = Rules<StoreRuleAttribute, Func<Context, Store, List<ManagedStatement>, bool>>(a => a.Order);
            public static readonly Func<Context, Store, ManagedValue, List<ManagedStatement>, bool>[] StoreTargets = Rules<StoreTargetRuleAttribute, Func<Context, Store, ManagedValue, List<ManagedStatement>, bool>>(a => a.Order);
            public static readonly Func<Context, Call, List<ManagedStatement>, bool>[] Calls = Rules<CallRuleAttribute, Func<Context, Call, List<ManagedStatement>, bool>>(a => a.Order);
            public static readonly Func<Context, Call, List<ManagedStatement>, bool>[] Invocations = Rules<InvocationRuleAttribute, Func<Context, Call, List<ManagedStatement>, bool>>(a => a.Order);
            public static readonly Func<Context, Call, AbiSignature, Dictionary<Storage, Expr>, ManagedInvocation, List<ManagedStatement>, bool>[] InvocationOutputs =
                Rules<InvocationOutputRuleAttribute, Func<Context, Call, AbiSignature, Dictionary<Storage, Expr>, ManagedInvocation, List<ManagedStatement>, bool>>(a => a.Order);
            public static readonly Func<Context, AbiValue, ArgumentSite, ManagedValue?>[] Arguments = Rules<ArgumentRuleAttribute, Func<Context, AbiValue, ArgumentSite, ManagedValue?>>(a => a.Order);
            public static readonly Func<Context, Call, AbiValue, LocalValue?>[] Results = Rules<ResultRuleAttribute, Func<Context, Call, AbiValue, LocalValue?>>(a => a.Order);
            public static readonly Func<Context, AbiValue, int, bool>[] Parameters = Rules<ParameterBindingAttribute, Func<Context, AbiValue, int, bool>>(a => a.Order);
            public static readonly Action<Context, ManagedBody>[] Proofs = Rules<BodyProofAttribute, Action<Context, ManagedBody>>(a => a.Order);

            private static TDelegate[] Rules<TAttribute, TDelegate>(Func<TAttribute, int> order) where TAttribute : Attribute where TDelegate : Delegate =>
                Methods.Select(m => (Method: m, Attribute: m.GetCustomAttribute<TAttribute>())).Where(p => p.Attribute is not null)
                    .OrderBy(p => order(p.Attribute!)).ThenBy(p => p.Method.Name, StringComparer.Ordinal)
                    .Select(p => p.Method.CreateDelegate<TDelegate>()).ToArray();

            /// <summary>拓扑排序：After 中的步骤必须已经运行；可运行的步骤中先运行 Order 最小的。缺少依赖或成环时启动即失败。</summary>
            private static (string, Action<Context>)[] OrderAnalyses()
            {
                var steps = Methods.Select(m => (Method: m, Attribute: m.GetCustomAttribute<AnalysisAttribute>())).Where(p => p.Attribute is not null)
                    .ToDictionary(p => p.Attribute!.Name, p => (p.Attribute!, Run: p.Method.CreateDelegate<Action<Context>>()));
                foreach (var (name, (attribute, _)) in steps)
                    foreach (var dependency in attribute.After)
                        if (!steps.ContainsKey(dependency)) throw new InvalidOperationException($"分析 {name} 依赖未注册的分析 {dependency}");
                var done = new HashSet<string>();
                var ordered = new List<(string, Action<Context>)>();
                while (ordered.Count < steps.Count)
                {
                    var next = steps.Where(p => !done.Contains(p.Key) && p.Value.Item1.After.All(done.Contains))
                        .OrderBy(p => p.Value.Item1.Order).ThenBy(p => p.Key, StringComparer.Ordinal).Select(p => p.Key).FirstOrDefault()
                        ?? throw new InvalidOperationException("分析的依赖成环：" + string.Join("、", steps.Keys.Where(k => !done.Contains(k))));
                    done.Add(next);
                    ordered.Add((next, steps[next].Run));
                }
                return ordered.ToArray();
            }
        }
    }
}
