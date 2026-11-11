# 查询

一个 `QueryContext` 绑定一个不可变快照和只读全局事实；换快照就换上下文。同一上下文只允许一个调用者，不支持并发。查询实例按引用区分，键按自身相等语义区分，成功和失败都记忆。每个查询使用按键类型的表，正常路径不装箱键。`Outcome<T>` 是值类型，默认值表示 `query.uninitialized` 失败。

```csharp
sealed class Identity : Query<int, int>
{
    public override Outcome<int> Compute(QueryContext context, int key)
        => Outcome<int>.Success(key);
}
var result = new QueryContext(snapshot).Get(new Identity(), 42);
```

同步取依赖可用于辅助方法、lambda、LINQ 和循环。依赖失败由作者显式处理或传播：

```csharp
var dependency = context.Get(other, key);
if (!dependency.IsSuccess) return dependency.Propagate<int>();
return Outcome<int>.Success(dependency.Value + 1);
```

查询的构造参数 `stepBudget` 限制每次计算的依赖读取次数加显式报告步数。长循环调用 `context.Step(count)`，返回原因时应立即返回 `Outcome<T>.Failure(why)`；即使忽略预算失败，本次计算也不能发布成功。框架不能抢占不取依赖、不计步的作者代码。没有依赖和显式步骤的计算可在零预算下完成。

```csharp
var group = new FixedPointGroup(10_000,
    FixedPointMember.Create(reach, key => new ReachLattice(key)),
    FixedPointMember.Create(effect, key => new EffectLattice(key)));
var context = new QueryContext(snapshot, facts, group);
var result = context.Get(reach, start);
```

组声明查询与随键选择的格，不枚举键。首次访问从 `Bottom` 开始，按调用动态发现键；重入的环必须全部属于同一组，否则立即抛 `QueryCycleException`，包含环上地址。合法环读取当前近似值。组内最外层计算结束后，按键首次出现的次序重算，合并到当前近似值，整轮无变化才收敛；新键随时加入。参与者是环上的键及读取这些近似值的组内调用者；不受近似值影响的键不重复计算。未读近似值的成功计算可立即记忆；参与者在组完成前不发布。无环时不重复计算。

组预算同样按依赖读取与显式步骤计，包含嵌套求解的工作；达到预算后仍需工作就返回 `query.fixed-point-limit`。组内一个键的失败只属于这个键：它立即成为最终结果，读它的键自行处理或传播。失败是格的顶，作者要保证近似值变大时结果只会从成功变成失败，不会反过来，也不能因为近似值还小而报失败。只有上限耗尽才让本次尚未完成的键全部成为带原因的洞；此后途中算出的组外结果不记忆。近似值不进入记忆；组外请求只能获得收敛结果。经组外查询读取尚未完成的值属于未声明环；组外可独立求解同组的其他键。已收敛键可直接复用。

作者保证：查询纯且不观察线程身份；实例、键、事实、结果不可变；格满足偏序、最小值及最小上界公理，计算函数单调；有限高度格或其他终止依据。预算充足时最小不动点与请求顺序无关。框架检查合并是否为上界及已观察到的连续计算结果是否下降，不能证明任意函数的全部格公理或单调性。不要直接调用其他查询的 `Compute`，不要在查询外保存分析状态。

取未记忆的依赖前用运行时剩余栈检查；不足时启动具有 32 MiB 栈的新线程，原线程同步等待，计算返回后原线程继续。`StackSwitches` 可观测次数。作者无需改写同步函数，但不能依赖线程局部状态、跨依赖持有线程绑定的锁，或自行进行无界递归／大块 `stackalloc`。换栈不是并行求值；错误经异常派发信息原样传回，任何作者错误之后丢弃上下文。

默认只保留失败原因链；创建时设置 `RecordDependencies = true` 可用 `Explain` 查看去重的直接依赖。`Statistics` 按查询实例统计计算次数（含迭代）、命中次数（含近似读取）和最终记忆为失败的键数。诊断地址才装箱值类型键；命中路径默认零分配。
