# 调用参数与接口 ABI

原生 SSA 调用节点保存调用前 SP、寄存器和内存。`AbiArgument` 按 AAPCS64 布局读取寄存器或 SP 相对栈参数，并将多个片段组合为逻辑参数。

接口槽的托管签名与字段布局共同确定 ABI。隐藏 MethodInfo 的位置由 ABI 分类决定，且必须与目标函数来自同一 VirtualInvokeData。返回值也使用该 ABI 分类，区分整数、浮点、聚合和间接返回。

签名缓存以完整类型、方法、参数和返回类型为键。未知类型、缺少栈来源或 MethodInfo 不匹配均保留为未解析。

async 诊断保留具体运行时操作及业务异常区域；普通表达式前端的限制存放在 `LegacyProblems` 中。
