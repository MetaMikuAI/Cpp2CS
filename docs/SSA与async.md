# SSA 与 async

机器 SSA 按独立身份表示值和前驱输入，保留循环回边。普通返回与异常入口使用独立状态；托管语义层传播类型、位宽、聚合切片和存储位置。

接口分派检查表布局、查找循环、类型相等分支、慢路径 helper、接收者、槽号及 MethodInfo。共享函数体签名复用要求完整指令、跳转相对位置、异常区域和 personality 槽一致。

async 协议检查 source/token 共同来源、前驱配对、awaiter 保存与清空、状态写入、调度参数及异常出口。原始方法身份由 AsyncStateMachineAttribute 关联，参数来源由入口对状态机的写入确定。

SetResult 与 SetException 的异常按实际保护区传播，不能自动归入 builder 的捕获路径。C++ RTTI、托管异常类型检查、cleanup 和 catch-all 分开表示。

原生布局与运行时读取存在差异时，覆盖值必须由匹配二进制哈希的运行时摘要提供。
