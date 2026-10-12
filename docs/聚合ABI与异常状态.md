# 聚合 ABI 与异常状态

参数与返回值按 ABI 分配到寄存器或栈的字节片段。托管值类型实例接收者使用未装箱地址。

值切片与拼接同时保留位值和表达式。源指针、token 与尾部字节具有各自范围，部分覆盖不合并为完整原值。向量寄存器别名和调用破坏按寄存器宽度处理。

LSDA 区分 typed catch、cleanup、catch-all 和相对动作链。C++ RTTI 与托管 TypeInfo 分开解析，未知重定位报错。

指令级控制流保留普通出口、异常出口和循环。不返回调用仍可具有异常边；缺少 LSDA call-site 与没有本地处理器分别表示。异常寄存器状态中的 X0 是 unwind 对象，X1 是 selector，不沿用普通返回值。

格式定义参见 [LLVM personality 实现](https://raw.githubusercontent.com/llvm/llvm-project/main/libcxxabi/src/cxa_personality.cpp) 和 [Itanium 异常 ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi-eh.html)。
