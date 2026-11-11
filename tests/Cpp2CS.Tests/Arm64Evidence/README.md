# ARM64 单指令证据

`generate.py` 按 A64 编码模板生成指令，先用 Capstone 检查助记符，再用 Unicorn 执行一条指令。固定随机种子；每条记录包含 31 个通用寄存器、SP、32 个完整向量寄存器和 NZCV 的前后状态，以及内存读写、下一条指令地址和陷阱结果。输入包含零、全一、正负边界、移位边界和全部 NZCV 组合。浮点输入另含正负零、无穷、静默与信号 NaN、次正规数、取整平局和整数转换越界；向量搬运检查完整 128 位单元。

在仓库外创建 Python 虚拟环境，安装 `requirements.txt`，运行：

```sh
python tests/Cpp2CS.Tests/Arm64Evidence/generate.py
```

输出 `evidence.json.gz`。文件记录生成器 SHA-256、Capstone、Unicorn、Python 与 zlib 的版本；gzip 时间戳固定为零。同一环境重复生成应逐字节一致。可传入另一个输出文件名进行比较。

`arm64` 检查使用具体取值发射器执行产品语义，逐项比较完整寄存器、NZCV、控制流与内存效果。128 位访存在 Unicorn 的钩子中可能分成两个 64 位访问，比较端按保持次序的字节序列核对。所有读取必须消费完，所有写入必须完全一致；不做存储转发。浮点运算结果按核心契约将所有 NaN 视为相同，只比较生成器声明的结果车道；其他位仍逐位核对。位型搬运、取负、绝对值不使用 NaN 等价。非默认寄存器的 RET 发射间接跳转，在单步检查中比较目标，在函数提升中交给保守解析器报洞。

`arm64-corpus` 从 `CPP2CS_CORPUS` 与 `CPP2CS_CORPUS_TRUTH` 读取映像与真值。逐函数提升两次，比较包括洞地址在内的完整汇总，并核对成功产物的出口。不设置这两个环境变量时明确跳过。可设置 `CPP2CS_ARM64_HISTOGRAM` 输出仅包含类别、指令字及次数的 JSON，再运行：

```sh
python tests/Cpp2CS.Tests/Arm64Evidence/histogram.py "$CPP2CS_ARM64_HISTOGRAM"
```

指令数按映像给出的函数范围逐个计数，函数范围重叠时重复计入。耗时只包含提升与出口复核，不含载入、独立编码普查或助记符统计。仅含单一编码缺口的函数数量是后续工作的上界，补齐指令后仍可能遇到间接跳转、栈恢复或异常边的缺口。

边界：取证是有限的随机与边界样本，不能替代完整架构证明。其余向量运算、半精度、固定小数点转换、平局远离零取整、原子与独占访问、屏障、系统寄存器和异常边不在本检查的语义覆盖内。指针认证提示按任务规定当作空操作；本证据不验证启用指针认证后的认证效果。

## 浮点与向量语义

生成代码假设 FPCR 为默认值：就近取偶、保留次正规数、异常不触发陷阱。不建模 FPCR/FPSR；读写这些寄存器的指令按系统寄存器报洞。`FRINTI/FRINTX` 按这一默认舍入模式执行，不输出异常标志。

依据为 [Arm《Instruction Set Reference Guide》](https://documentation-service.arm.com/static/6245c734b059dc5ff9a8bdab)的 A64 浮点和 Advanced SIMD 指令定义，以及独立模拟器的单步结果。`FMINNM/FMAXNM` 对信号 NaN 显式传播 NaN；核心 `minimumNumber/maximumNumber` 单独处理静默 NaN 的数值选择。浮点转整数先取整，再用二次幂边界显式选择饱和值，NaN 返回零，未选中的核心越界转换不求值。

支持单/双精度标量搬运、立即数、算术、融合乘加减、比较、条件比较与选择、格式转换、整数转换、四种取整及最小最大。平局远离零的 `FRINTA/FCVTAS/FCVTAU` 缺少直接对应的核心运算，保留浮点洞。向量支持 ORR/MOV、修改立即数、DUP、INS、UMOV/SMOV、XTN、SSHLL/USHLL 及单/双精度 FCVTL/FCVTN；其他编码保留向量洞。
