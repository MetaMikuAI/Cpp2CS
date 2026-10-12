# 多 await 与 UniTask 布局

`AwaitSite` 使用调度调用身份区分挂起点，同一 awaiter 字段可以用于多个状态。builder 与 awaitable 分开识别。

状态写入沿正常控制流反向查询。入口未写入、部分覆盖、未知调用或不明别名阻止完整保存证明。本地 awaiter 必须与到达调度点的保存值一致；状态、字段与生产者分别记录。

`StatusCandidates` 和 `ResultCandidates` 表示共享值来源，不代表恢复分支、token 配对或异常协议成立。`AsyncBodyRecovery` 分别检查保存、恢复、清空、source/token 配对、调度后返回和异常出口。

`UniTaskStorage` 根据 Clang 布局读取 source、token 和 result，不为普通任务与泛型任务共用固定偏移。调用快照包含 X0–X8、V0–V7、SP 和内存，参数按 ABI 读取。

`.await-sites.json` 保存挂起数据流，`.ssa-managed.json` 保存调用及存储分析，`.flow.json` 保存控制流。
