# Cpp2CS · 第十次尝试

目标：直接读取 IDA 数据库中的 ctree，结合 IL2CPP 元数据恢复可编译、可验证的 C#。

本分支没有父提交。第九次尝试保留在 `attempt-09`，不继承其整个分析管线。

- [接入方案](docs/IDA接入方案.md)
- [无头探针](scripts/ida_probe.py)：顺序读取伪代码、ctree 节点、变量、引用、警告及优化后的 microcode。

数据库实验副本放在 `D:/Cpp2CS/attempt-10/ida-session/`，原始数据库保留在仓库外层的 `.re-jp-pjsk-7.0.0/ida/`。数据库、二进制和查询生成物不提交 Git。

当前仅验证接入能力，尚未实现通用 ctree → C# 转换器。
