# Cpp2CS · 第十次尝试

目标：直接读取 IDA 数据库中的 ctree，结合 IL2CPP 元数据恢复可编译、可验证的 C#。

本分支没有父提交。第九次尝试保留在 `attempt-09`，不继承其整个分析管线。

- [接入方案](docs/IDA接入方案.md)
- [首组交付与验证](docs/首组交付.md)
- [无头探针](scripts/ida_probe.py)：顺序读取伪代码、ctree 节点、变量、引用、警告及优化后的 microcode。

数据库实验副本放在 `D:/Cpp2CS/attempt-10/ida-session/`，原始数据库保留在仓库外层的 `.re-jp-pjsk-7.0.0/ida/`。数据库、二进制和查询生成物不提交 Git。

已打通 ctree → 托管表示 → C# → 独立编译 → 原始 ARM64 差分执行的完整链路。首组恢复 `Sekai.Api.MusicScoreSearchConditionRequest`、`Sekai.Mysekai.StaminaData` 两个完整类型及其两个枚举依赖，共八个方法。当前是有明确能力边界的转换器，尚未覆盖 API 请求执行链、异步、异常区域和 Unity 运行环境。

```powershell
python -X utf8 -u scripts/run_first.py D:/Cpp2CS/attempt-10/ida-session/libil2cpp.i64
```

生成源码和独立工程位于 `artifacts/first/recovered/`。所需本机工具为 .NET 10、Python、IDA 9.3 的 idapro 和 Unicorn；脚本不安装依赖。
