# Cpp2CS

基于 C# / .NET 10 的 IL2CPP 分析工具。输入为二进制、metadata 和方法 VA，输出为 C# 语义视图。

支持 AArch64 小端 ELF 磁盘文件。不支持 PE、Mach-O、内存转储或加密 metadata。无法确定的类型、调用和控制流以未恢复项表示；生成的视图不保证可独立编译或与运行时行为等价。

## 构建

依赖 .NET 10 SDK、Clang 和 Capstone 5 原生库。`clang` 由 PATH 解析，Capstone 由系统原生库加载器解析；可用 `CPP2CS_CLANG` 和 `CPP2CS_CAPSTONE` 指定工具路径。

```powershell
git submodule update --init
dotnet build Cpp2CS.slnx -c Release
```

导入器依赖 `third_party/Il2CppDumper` 固定版本源码和 Mono.Cecil 0.11.4，两者使用 MIT 许可证。

## 使用

将占位符替换为对应文件和十六进制地址。VA 是虚拟地址，不是文件偏移。

```powershell
dotnet run --project src/Cpp2CS.Cli -c Release --no-build -- "<binary>" "<metadata>" "<VA>"
```

标准输出为 C#，标准错误为未恢复项。CLI 自动生成 script.json、il2cpp.h 和 DummyDLL，不读取 `native.local.json`。

中间文件位于工作目录的 `.cpp2cs/cache/`，以二进制 SHA-256、metadata SHA-256 和导入器版本区分。相同输入复用缓存；导入失败的日志位于对应 `.pending-*` 目录的 `import.log`。

添加 `--diagnostics <目录>` 可保存指令、SSA、语义视图和证据报告：

```powershell
dotnet run --project src/Cpp2CS.Cli -c Release --no-build -- "<binary>" "<metadata>" "<VA>" --diagnostics artifacts/recovered
```

| 退出码 | 含义 |
|---|---|
| `0` | 无已报告的未恢复项 |
| `2` | 输入或导入失败 |
| `3` | 存在未恢复语义 |

## 测试

```powershell
dotnet run --project tests/Cpp2CS.Tests -c Release --no-build
```

测试入口为可执行断言程序。机器码对照脚本依赖 Python、Unicorn 和 pyelftools；需要配置的测试显式接收配置文件，格式见 `native.example.json`。

## 结构

| 目录 | 职责 |
|---|---|
| `src/Cpp2CS.Input` | ELF 与 metadata 导入 |
| `src/Cpp2CS.Core/Model` | 定义身份、泛型实例、布局和证据 |
| `src/Cpp2CS.Core/Abi` | AAPCS64 参数与返回分类 |
| `src/Cpp2CS.Core/IR` | 位值、寄存器、内存和调用状态 |
| `src/Cpp2CS.Core/Native` | ARM64、控制流、SSA 和托管语义 |
| `src/Cpp2CS.Cli` | 参数处理、缓存和输出 |
| `tests` | 断言、夹具和执行对照 |

模型约定见 [核心模型](docs/核心模型.md)。

方法恢复顺序、async 与普通业务体的公共部分、兼容回退和回归入口见 [方法恢复流水线](docs/方法恢复流水线.md)。
