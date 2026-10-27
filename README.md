# Cpp2CS

Cpp2CS 从 Unity IL2CPP 二进制与匹配的元数据中恢复托管方法，输出 CIL 程序集、C# 源码和未恢复部分的诊断。

恢复管线面向 Android ARM64 ELF，运行时布局按 Unity 2022.3.62f2、元数据 v31 建模。映像读取能力不代表其他平台或版本已完成恢复适配。

## 构建

需要 .NET 10 SDK。元数据解析使用 Il2CppDumper 子模块；CIL 写出使用 Mono.Cecil；C# 输出使用 ILSpy。

```bash
git submodule update --init
dotnet build Cpp2CS.slnx -c Release
```

## 使用

恢复范围必须显式指定，可选命名空间、程序集、方法清单或 `--all`：

```bash
dotnet run --project src/Cpp2CS.Cli -c Release -- recover <binary> <metadata> <output> --namespaces Example
dotnet run --project src/Cpp2CS.Cli -c Release -- recover <binary> <metadata> <output> --methods <methods.tsv>
```

方法清单每行是十六进制入口地址和完整方法名，以制表符分隔，必须与输入映像匹配。
`--assemblies A.dll,B.dll` 按程序集选择；`--all` 选择全部托管方法定义；`--limit N` 限制非清单模式的方法数量；`--no-source` 跳过 C# 文件生成。

`--source-layout project` 按 `src/程序集.dll/命名空间/类型.cs` 导出，并为每个程序集生成 `.csproj`；泛型同名类型合并到同一文件。包含所选范围内的全部类型声明，未恢复成员仍为占位体。默认 `flat` 保持平铺输出；项目文件不代表源码已通过编译。

`--jobs N` 设置方法恢复的最大并行度，默认 `1`。例如 `--jobs 8` 同时恢复最多八个方法，共享基础事实，每个工作线程使用独立恢复器；结果按原清单顺序汇总。依赖处理和程序集写出仍按顺序执行，最终 C# 按类型并行生成。
已有程序集可用 `source-project <程序集.dll> <输出目录>` 单独导出，依赖从程序集所在目录解析。

其他入口：`facts` 建立基础事实，`refs` 查询函数引用，`layout` 查询字段布局，`ssa` 查看机器 IR，`idioms` 统计编译器模式。无参数运行 CLI 可查看用法。

## 输出

| 路径 | 内容 |
|---|---|
| `assemblies/` | 元数据骨架与恢复的 CIL，供底层检查和执行对照 |
| `assemblies-src/` | 为源码展示整理后的程序集 |
| `src/` | C# 文件 |
| `recovery.jsonl`、`emitted.tsv` | 逐方法诊断与完整写出清单 |
| `holes.txt` | 未恢复原因与汇总 |

部分方法可以输出可读片段，并以 `Cpp2CS.Unrecovered` 和原生地址标记缺口；完整原因见 `recovery.jsonl`，不嵌入程序集字符串堆。这些方法不计入完整写出清单。源码折叠和类型名称还原不等于整个工程可以编译或在 Unity 中运行。

实现边界见 [架构](docs/架构.md)，检查方式见 [验证](docs/验证.md)。
