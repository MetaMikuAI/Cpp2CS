# IL2CPP 语料

用 Unity 2022.3.62f2、其 Android NDK clang、Release 配置一次构建 ARM64 与 x86_64。两个目标共用生成的 C++ 和元数据，保留调试符号。语料是已知源码的输入；符号存在不代表语义恢复或优化形态验证通过。

## 目录

- `cases/<类别>/*.cs`：按生成器模板或编译器变换分类的用例。
- `cases/Support.cs`：类型、静态构造、调用目标等支撑代码，不计为独立用例。
- `cases/methods.json`：验收方法清单，记录类型、方法和生成器符号前缀。
- `unity/`：最小 Unity 外壳；构建时把 `cases/` 复制到 `Assets/Corpus/Cases/`。
- `build/`：本机驱动、Windows 后台包装、产物清单与符号检查脚本。

| 类别 | 方法数 | 内容 |
|---|---:|---|
| arithmetic | 8 | 整数、浮点、位运算、转换 |
| fields | 9 | 实例与静态字段、结构体、嵌套结构体、数组 |
| calls | 6 | 直接、虚、接口、委托、引用类型共享泛型 |
| control | 5 | if/else、三元、while、for、switch |
| checks | 4 | 空、边界、除零、余数除零 |
| guards | 4 | 元数据与类初始化守卫的分支候选、与空/边界检查组合 |
| dispatch | 3 | 重复接口调用、分支尾合并、接收者合流 |
| typechecks | 3 | is、as、castclass 结果合流 |

共 42 个用例方法。`NoInlining` 保留独立函数；`link.xml` 保留整个用例程序集，泛型调用方法显式实例化两个引用类型。`Support.TypeToken` 有意强制内联，用于构造方法元数据守卫复制候选。构建入口显式开启 `--enable-divide-by-zero-check`，因此除零检查属于本语料配置，不能外推到默认配置。

## 增加用例

1. 在对应类别增加小而单一的方法，方法名描述考察内容，添加 `MethodImplOptions.NoInlining`。不对真实业务方法或地址做特判。
2. 在 `methods.json` 登记其类型、方法名与 `<类型短名>_<方法名>_m` 前缀。避免重载和类型短名冲突；泛型体放在支撑代码，用非泛型入口作为独立验收方法。
3. 构建两个 ABI，检查符号唯一性，再核对生成 C++ 和机器码。源码上的两臂不保证优化后仍有两份守卫或共享慢路径；未出现时保留失败结论。
4. 改动计数时同步本文；支撑方法不进入用例分母。程序集的保留不代替每个用例的符号核对。

## 构建

本机需要 Python 3、OpenSSH；Windows 需要 Python 3、PowerShell 5.1、指定版本 Unity 与 Android 支持。所有 `.ps1` 必须带 UTF-8 BOM。为每次构建使用新运行名，不覆盖已有项目缓存或输出。

本机创建不入库的 `settings.local.json`，填写 `host`（SSH 别名）、`root`（专用新目录，末级名为 `corpus`）、`unity`（Unity.exe 完整路径）。远端父目录需已存在。实际机器路径只放本地配置，不写入仓库。

```sh
python3 corpus/build/drive.py sync --config settings.local.json
python3 corpus/build/drive.py probe --config settings.local.json
python3 corpus/build/drive.py start --config settings.local.json --run first
python3 corpus/build/drive.py status --config settings.local.json --run first
python3 corpus/build/drive.py fetch --config settings.local.json --run first --destination results.local.dir
```

`start` 经 WMI 创建脱离 SSH 会话的后台进程。发现任意 Unity 进程时拒绝启动，不终止其他进程。两个 ABI 在一次 Unity 调用中构建；手动轮询至少间隔 60 秒。`status` 返回运行阶段、Unity 和包装脚本退出码及日志尾部。`complete` 才表示构建、清单、符号检查和打包全部完成；仅有启动 PID 不表示构建成功。

`sync` 仅传源码和脚本，并生成逐文件 SHA-256 清单；构建只使用清单内文件，远端残留的旧文件不参与合成。源码校验失败即停止。`fetch` 仅传固定文本清单，每个文件先核对不超过 5 MB。压缩包由用户另行传输，不经慢隧道下载。

## 产物与检查

远端 `<root>/runs/<run>/`：

- `project/`：合成工程与 Unity/Bee 缓存。
- `output/artifacts/il2cppOutput/`：生成 C++、数据、各 ABI 的 `libil2cpp.so`、`libil2cpp.sym.so`、`libil2cpp.dbg.so`。
- `output/artifacts/ManagedStripped/`：裁剪后托管程序集，供后续 IL 真值抽取。
- `output/artifacts/commands/`：Bee JSON 与响应文件，用于核对 IL2CPP 实际输入、编译命令。
- `output/source/`：此次输入源码与脚本的快照。
- `output/manifest.json`：产物相对路径、字节数、SHA-256。
- `output/provenance.json`：工具位置、clang 版本、NDK 版本及裁剪目录来源。
- `output/symbol-check.{txt,json}`：两目标的找到数、缺失和不唯一列表。
- `output/*-shapes.txt`、`cases-cpp.txt`：三族候选和检查用例的机器码、用例 C++ 文本。
- `corpus-artifacts.zip` 与 `archive.json`：后续任务所需归档及其路径、大小、SHA-256。APK 不纳入归档。

后台自动运行严格检查：只接受已定义的 `T/t` 函数符号、完整方法前缀和哈希后缀，排除数据、未定义符号、内联副本和调整桩。每个用例必须恰好匹配一个名字；丢失或歧义均退出失败。

也可对取回的文本清单重跑：

```sh
python3 corpus/build/check_symbols.py --methods corpus/cases/methods.json \
  --symbols arm64-v8a=results.local.dir/arm64-v8a-symbols.txt \
  --symbols x86_64=results.local.dir/x86_64-symbols.txt \
  --output results.local.dir/recheck.json
```

收到压缩包后可用 `--nm <llvm-nm> --library arm64-v8a=<sym.so> --library x86_64=<sym.so>` 替换两个 `--symbols` 参数直接检查 ELF。归档不进入仓库。本任务不抽取真实 IL、地址映射或内联记录；它们由后续真值抽取任务处理。

## 已核对的形态与缺口

以下结论来自 Unity 2022.3.62f2、NDK 23.1.7779620 / clang 12.0.8 的双目标 Release 产物。定位使用方法名及函数内偏移；完整文本在 `*-shapes.txt` 与 `cases-cpp.txt`，地址只对对应产物有效。

| 用例 | 双目标结果 |
|---|---|
| `Guards.ClassInitOnBranches` | 两臂分别保留类初始化检查和调用；ARM64 的初始化调用在 `+0x48`、`+0x84`，x86_64 在 `+0x3c`、`+0x7a`。方法入口另有单份元数据守卫。 |
| `Dispatch.InterfaceBranchTail` | 两臂保留各自的接口表查找循环，共享一个慢路径和间接调用尾部。ARM64 两臂失败边汇入 `+0xac`，x86_64 汇入 `+0x9b`。 |
| `Dispatch.RepeatedInterface` | 同一方法有两次接口查找、两次慢路径调用和两次接口方法调用。 |
| `TypeChecks.IsMerge`、`AsMerge`、`CastMerge` | C++ 两臂结果写入同一个局部；机器码也保留两臂检查与结果合流。ARM64 的合流分别位于 `+0x74`、`+0x74`、`+0x7c`。强制转换的失败路径调用抛异常 helper。 |
| `Checks.DivideByZero`、`RemainderByZero` | C++ 有 `DivideByZeroCheck`；两个目标都有除数为零的异常分支。 |
| `Guards.MetadataOnBranches` | C++ 两臂调用含元数据守卫的 `_inline` 副本；机器码只有单份守卫。未使用返回值的纯 `Opaque` 调用被消去，源分支也随之消失。`NoInlining` 不阻止死调用删除。 |
| `Guards.GuardWithNull`、`GuardWithBounds` | 类初始化与空/边界检查确实共存；前者的显式判空吸收了隐式判空。尚未观察到初始化守卫与其他检查共用同一条件跳转或冷路径，不能计为该形态已覆盖。 |

补足元数据守卫复制可以尝试让两臂分别在守卫之前、之后执行有可观察写入的非内联调用，阻止尾部合并；该构造尚未验证。补足守卫与检查共享分支可尝试在强制内联 helper 中交错空/边界检查与初始化，并使两臂拥有共同成功尾部；必须重新核对机器码，不能把源码上的组合当成已生成的形态。

符号检查通过不证明内联记录完整、CIL 真值可读或执行语义一致；这些属于后续任务。当前类型检查只覆盖 sealed 类，没有覆盖非 sealed 继承链和接口类型检查。
