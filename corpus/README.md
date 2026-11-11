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

收到压缩包后可用 `--nm <llvm-nm> --library arm64-v8a=<sym.so> --library x86_64=<sym.so>` 替换两个 `--symbols` 参数直接检查 ELF。归档不进入仓库。构建脚本不抽取真实 IL、地址映射或内联记录；IL 与地址映射由下文的真值工具处理。

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

## 真值

`truth/` 是独立工具，不加入解决方案。读取产物根目录，输出到另一个空目录；不构建语料，不修改输入，不抽取 DWARF 内联记录。依赖 Python 3.11+ 标准库、.NET 10、Mono.Cecil（沿用仓库集中版本）、GNU `c++filt` 和验收用的 `nm`。构建、抽取、验收均按 `AGENTS.local.md` 加同一把重任务锁；以下变量由调用者提供，不把机器路径写进脚本。

```sh
"$DOTNET" build corpus/truth/Managed/Managed.csproj -nodeReuse:false -m:1
python3 corpus/truth/extract.py --input "$CORPUS_INPUT" --output "$TRUTH_OUTPUT" \
  --dotnet "$DOTNET" --managed-reader corpus/truth/Managed/bin/Debug/net10.0/Managed.dll
python3 corpus/truth/extract.py --input "$CORPUS_INPUT" --output "$TRUTH_REPEAT" \
  --dotnet "$DOTNET" --managed-reader corpus/truth/Managed/bin/Debug/net10.0/Managed.dll
python3 corpus/truth/verify.py --input "$CORPUS_INPUT" --truth "$TRUTH_OUTPUT" \
  --repeat "$TRUTH_REPEAT" --report "$TRUTH_REPORT"
```

`TRUTH_OUTPUT`、`TRUTH_REPEAT` 是两个不同的空目录，建议放在被忽略的 `artifacts/corpus.local/` 下。`TRUTH_REPORT` 放在真值目录之外。可用 `--cases` 指定用例清单，默认是仓库的 `cases/methods.json`，必须与产物的 `source/cases/methods.json` 内容一致。`--cxxfilt`、`--nm` 可指定工具位置。程序发现歧义、输入校验失败或用例缺失时非零退出，不覆盖已有输出。

### 文件与字段

格式版本为 1。表是 UTF-8 JSON 数组，键排序、固定缩进、LF 换行，无时间戳与绝对路径。标记、地址使用 `0x` 十六进制字符串；大小、索引和行号使用整数。空列表表示没有匹配，`null` 表示不适用或没有证据。地址为 ELF 链接虚拟地址，不含加载偏移。

| 文件 | 一项的含义与主要字段 |
|---|---|
| `methods.json` | `ManagedStripped/*.dll` 中每个 MethodDef，包括支撑代码、构造函数、访问器、泛型定义及无方法体方法。`id` 为 `assembly:token`；`assembly` 为文件名，`assembly_identity` 为完整程序集身份，`module_mvid` 标识模块，`assembly_path` 相对输入根目录。`declaring_type`、`name`、`signature` 为 Cecil 的完整名称；`signature_blob` 为原始 ECMA-335 签名字节，`generic_arity` 为方法泛型参数数，`generic_type` 表示声明类型有泛型参数。`has_body` 按 RVA 非零判断；`rva` 指向原方法体；`il_size`、`il_hex`、`il_sha256` 仅含 IL 指令流，不含方法头、局部签名和异常表；无方法体时三者为 null。有对应元数据时附 `metadata_index`、`declaring_type_token`。 |
| `functions.<目标>.json` | 完整 `.symtab` 的每个 FUNC/IFUNC 符号，不重复读 `.dynsym`。`symbol_index` 是原符号表索引；`name` 为原始链接名，`demangled_name` 为 `c++filt` 输出，`cpp_name` 是能与生成 C++ 定义名精确匹配的名字。`address`、`size` 来自 `st_value`、`st_size`；范围为半开区间 `[address,address+size)`，大小为零时不猜范围。`section`、`section_index` 为所属节；`defined=false` 表示未定义导入，不作为函数范围。`binding`、`visibility` 保留 ELF 数值，`symbol_type` 为 FUNC/IFUNC。`same_address_symbols` 列出同节同地址的已定义符号索引，`duplicate_address` 表示多于一项；不据此断言一定发生了相同代码折叠。 |
| `mappings.json` | 方法到生成函数的一条关系。`method_id` 关联方法表；没有托管输入时为 null，仍保留 `metadata_method_id`。`cpp_name` 是生成函数名，`role` 区分普通入口、共享/非共享泛型实例、内联副本、调整桩、调用器、泛型包装函数。`evidence` 给出注册表及槽位或包装函数体位置。`targets` 按目标列出原始 `symbol_name`、`symbol_index`、地址、大小和节；不会把共享入口地址冒充包装函数自己的地址。`sources` 列出所有定义位置。泛型关系附 `method_spec_index`、`class_inst_index`、`method_inst_index`；实例索引 -1 表示无该类实例化。包装函数另有 `forwarded_to`、`forwarded_targets`。同一个共享入口可以关联多个方法/实例；同一个内联定义可在多个翻译单元出现。 |
| `generic-instances.json` | 每个 `g_Il2CppMethodSpecTable` 项，保存方法定义键、实例索引和有注册依据的 `cpp_names`。空名字列表不证明该实例未被使用，也不猜其共享目标。 |
| `generated.json` | 生成 C++ 定义名与已定义原生符号名的并集，用于查找未建立托管关系的函数。`name`、`kind`、`linked`、`sources`、`targets`；`linked=false` 如实保留未关联项，原生运行时函数通常不对应 MethodDef。`sources` 为空时也可能是当前 C++ 解析器未覆盖，不能据此判定没有源码。 |
| `cases.json` | 用例清单每项一条：原始 `case`、完整 `method` 项、唯一普通入口 `mapping`；同时包含双目标地址与大小、C++ 定义位置。 |
| `coverage.json` | 每个托管方法的 `method_id`、`signature`、`has_body`、`case_assembly`、`status`。分母按方法定义计，不按共享入口或关系条数计。 |
| `unmatched-metadata.json` | 元数据中存在、但相应映像没有托管程序集输入的方法；保留方法键、名字、全局索引和原因，不伪造 IL。若已有托管程序集却缺少对应标记，立即失败。 |
| `target-differences.json` | 两目标已定义原始函数名集合的对称差集。`target` 表示哪边独有，保留原名、解码名、`cpp_name` 和 `reason` 分类；`cause_proven=false` 表示没有编译器/链接器证据证明消失的确切原因。 |
| `checks.json` | 用例唯一性、独立 IL 核对、覆盖、附加函数、重复地址及目标差异计数；`inline_debug_records=not_extracted` 明确没有读取内联记录。 |
| `manifest.json` | 格式/工具版本、工具源码 SHA-256、托管读取器和 Cecil 二进制 SHA-256、运行工具版本、用例、产物中的用例快照与输入清单 SHA-256、逐输入产物的路径/字节数/SHA-256、各表条数及输出校验和（不含清单自身）。输入清单全部重新校验，包括调试库；读取的程序集、C++、元数据和符号库必须在清单中；用例快照单独记录校验和。 |

`source` 位置中的 `file` 相对输入的 `artifacts/il2cppOutput/cpp/`；`start_line` 是函数声明首行，`end_line` 是结束花括号所在行，均从 1 开始且包含端点。`declaration` 保存声明，`managed_comment` 保存紧邻的单行注释，没有时为 null。当前解析器覆盖生成器的单行函数声明、下一行独立左花括号形式；先屏蔽字符串和注释再配对括号，不把声明或调用当作定义。

后续工具用 `assembly_path` 打开原程序集、按 `token` 取 MethodDef，即可读取完整方法体及局部变量和异常区域。`il_hex` 可直接用于指令字节核对；它不是可独立装载的完整方法体。引用的原程序集由清单校验和固定。

### 对应依据与附加函数

当前支持小端 ELF64、Unity 元数据 v31 和该生成器注册表布局；不支持的布局报错。普通函数由 CodeGen 模块的 `s_methodPointers[RID-1]` 关联，程序集名取模块声明；v31 元数据的方法标记、名字与托管输入交叉核对。调用器由模块 `s_InvokerIndices` 指向 `g_Il2CppInvokerPointers`。泛型由方法规格表、泛型函数注册表、函数指针表和调整桩表关联；不以类型短名或哈希反推托管方法。

该语料 C++ 没有托管方法前置注释，因此注释不是必要证据。`_inline` 副本按已注册函数名加精确后缀识别；`_AdjustorThunk` 按精确后缀或泛型调整桩注册表识别；`_gshared` 标记共享实现。`RuntimeInvoker_` 标记运行时调用器。泛型包装函数必须是生成的 `inline` 单返回语句函数，函数体仅引用一个已注册泛型调用目标，且该目标只关联一个方法定义，才建立转发关系。包装函数不会计入普通入口验收。

`kind` 还区分 `_marshal_pinvoke/com` 及其 back/cleanup 后缀的 `marshal_helper`、`DelegatePInvokeWrapper_` 的 `delegate_pinvoke_wrapper`、方法哈希之后 Open/Closed/Multicast 后缀族的 `delegate_helper`；这些分类不自动推定 MethodDef。剩余项为 `method` 或 `generated_other`，后者也包含原生库函数。附加函数统计以有 C++ 定义的唯一名字计，关系表可能有多条实例或翻译单元证据，不能直接作为函数数量。

覆盖状态：`mapped_both_targets` 表示普通或泛型实现至少一条关系在双目标都有定义符号；`no_managed_body` 无 IL 方法体；`registered_but_native_symbol_missing` 有注册入口但缺符号；`no_registered_generic_instance` 为泛型定义没有读到注册实例；`no_registered_pointer_unresolved` 为其他缺口。后两者不等于已证明“未实例化”或“被裁剪”。无法仅凭符号缺失区分内联消除、死代码删除、链接裁剪和解析范围，必须保留不确定性。

目标差异按可观察来源分类：展开器与链接桩、ABI 类型、原生模板发射、生成 C++ 发射、未决运行时差异。两个目标共享托管输入和生成 C++，普通托管入口的集合一致时，不把原生模板或平台库的符号差异解释成托管裁剪。生成的 `_inline` 定义只在一边留下符号，也不能证明另一边的 DWARF 内联记录存在或完整。

### 自检与边界

抽取时要求每个用例恰好一个 MethodDef、一个普通 C++ 定义、每个目标恰好一个定义符号，并核对完整前缀及 40 位哈希。原始 IL 由 `PEReader` 读取，独立用 Cecil 解码并重编码比较；字符串操作数不保留原字符串标记、泛型参数操作数可能丢失原 TypeSpec 标记，这两类不做字节重编码旁证，但仍完整抽取原始 IL。当前全部 42 个用例均能做独立字节核对。

`verify.py` 核对两次输出全部文件逐字节相同，并用 `nm -S --defined-only` 独立核对全部用例的名字、地址和大小，另输出来自五个类别的抽查明细。报告不写回真值，避免改变可复现产物。完整方法体语义、IL 执行、内联记录及非 v31/非 ELF64 格式不在此工具的验证范围内。
