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

`truth/` 是独立工具，不加入解决方案。读取产物根目录，输出到另一个空目录；不构建语料，不修改输入。`extract.py` 抽取 IL 与地址关系，`inline.py` 另行抽取 DWARF 内联记录并审计调用来源。依赖 Python 3.11+ 标准库、.NET 10、Mono.Cecil（沿用仓库集中版本）、GNU `c++filt` 和验收用的 `nm`。构建、抽取、验收均按 `AGENTS.local.md` 加同一把重任务锁；以下变量由调用者提供，不把机器路径写进脚本。

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

`verify.py` 核对两次输出全部文件逐字节相同，并用 `nm -S --defined-only` 独立核对全部用例的名字、地址和大小，另输出来自五个类别的抽查明细。报告不写回真值，避免改变可复现产物。完整方法体语义、IL 执行及非 v31/非 ELF64 格式不在此工具的验证范围内；内联记录另按下节验证。

### 内联记录与完整度审计

`inline.py` 消费已有真值及其匹配的产物，输出独立目录，不改 `cases.json` 等已有文件。依赖 Python 3.11+、pyelftools 0.32、Capstone 5.0.6；Python 包安装到仓库外的虚拟环境。两个目标均用 Capstone 解码，避免依赖本机 objdump 的目标支持。调用者须按本机约定加重任务锁，以下命令省略锁前缀。

```sh
"$TRUTH_PYTHON" corpus/truth/inline.py --input "$CORPUS_INPUT" --truth "$TRUTH_INPUT" \
  --output "$INLINE_OUTPUT" --cache "$INLINE_CACHE"
"$TRUTH_PYTHON" corpus/truth/inline.py --input "$CORPUS_INPUT" --truth "$TRUTH_INPUT" \
  --output "$INLINE_REPEAT" --cache "$INLINE_REPEAT_CACHE"
```

输出目录必须为空，不能在输入产物或已有真值目录中。缓存目录与输出分开，建议置于被忽略的目录。缓存按调试库、工具源码、函数表、生成表和映射表的 SHA-256 失效；按编译单元释放解析缓存，避免同时驻留两目标的 DWARF。已有真值的输出校验和及产物清单逐项核对，确保源码、机器码、调试库来自同一批输入。

格式版本为 1，JSON 排序、缩进、地址及换行约定同前。每个目标各有三张表，另有两个公共文件：

| 文件 | 内容 |
|---|---|
| `inlines.<目标>.json` | 每个有非空 `method_id` 映射且有定义符号的生成函数一项，包含调用器、共享入口等；共享入口按 `cpp_name` 计一次。`cpp_name`、`method_ids`、`address`、`size` 关联原有表。`debug_function_found` 区分找不到 DWARF 函数与找到函数但没有内联。`records` 无记录时为空。 |
| `inline-cases.<目标>.json` | 原有 `cases.json` 每个用例一项，带 `case`、`method_id` 及上述函数记录；按普通入口 `mapping.cpp_name` 精确关联，不需要修改原用例表。 |
| `inline-audit.<目标>.json` | 每函数的源码调用位置、直接机器调用、尾调用、名称匹配状态和额外内联来源。`calls` 每项含 `name/file/line/known/status`；`matching_inline_ids` 是同名记录，`callsite_inline_ids` 进一步要求调用文件与行号一致。`candidate_class` 沿用生成表的 `kind`，不自动判定删除原因。`direct_calls` 保存调用地址、目标地址、候选符号名、`tail`、`via_plt`。`extra_inline` 标出不直接见于函数体的记录：嵌套内联、头文件/模板/宏候选或未解释项。 |
| `inline-summary.json` | 双目标的全部函数及用例子集统计、源码可用函数数、DWARF 函数数、记录数和候选比例。 |
| `inline-manifest.json` | 版本、工具与依赖版本、输入真值校验和、输出校验和。实际产物由输入真值清单及调试库 SHA-256 固定；不记录机器路径和时间戳。 |

一条 `records` 记录含：

- `id`：该 `.debug_info` 内 DIE 的绝对节偏移，`parent` 为最近的外层内联 DIE，顶层为 null；不是跨构建身份。
- `name/linkage_name`：沿 `abstract_origin/specification` 读取的原名及链接名。`generated_name` 精确关联 `generated.json` 的名字或链接名；`method_ids` 关联 `mappings.json`。没有生成源码定义的项标为 `origin=runtime_or_library`，不猜托管身份。
- `ranges`：全部半开地址段，保留多段、空段及重叠，不推断连续区域或互斥分区。读取 `low_pc/high_pc` 或 range list，处理基址选择。
- `call_file/call_line/call_file_index`：调用来源；`declaration_file/declaration_line`：被内联定义来源。文件只保留文件名，避免泄漏编译机路径；`cu_offset` 与文件表索引可用于回查同名文件。缺少属性为 null。

**统计口径。** 源码扫描先屏蔽字符串和注释，再按已有定义范围查找普通调用、模板调用及函数指针转换后的具名调用。`known` 表示名字精确存在于生成表（该表也含原生符号），不是推测的托管方法。分母 `known_calls` 是所有定义位置的已知名字调用出现次数，包含同名调用的不同源码位置；不是动态执行次数、唯一被调方法数或内联事件数。状态优先级为直接调用 `direct`、同名内联 `inline`、两者皆无的 `missing_candidate`。只证明函数内存在同名证据，不证明每个调用位置都保留；需另看 `callsite_inline_ids`。候选比例是 `missing_candidate / known_calls`，不是已经证实的调试信息漏记率。

未知名字匹配到运行时内联时记 `runtime_inline`，其余调用形文本记 `unknown` 并计数。当前不运行 C++ 预处理器；宏内部的隐藏调用、函数指针间接调用、类型转换和函数类型声明可能落入未知项，不能把未知计为零或当作已验证调用。直接调用包含函数范围外的无条件直接跳转；PLT 通过跳板读取的 GOT 槽与 `.rela.plt` 关联。间接分派、其他跳板和复杂跨函数跳转不作目标恢复。任一函数机器码解码不完整即失败。

额外内联不是自动异常：例如接口 `Invoke` 内嵌运行时查表函数，算术模板定义在头文件；`FinallyHelper` 的隐式析构和 `Il2CppFakeBox` 的构造也可能没有同名的显式调用文本；`parent`、声明文件和源调用位置提供人工追溯依据。头文件/模板/宏分类只是来源候选，不能据此证明所有额外记录均已解释。

**独立核对。** 对每个目标生成 GNU readelf 的 `--debug-dump=info --wide` 与 `--debug-dump=Ranges --wide` 文本，保存在忽略目录，再运行：

```sh
"$TRUTH_PYTHON" corpus/truth/verify_inline.py --truth "$INLINE_OUTPUT" --repeat "$INLINE_REPEAT" \
  --info "arm64-v8a=$ARM_INFO" --ranges "arm64-v8a=$ARM_RANGES" \
  --info "x86_64=$X64_INFO" --ranges "x86_64=$X64_RANGES" \
  --case Corpus.Arithmetic.IntegerArithmetic --case Corpus.Calls.InterfaceCall \
  --case Corpus.Calls.DelegateCall --report "$INLINE_REPORT"
```

核对程序不调用 pyelftools：解析 readelf 的 DIE、抽象来源和范围文本，比较所选用例每条记录的名字与全部地址段，并核对两次输出的全部文件逐字节一致，以及全体记录的父引用、无环嵌套和函数范围边界。该文本解析器验证的是当前 GNU readelf 的 DWARF4 输出，不是通用 DWARF 文本解析器。

**已知完整性边界。** 当前 Release 语料存在明确反例：`Guards.MetadataOnBranches` 两臂的 `Support.TypeToken` 内联副本合并后，初始化与类型查询机器码仍在，但两个目标均没有该副本的内联记录；两处未使用结果的 `Support.Opaque` 纯调用则可直接消去。不能把这四处候选都算作漏记。另在库代码中，相邻字段 getter 被 ARM64 的一条成对加载覆盖时，只留下其中一个 getter 的记录，而 x86_64 的独立加载各有记录。这说明已有记录可作为局部正例和嵌套来源证据，不能充当完整内联集合或完整区域边界；内联逆的完整度验证需要人工标注的小对照集。

当前用例已有两级生成包装/内联副本及三级运行时嵌套、分段范围、检查吸收与合并后记录缺失；尚缺专门隔离的多入口内联、含循环或异常区域内联，以及相邻有可观察写入的内联合并用例。需要另外构建这些用例，不能从一般 BCL 函数出现类似指令就宣称覆盖。其他编译器、优化级别、Unity 版本及 DWARF5 尚未验证。

### 入口形参与类型形状

`truth/parameters.py` 读取匹配的 DWARF 与 `.eh_frame`，为 ABI 分类器提供独立的编译器证据。依赖和虚拟环境同内联工具；不构建语料，不推导 ABI 槽位。调用者按本机约定加重任务锁。输出及缓存不得位于输入产物或已有真值目录内，输出必须为空。

```sh
"$TRUTH_PYTHON" corpus/truth/parameters.py --input "$CORPUS_INPUT" --truth "$TRUTH_INPUT" \
  --output "$PARAMETER_OUTPUT" --cache "$PARAMETER_CACHE"
"$TRUTH_PYTHON" corpus/truth/parameters.py --input "$CORPUS_INPUT" --truth "$TRUTH_INPUT" \
  --output "$PARAMETER_REPEAT" --cache "$PARAMETER_REPEAT_CACHE"
"$TRUTH_PYTHON" corpus/truth/check_parameters.py
"$TRUTH_PYTHON" corpus/truth/verify_parameters.py --input "$CORPUS_INPUT" \
  --truth "$PARAMETER_OUTPUT" --repeat "$PARAMETER_REPEAT" --report "$PARAMETER_REPORT" \
  --function "$CPP_FUNCTION_NAME"
```

重复运行使用不同的空缓存目录，检查完整抽取过程的确定性；也支持按调试库、机器码、工具及关联表的 SHA-256 复用缓存。逐编译单元释放 DIE 缓存，两个目标串行解析。`verify_parameters.py` 比较全部 JSON 的字节、检查用例关联，并用 Capstone 导出 `--function` 指定的完整函数机器码；选项可重复。机器码与参数位置是否一致须人工核对，工具不把“成功解码”当成一致性证明。

格式版本为 1，沿用前述 JSON、地址和换行约定，无机器路径、时间戳：

| 文件 | 内容 |
|---|---|
| `parameters.<目标>.json` | `mappings.json` 有非空 `method_id` 且目标有定义符号的每个 `cpp_name` 一项；共享函数按名字计一次。含 `method_ids/address/size/records`，以地址关联具体 DWARF 函数；同地址多个 DIE 全部保留，不选择一个冒充唯一签名。没有调试函数时 `records=[]`。 |
| `parameter-cases.<目标>.json` | 每个原有用例一项，含 `case/method_id` 和完整函数记录；以 `cases.json` 的 `mapping.cpp_name` 精确关联，不改原有用例表。 |
| `parameter-summary.<目标>.json` | `all` 为全部映射函数，`cases` 为受控用例子集，分别给函数数、找到调试函数数、形参数、完整入口位置已知数及比例、未知原因和类型形状未知数；`groups` 分组计数，`gaps` 列用例缺失、少于五项或位置不完整的组。五项仅为提醒阈值，不代表统计充分性。 |
| `parameter-manifest.json` | 工具、辅助模块、依赖版本、原有真值及两目标输入库和输出文件的校验和。 |

一条函数 `records` 含 `.debug_info` 节内 `die` 偏移、`dwarf_name`、`parameters`、`return_shape`、`variadic`、`frame_base`、`entry_cfa`。具体形参的名字、类型沿 `abstract_origin/specification` 继承；`index` 按形参 DIE 的出现顺序从零计数，保留 `this`、方法信息指针和 `artificial` 标志。返回类型仅抽形状，不推测返回位置或未描述的隐藏返回指针。

`shape` 含 `kind` 和字节 `size`：整数（含枚举、布尔和 UTF 字符）、指针、浮点、聚合、void 或 unknown。聚合包含成员名字、字节偏移及递归形状，保留位域属性；数组用 `element/dimensions` 表示，大小可由维数和元素大小得出。指针不递归展开被指类型。没有大小或成员偏移证据时为 null，不按托管布局补齐。

`location` 的 `source` 为直接表达式或覆盖函数最小代码地址的半开位置列表项；只读入口，不选第一个后续有效项。`expression` 保留解码后的 DWARF 操作。`pieces` 的 `value_bit_offset/size_bits` 给值内分片位置，`location_bit_offset` 给寄存器或存储内的起始位；`kind` 可为：

- `register`：`register/dwarf_register` 为 pyelftools 按目标 DWARF 寄存器编号给出的名字和编号，不映射到 ABI 抽象槽。支持直接寄存器和零偏移寄存器值、逻辑右移后 `stack_value` 描述的位片，后者标 `derivation=register_value_expression`。
- `stack`：`offset` 为相对函数第一条指令执行前 SP 的字节偏移。
- `indirect`：值位于 `register+offset` 指向的内存，不把指针形参自身所在的寄存器误标为按引用传递。
- `unknown`：带原因，可能附 `entry_value_pieces`。入口值表达式即使能读出寄存器也不计为当前位置已知。空片、未报告尾部、未支持表达式和未证明帧基址分别记录；不丢弃同一形参的其他有效分片。

`known=true` 要求所有报告分片可解释且没有未报告尾部；没有位置属性记 `no_location_attribute`，有列表但不覆盖入口记 `no_range_at_entry`。DWARF 通常不能区分“源码没用到”与“优化器删除了位置”，工具不伪造这个原因。含常量/掩码的计算值表达式保留原操作但不冒充存储位置。

**栈换算。** `entry_cfa` 来自机器码库的 CFI，在入口选覆盖该 PC 的规则，记录基址寄存器与偏移。若 CFA 为入口 SP 加常量，则 `DW_OP_call_frame_cfa` 可直接换算；`DW_OP_fbreg d` 则需已证明的 `frame_base.entry_sp_offset+d`。当前两个目标的入口 CFA 分别常见为 `sp+0`、`rsp+8`，这是读到的 CFI 事实，不是分类器默认值。

clang 的固定 `DW_AT_frame_base=SP` 配合 `fbreg` 有时以序言后的 SP 计数，即使位置范围覆盖入口。不能直接以入口 SP 加该偏移：x86_64 的一个多参数 `Guid` 构造函数连续三次 push 后以 `rsp+32` 读第一个栈参数，实际入口偏移是 8，调试表达式却为 `fbreg 32`。因此只有 CFI 覆盖整个函数并证明 SP 基址不变时，才将该种帧基址换算为入口 SP；否则 `sp_stable=false`，位置记 `unresolved_frame_base`。非 SP 帧基址也保留未知，不猜序言建立后的帧指针。此策略会遗漏可人工证明的栈参数，但不会把序言后的偏移当成入口偏移。

**统计与证据边界。** 类型组有整数/指针、浮点、≤16 字节聚合、>16 字节聚合、含浮点成员聚合，后者与大小组重叠。`observed_stack` 仅统计确实换算出的栈位置，其分母不含帧基址未解决项；它不是独立计算的“寄存器耗尽”总体。调试位置本身不能区分寄存器耗尽与聚合的强制内存传递，因此不将两者自动等同。受控的高参数数目用例仍需补充。

该证据可核对 C 层形参顺序、大小、嵌套成员布局和有正面位置证据的寄存器/位片/间接存储/入口栈偏移。不能单凭它确认未使用参数、聚合未报告字节、栈帧不稳定项、返回位置、隐藏返回参数、寄存器扩展位、调用者传参动作或所有 ABI 边界。DWARF 不完整，不能按未知项判定分类器错误。当前语料在形参方面的缺口：受控用例里按值传递的小聚合只有两个，没有超过 16 字节的聚合、含浮点成员的聚合，也没有寄存器用尽后落到栈上的形参；窄整数与布尔没有被单独消费的用例。补语料时各加一组，并让每个成员、每个末尾形参都被用到。
