# 运行时布局

布局由 libclang 18.1.1 按目标三元组计算；生成器不计算结构填充，不保存手写偏移。头文件通过参数传入，不入库。当前范围是 C 兼容的运行时声明，不包含运行时函数目录与操作登记表。

| 数据文件 | 目标 | 结构/联合数 | 整数常量数 |
|---|---|---:|---:|
| `unity-2022.3.62f2-android-lp64.json` | Android ARM64、x86_64 | 134 | 325 |
| `unity-2021.3.28f1-windows-x64-llp64.json` | Windows x64 | 169 | 225 |

Android 两个目标的 `records`、`constants` 逐项相同，合并为一份；各目标的基础类型大小与对齐分别保留在 `targets`，例如 `long double` 的大小可能不同，不能由 LP64 推断全部基本类型相同。

覆盖对象、类、方法、类型、数组及边界、字符串、委托、多播委托、异常、虚调用数据、RGCTXData、泛型类/实例/上下文、字段、属性、事件、映像、程序集、注册表及头文件中其余完整结构。计数包含联合，不包含嵌套匿名类型；后者保存在字段的 `members` 中。Windows 单文件头还带有元数据、快照和 `Il2CppClass_0` 等提取器辅助结构，这些不是额外的运行时对象模型。

## 数据格式

JSON 格式版本为 `schema_version: 1`，键排序、UTF-8、末尾换行，不含时间戳及输入目录的绝对路径。

- `unity_version`、`source`：声明的版本、来源类型、实际读入头文件的 SHA-256、声明适配与还原记录。真实头文件路径相对于输入根目录；单文件只记录文件名。
- `generator_version`、`generator_sha256`、`compiler`：生成器版本、实现摘要、固定的 libclang 包版本。
- `target` 或 `targets`：三元组、数据模型、语言、默认目标对齐、由编译器查询的基本类型大小/对齐。Windows 使用 clang 的 MSVC 目标布局规则。
- `records`：按 C 类型名索引，含编译器可用的 `type`、`kind`、字节 `size`、字节 `alignment`、声明顺序的 `fields`。
- 字段：`name`、相对所属结构起点的 `offset_bits`、字节 `size`、声明的 `type`。普通字段字节偏移为 `offset_bits / 8`。位域另有 `bit_width`，其 `size` 是声明类型的大小，不是占用字节数；位域存储位置由位偏移和位宽确定。
- 匿名联合的可直接访问成员展开到父字段列表，重叠偏移是正常的。具名字段内的匿名结构/联合保留 `members`，其中偏移相对该匿名类型起点。指针不会递归展开。
- 零长数组的字段大小为 0；结构 `size` 是编译器的 `sizeof`，可能含尾部填充。例如字符串字符区起点应查 `chars`，不能用结构大小代替。
- `constants`：枚举成员、整数常量以及类型、字段、方法、参数、泛型参数属性宏等。值由编译器求出，函数宏、字符串、指针常量不导出。缺项不得按 0 处理。

## 重新生成

Python 3.10 以上；虚拟环境放在仓库外。以下变量均由调用者指定，不写入生成数据。

```sh
python3 -m venv "$LAYOUT_VENV"
"$LAYOUT_VENV/bin/pip" install -r spec/gen/requirements.txt
"$LAYOUT_VENV/bin/python" spec/gen/regenerate.py --runtime-2022 "$RUNTIME_HEADERS" --single-headers "$VERSION_HEADERS"
```

最后一条命令生成两个布局文件和 `checks.json`。`RUNTIME_HEADERS` 是真实 libil2cpp 目录；`VERSION_HEADERS` 包含两个版本的 `.h` 以及 `extract.py`。需要 Git 中存在 `attempt-12`，也可通过 `--legacy-ref` 指定等价旧引用。所有编译诊断中的错误都会终止生成；共有数据出现未解释差异或旧常量不一致也会终止。最小用例使用 Python 断言，不要用 `-O` 运行 `selfcheck.py`。

单独生成一个组合：

```sh
"$LAYOUT_VENV/bin/python" spec/gen/generate.py --source "$HEADER" --unity 2021.3.28f1 --target windows-x64 --output "$OUTPUT_JSON"
```

真实目录使用 `--runtime-headers`；单文件输入默认还原已知的提取器零长数组转换。所有布局在还原声明后重新由编译器计算，不改写已生成的偏移。

核对与最小用例：

```sh
"$LAYOUT_VENV/bin/python" spec/gen/selfcheck.py
"$LAYOUT_VENV/bin/python" spec/gen/check_legacy.py spec/unity-2022.3.62f2-android-lp64.json --output "$CHECK_JSON"
"$LAYOUT_VENV/bin/python" spec/gen/verify_gcc.py --runtime-headers "$RUNTIME_HEADERS" --data spec/unity-2022.3.62f2-android-lp64.json
```

`check_legacy.py` 从 Git 解析全部 87 个常量声明，包括对象头大小的外部常量引用；`legacy-map.json` 仅保存查询名称，不保存数值。`checks.json` 保存逐项结果：一致 87、不一致 0、数据里没有 0。虚表辅助函数不是常量声明，其两项输入也已覆盖：虚表起点、槽大小和 `VirtualInvokeData.method` 偏移。

## 头文件来源核对

2022 的两种来源在两个 Android 目标上分别比较。共有 134 个结构全部纳入；共有 210 个常量逐项核对；双方独有的结构与常量分别列出，不计入一致数。详细差异路径保存在 `checks.json`。

原始单文件与真实头文件有两类差异：

1. `headers/extract.py` 为 IDA 把零长数组替换成 `[32]`。`Il2CppClass.vtable`、`Il2CppArraySize.vector`、`Il2CppString.chars` 因此增加了结构及字段大小，但偏移不变。生成器只还原这三种声明，包含提取器生成的类副本；不把任意 `[32]` 都视为零长数组。还原后重新计算的布局与真实头文件一致。
2. 三处自引用指针分别使用 `struct T` 和 typedef `T`，是同一类型的不同拼写。比较只去掉类型字符串中的 `struct` 前缀，不忽略字段、大小、对齐或位域差异。

`checks.json` 同时记录未经还原的逐项差异、还原后的比较结果及提取器 SHA-256。单文件头来自 Il2CppVersions 对 Windows Unity 安装内容的提取；该仓库 README 与 notes 解释了提取流程。不能把它等同于未经修改的原始头文件。

真实头文件目录不完整，缺少 `os/c-api` 平台配置及目标系统标准头。生成器为 C 声明提供显式 Android 配置（非 tiny、非 debugger、64 位目标、UTF-16 字符）与基于编译器内建类型的标准整数/指针类型。未替换任何运行时结构声明；对齐宏、条件结构及枚举仍由真实头文件与预处理器处理。这个适配属于生成条件，完整平台配置到位后应再次核对。

## 新版本与新目标

新版本先准备对应头文件并运行 `generate.py`，检查所需结构、枚举与属性宏是否齐全。真实头文件优先；仅有提取头时要审阅其转换规则，确认零长数组及平台 typedef，保留来源与适配记录。若有同版本两种来源，沿用共有字段逐项比较，解释所有差异。

新目标在 `TARGETS` 中增加三元组，并补充数据模型与平台适配。用 `selfcheck.py` 的打包、匿名联合、位域与 long 宽度用例验证，增加目标基础类型断言；有原生编译器时做独立核对。不能仅因同为 LP64 就合并，必须逐项比较结构与常量。


## 边界与缺口

- Windows 2021 单文件不含 `il2cpp-tabledefs.h` 属性宏；保留它已有的类型枚举和标志枚举，没有借用其他 Unity 版本补值。需要该版本头文件才能补齐这些宏。
- Windows 使用 clang 的 MSVC ABI 模型，未用 MSVC 或对应版本的完整真实头文件交叉验证。2022 对提取转换的验证支持还原方案，不能证明所有 2021 平台配置均一致。
- GCC 只用于宿主 x86_64 LP64 结构、对齐和非位域字段的交叉核对，不能证明 Android 系统 ABI 或 Windows 布局。最小用例检查三个 clang 目标的位域，但没有独立编译器的全量位域检查。
- 未编译完整生成 C++ 与内联函数；导出的是其运行时数据结构声明。没有扫描业务二进制，也没有改动 CIL 或恢复流水线。
