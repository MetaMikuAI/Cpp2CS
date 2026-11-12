# 运行时布局

布局由 libclang 18.1.1 按目标三元组计算；生成器不计算结构填充，不保存手写偏移。头文件通过参数传入，不入库。本节的布局范围是 C 兼容的运行时声明；函数目录与操作登记表见末节。

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

## 运行时函数目录与操作登记表

Unity 目录为 `functions-unity-2022.3.62f2-android-{arm64,x64}.json`。`RuntimeFunctionCatalog.Load/Read` 精确匹配版本、目标和数据模型；不跨版本回退。系统目录 `functions-system-android-lp64.json` 单独声明 bionic、LP64 和两个 Android 三元组，不依赖 Unity 版本。`LoadWithSystem` 显式接收两份文件并合并，拒绝目标不匹配与符号冲突。没有修改 `RuntimeSpec` 或添加二进制识别。

`RuntimeOperations.All` 是语义的唯一来源。输入记录用途与种类；结果关系封闭为无关系、恒等于输入、输入或空。`ReturnInput` 只投影恒等关系。`IsInstance` 用输入或空，`CastClass` 用恒等；`UnboxAny` 返回盒内或缓冲区地址，不登记恒等。

`MemoryBarrier` 无输入、无结果、不访问托管堆；它只约束多线程内存次序，在单线程语义下不可观察，由结构还原消去。

指针范围封闭为固定字节、一个指针槽、类输入的值大小、整数输入的长度乘元素字节数、不定。条件封闭为总是、正常返回、异常退出、状态尚未建立、其他；其他条件必须保留说明，消费者不能把它当成已证明的条件。范围与条件的文字仅作说明。`EventCondition` 为空表示没有事件。`memcpy`、`memmove`、`memset` 以 `length` 字节记录访问，返回值恒等于 `destination`；整体无额外堆改写不取消这些显式读写。地址属于帧、托管堆或原生区域仍由位置查询判定。

后置条件包含具名谓词、条件、说明与状态表示。类构造重入不保证完成标志；公开类布局初始化入口断言不处于布局重入；正常返回建立就绪事实。空 RGCTX 集合允许指针为空，非空数据指针是幂等消去的充分凭据，不能把空数据误判为失败。匿名元数据槽仍要求全局访问凭据。beforefieldinit 的事件时机与堆改写分开，必须有类型元数据证明才能选择对应操作。

效果依据针对 Unity 2022.3 的 Android LP64、线程化 Boehm GC 与匹配基础库，不外推至其他配置。函数级链保存在登记项 `Evidence`，当前线程是否运行托管代码另有 `SynchronousManagedCode`。`Class::Init` 建立布局，不执行输入类静态构造；`Runtime::ClassInit` 调用静态构造。对象分配与装箱会走后者，数组不会。分配触发的终结器由 `gc/BoehmGC.cpp` 的 finalize-on-demand 与 `gc/GarbageCollector.cpp: NotifyFinalizers / FinalizerThread` 转到其他线程，不算本次调用同步执行任意托管代码。

`vm/Exception.cpp: FromNameMsg` 经 `Object::New`、`Runtime::ObjectInit` 调用基础库异常构造；不能把它说成完全没有托管执行。匹配基础库的异常构造经 `SystemException`、`Exception.Init` 只写新对象，但 `Exception` 静态构造可初始化静态锁，因此错误路径仍登记可能改写。缓存异常经 `PrepareExceptionForThrow` 还可补写既有异常堆栈。依据为对应生成 C++ 的基础库 `Exception`、`SystemException`、`ArithmeticException`、`MemberAccessException`、`SafeSerializationManager` 构造及 `Environment.GetResourceString`，不按其符号或地址做识别。原生分配耗尽、内存损坏与自定义 profiler 回调不在此配置的精确结论内；改变这些配置必须重新核对。

静态构造失败被 `Runtime::ClassInit` 包装成 `TypeInitializationException`，布局失败缓存为 `TypeLoadException`；泛型类型深度失败由 `vm/GenericClass.cpp: CreateClass` 经 `GetMaximumNestedGenericsException` 抛 `NotSupportedException`。泛型方法查找只安装失败桩，不能把将来执行桩的异常算在当前查找上。接口查找仍保留任意异常上界：`vm/ClassInlines.cpp` 的对象慢路径可以进入 `RCW::GetComInterfaceInvokeData`，进而调用外部 `QueryInterface`，外部代码和回调没有封闭摘要。目录没有按 Android 常见对象形态擅自删掉此分支。

重新生成仍使用布局节的 Python 环境和原始声明头文件：

```sh
"$LAYOUT_VENV/bin/python" spec/gen/generate_catalog.py --runtime-headers "$RUNTIME_HEADERS" --unity 2022.3.62f2 --target android-arm64 --output spec/functions-unity-2022.3.62f2-android-arm64.json
"$LAYOUT_VENV/bin/python" spec/gen/generate_catalog.py --runtime-headers "$RUNTIME_HEADERS" --unity 2022.3.62f2 --target android-x64 --output spec/functions-unity-2022.3.62f2-android-x64.json
"$LAYOUT_VENV/bin/python" spec/gen/selfcheck_catalog.py
```

`spec/gen/runtime-functions.json` 手写函数到操作的对应；libclang 计算 C 原型与 Itanium 修饰名。原始声明来自头文件包的 `vm-utils/ClassInlines.h`；完整实现包将此头文件放在 `vm/ClassInlines.h`，两个包的 codegen 头文件、实现与 ClassInlines 头文件逐字节相同；声明与实现依据分别记录，不伪造声明来源。系统原型手写，依据为 ISO C11 N1570 的 memcpy、memmove、memset、abort、exit，Itanium C++ ABI 的 `_Unwind_Resume`、`__cxa_begin_catch`、`__cxa_end_catch`，ISO C++ 的 `std::terminate` 及 LSB/bionic 的 `__stack_chk_fail`。

JSON 的 `schema_version` 为 1。函数项含原始声明及位置、C 原型、参数类型与名称、操作名、按形参次序的输入名、结果处理、依据与识别空位。每个形参都必须映射到一个操作输入，本目录没有未使用形参，不提供静默丢弃的退路。`result` 为 `operation`、`discard`、`void`；前者返回操作结果，中者包装函数丢弃结果，后者操作本身无结果。系统项以 `recognition.import` 记录精确导入名，其他识别线索仍留空。不支持的 C 类型保留诊断，`RequireSignature` 明确失败。

快速检查 `runtime-catalog` 核对形参完整对应、指针输入用途、范围输入类型和结果关系种类。定向检查 `runtime-catalog-truth` 读取 `CPP2CS_CORPUS_TRUTH`；未配置则明确跳过。调用审计默认从同级 `-inline` 目录读取，也可用 `CPP2CS_CORPUS_INLINE_TRUTH` 指定。系统导入存在性按函数真值中 `defined=false` 核对，不把静态链接符号当作导入。

覆盖保留用例统计，并增加全语料统计：以 `mappings.json` 中 `method_id` 非空的所有角色目标地址作为托管映射集合（包括泛型、调整桩和调用器），按地址合并别名，选取调用审计中对应的全部函数；按调用指令地址去重，包含直接尾调用。目标地址及全部别名均不属于任何托管映射时，归为运行时/系统候选；不依赖名称前缀判定。任一同址符号在目录即覆盖。报告映射函数数、审计函数数和缺少审计数，缺少审计的函数不伪造零调用，并使完整性检查失败。`method_id` 为空的运行时合成入口不冒充托管方法；它们若被直接调用仍计入运行时候选。未收目标按调用点次数降序列前五十，名称分类仅用于报告，不能作为恢复识别依据。间接调用、无审计函数及没有独立符号的内联均不进入该直接调用覆盖率。

## 运行时参考形状

`shapes-*.json` 按精确 Unity 版本、目标三元组与数据模型选择。离线生成器通过同一次构建的符号确定目录函数身份，输出中只保存目录名称、范围长度、地址无关的完整原生 IR 形状及按首次调用顺序排列的直接被调形状，不保存原生地址。缺失项单独记录函数与原因；参考映像及符号文件的 SHA-256 记录生成来源。

```sh
dotnet run --project src/Cpp2CS.Cli -- runtime-shapes "$REFERENCE_IMAGE" "$REFERENCE_SYMBOLS" "$OUTPUT_JSON"
```

范围长度只筛选候选；控制流、运算、常量、映像引用相等关系和调用目标相等关系必须逐项相同。根函数的全部直接被调形状必须存在并相同；被调节点的子关系只在其全部直接被调均可完整提升时附加，生成预算止于根的第二层被调，未附加的关系不作为身份依据。全部附加形状也必须逐项相同；参考中已知的目录调用关系不得与目标中的唯一定位冲突。没有内部调用或具名导入调用印证的叶子不定位；多个入口通过复核时不定位；未知项、无法提升和未归一的异常匹配数据不能成为依据。间接目标按完整项表示进入形状，不含未知项或未定义位；间接调用本身不冒充直接调用印证。形状是编译器剖面的识别数据，不是代码变换的等价证明。前端的 IR 表示变化后须重新生成并跑无符号语料核对。版本与目标只用于选择数据，不代表编译配置兼容；更换优化级别、内联或链接配置后，须以对应参考构建重新生成并核对。

参考分析可显式提升全读写屏障和 acquire/release 访问；其顺序属性及观察域进入形状，不能当作普通访问或忽略。普通恢复未启用该词汇，继续报洞。编码与顺序语义依据 [Arm DDI0602](https://support.arm.com/documentation/ddi0602/2022-09/Base-Instructions/DMB--Data-Memory-Barrier-) 和 [Arm 内存系统指南](https://support.arm.com/documentation/102336/0101/Load-Acquire-and-Store-Release-instructions)。

语料核对使用 `runtime-locate-nosymbols-corpus`：先在没有函数符号输入的事实中定位，再读取符号真值逐项核对，报告加权调用覆盖与未定位原因。`pipeline-corpus-nosymbols` 与 `pipeline-corpus` 复用恢复与执行对照，分别写入各自的本地产物目录。两种检查均使用 `CPP2CS_CORPUS` 和 `CPP2CS_CORPUS_TRUTH`，定位错误或执行对照不一致均使检查失败。
