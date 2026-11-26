# 输入层的规范导出与比较

新读取器的入口是 `Il2CppInput.Load(elf, metadata)`。读入 Unity 2022.3 的 LP64 ELF 和 v31 元数据，结果包含 ELF 映像、托管模型和使用 RVA 的代码地图。ELF 层公开的符号值、段地址、重定位位置和字段来源地址均使用链接虚拟地址。`Elf64.FileOffset` 只对文件实际覆盖的范围给出偏移。

## 用法

导出与比较都是重任务，按本机约定加锁。以下变量由调用方给出，输出与差异文件放入被忽略的本地产物目录。

```sh
dotnet build tools/CanonicalExport -c Release -nodeReuse:false -m:1
dotnet tools/CanonicalExport/bin/Release/net10.0/CanonicalExport.dll "$ELF" "$METADATA" "$NEW_JSONL" "$FIELD_SOURCES"
python3 tools/CanonicalExport/compare.py "$REFERENCE_JSONL" "$NEW_JSONL" "$DIFFERENCES"
```

`REFERENCE_JSONL` 是另一个读取器按本文格式写出的导出，用作对照答案。

字段来源文件可省略。提供时，每个字段带上下标、所有者泛型参数数、注册槽虚拟地址、文件偏移、原始有符号 32 位值。地址与文件偏移用十六进制；零填充段只有虚拟地址；无注册槽时三个来源列为空。

## 身份与编码

- 每行一个 UTF-8 JSON 对象，属性名按序数排列。数据行按种类及数值下标递增，末行为汇总。共享入口、重复内容、没有入口的方法规格均保留独立的表下标。
- `Dk` 表示全局类型定义下标 k。`Dk<T,U>` 的实参有序。类型参数为 `!Dk.p`，方法参数为 `!!Mk.p`，k 是所有者定义下标，p 是声明中的位置。`T[]` 是向量，`T[n]` 是秩为 n 的 ARRAY，`T*` 与 `T&` 分别表示非托管指针与托管引用。
- 方法签名依次写返回类型、一个反引号、泛型参数数、括号内逗号分隔的参数类型。方法实例 `Mk<A,B><C>` 依次写定义下标、类实参、方法实参；空实参表写 `<>`。
- `image` 的类型区间左闭右开。`field` 同时给出全局字段下标和所属类型内的序号。实例偏移对引用类型以对象起点为基准，对值类型以未装箱数据起点为基准。静态与线程静态分别以各自的数据区起点为基准。常量及未知偏移写 null。
- 方法与实例的 `entry` 为十进制 RVA，无代码写 null。`invoker` 为调用器表序号，`invoker` 行给出有入口的槽及其 RVA。`registration` 给出两个注册结构的 RVA。`runtime-type` 保留注册类型表的每个位置。
- 字符串内容以 UTF-8 编码计算 SHA-256，用大写十六进制表示。元数据名和字面量分别按终止符和显式长度读取。汇总统计各数据种类，汇总行自身单列比较。
- 比较器校验主键顺序、唯一性、列集合与汇总。按键归并时比较整行字节，额外行、缺行及同键异值各记一处差异。差异文件保留两侧原对象，缺失侧写 null。退出码 0 表示全部一致，1 表示存在差异。输入格式无效时报错。

## 依据

v31 元数据表的行布局来自 `vm/GlobalMetadataFileInternals.h`。注册结构来自 `il2cpp-class-internals.h`，类型与泛型实例来自 `il2cpp-runtime-metadata.h`。普通方法入口由模块与 token RID 索引，泛型入口和调用器由 `Il2CppGenericMethodFunctionsDefinitions` 索引。字段注册值由 `vm/GlobalMetadata.cpp` 的 `GetFieldOffset` 读取，线程静态标志的解释见 `vm/MetadataCache.cpp` 的 `GetFieldOffsetFromIndexLocked`，泛型实例的布局见 `vm/Class.cpp` 的 `LayoutFieldsLocked`。
