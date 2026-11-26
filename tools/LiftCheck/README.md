# ARM64 快照核对

`scan` 读取 ELF、元数据和代码地图，按去重的登记入口逐个构造快照。清单保存入口、FDE 起止地址和提升结果。指令字按出现次数计数，相同编码只格式化一次。运行文件使用 `*.local.*` 后缀。

`check` 从同一清单取成功入口，再逐个提升、解释和执行。抽样数为 0 时取全部，否则对已排序的成功入口用 .NET 10 的 `Random(202211).Shuffle` 无放回抽样。执行种子为 11、29、47。每个种子独立建立 CPU、寄存器和内存。每次执行上限为 2048 条原生指令或 2048 次快照块访问，耗尽预算计为失败。

```sh
flock -o /tmp/cpp2cs-heavy.lock dotnet build Cpp2CS.slnx -nodeReuse:false -m:1
flock -o /tmp/cpp2cs-heavy.lock dotnet run --no-build --project tools/LiftCheck -- scan "$elf" "$metadata" "$prefix"
flock -o /tmp/cpp2cs-heavy.lock dotnet run --no-build --project tools/LiftCheck -- check "$elf" "$metadata" "$prefix" "$count" "$unicorn" "$capstone"
flock -o /tmp/cpp2cs-heavy.lock python tools/LiftCheck/decode.py "$prefix"
flock -o /tmp/cpp2cs-heavy.lock python tools/LiftCheck/report.py "$prefix" --symbols "$symbols" --cases "$cases"
```

输出前缀的父目录须存在。单独复查一个地址区间时，可在 scan 命令末尾给出十六进制的起点和不含的终点，使用独立的输出前缀。原生库参数也可由 `UNICORN_LIBRARY`、`CAPSTONE_LIBRARY` 提供。解码核对使用 Capstone 5 的 Python 绑定；符号核对使用 pyelftools。没有符号文件或用例清单时可省略对应选项。

| 输出后缀 | 内容 |
|---|---|
| `.functions.local.tsv` | 每个登记入口的 FDE 与提升结果 |
| `.execution.local.tsv` | 每个受核对快照的结果、三个种子合计到达的不同出口数、全部出口数 |
| `.failures.local.tsv` | 各失败种子的类别、首个不同事件的序号与两侧值 |
| `.differences.local.tsv` | 每种有差异的指令字、出现数、类别及两侧文本 |
| `.unsupported.local.tsv` | 含相应未支持助记符的函数数，同一函数内去重 |
| `.ranges.local.tsv` | FDE 与符号范围的逐入口差异 |
| `.cases.local.tsv` | 用例清单映射到的各入口、提升与核对结果 |
| `.summary.local.json` | 按输入汇总的提升结果、执行结果及出口覆盖 |

两侧按链接虚拟地址读取 PT_LOAD，段内零填充与重定位均参与读取。导入符号按名称分配不同的映像外地址。未映射内存按种子与地址生成。Unicorn 按页物化数据，快照解释器按字节取数。调用事件包含目标和当前有定义的参数槽，调用结果与破坏值由种子、调用序号和寄存器决定。原生一侧用 Capstone 的写寄存器集合维护调用槽，使用 Unicorn 的访存钩子记录访问。Q 访存只在指令、方向、地址和两半位宽均吻合时重建为 128 位的架构访问。

访问、调用、返回行和结局逐项比较。任一种子失败即为该函数失败，汇总取首个失败种子的类别；失败明细保留全部种子。出口覆盖以快照的块号与出口序号去重，包含返回、陷阱和展开出口。执行只模拟正常路径。解码核对固定反汇编基址，对齐寄存器别名、整数字面值和同一位型的有符号显示后比较完整助记符和操作数。
