# ARM64 快照核对

`scan` 读取 ELF、元数据和代码地图，按去重的登记入口逐个构造快照。清单保存入口、FDE 起止地址和提升结果。指令字按出现次数计数，相同编码只格式化一次。运行文件使用 `*.local.*` 后缀。

`check` 从同一清单取成功入口，再逐个提升、解释和执行。抽样数为 0 时取全部，否则对已排序的成功入口用 .NET 10 的 `Random(202211).Shuffle` 无放回抽样。执行种子为 11、29、47、61、83。后两个种子对整数槽使用零、边界整数和普通地址，对映像外内存使用零、小长度和普通地址，向量槽亦覆盖带负载的 NaN 和有符号零。每个种子独立建立 CPU、寄存器和内存。

每侧的预算为 4096 条原生指令。解释器按块消耗实际指令数，在下一个完整块超出预算时停止；Unicorn 逐条计数，截在同一指令数。只有两侧都耗尽预算，且全部已发生事件数量、顺序和内容一致，才记为“预算内一致”。一种子的失败优先于其他种子的预算状态。

```sh
flock -o /tmp/cpp2cs-heavy.lock dotnet build Cpp2CS.slnx -nodeReuse:false -m:1
flock -o /tmp/cpp2cs-heavy.lock dotnet run --no-build --project tools/LiftCheck -- scan "$elf" "$metadata" "$prefix"
flock -o /tmp/cpp2cs-heavy.lock dotnet run --no-build --project tools/LiftCheck -- check "$elf" "$metadata" "$prefix" "$count" "$unicorn" "$capstone"
flock -o /tmp/cpp2cs-heavy.lock dotnet run --no-build --project tools/LiftCheck -- branches "$elf" "$metadata" "$prefix"
flock -o /tmp/cpp2cs-heavy.lock dotnet run --no-build --project tools/LiftCheck -- step "$elf" "$metadata" "$prefix" 0 "$unicorn" "$capstone"
flock -o /tmp/cpp2cs-heavy.lock python tools/LiftCheck/decode.py "$prefix"
flock -o /tmp/cpp2cs-heavy.lock python tools/LiftCheck/report.py "$prefix" --symbols "$symbols" --cases "$cases"
```

输出前缀的父目录须存在。单独复查一个地址区间时，可在 scan 命令末尾给出十六进制的起点和不含的终点，使用独立的输出前缀。原生库参数也可由 `UNICORN_LIBRARY`、`CAPSTONE_LIBRARY` 提供。解码核对使用 Capstone 5 的 Python 绑定；符号核对使用 pyelftools。没有符号文件或用例清单时可省略对应选项。

| 输出后缀 | 内容 |
|---|---|
| `.functions.local.tsv` | 每个登记入口的 FDE 与提升结果 |
| `.execution.local.tsv` | 每个受核对快照的结果、全部种子合计到达的不同出口数、全部出口数 |
| `.coverage.local.tsv` | 同批快照在普通种子、全部种子下的出口并集与总数 |
| `.followup.local.tsv` | 主抽样、历史入口和补测的去向；历史清单作为 check 的最后一个可选参数 |
| `.undefined.local.tsv` | 严格观察的位掩码、指令和沿实际寄存器读写链找到的来源 |
| `.branches.local.tsv` | 每个间接跳转拒绝入口、首个拒绝点、SP、LR、目标来源与索引读取形态 |
| `.executed.local.tsv` | 函数核对中 Unicorn 实际执行的扩展指令字、入口和核对结果 |
| `.steps.local.tsv` | FDE 中每个不同扩展指令字的原始位置、种子和单步核对结果 |
| `.failures.local.tsv` | 各失败种子的类别、首个不同事件的序号与两侧值 |
| `.differences.local.tsv` | 每种有差异的指令字、出现数、类别及两侧文本 |
| `.unsupported.local.tsv` | 含相应未支持助记符的函数数，同一函数内去重 |
| `.ranges.local.tsv` | FDE 与符号范围的逐入口差异 |
| `.cases.local.tsv` | 用例清单映射到的各入口、提升与核对结果 |
| `.summary.local.json` | 按输入汇总的提升结果、执行结果及出口覆盖 |

两侧按链接虚拟地址读取 PT_LOAD，段内零填充与重定位均参与读取。导入符号按名称分配不同的映像外地址。未映射内存按种子与地址生成。Unicorn 按页物化数据，快照解释器按字节取数。调用事件包含目标和当前有定义的参数槽，调用结果与破坏值由种子、调用序号和寄存器决定。原生一侧用 Capstone 的写寄存器集合维护调用槽，使用 Unicorn 的访存钩子记录访问。Q 访存只在指令、方向、地址和两半位宽均吻合时重建为 128 位的架构访问。

访问、调用、返回行和结局逐项比较。调用参数和返回行按解释器的逐位未定义掩码比较，保留槽号、位宽及所有有定义位。地址、写值、控制条件和调用目标仍要求完全有定义。任一种子失败即为该函数失败，失败明细保留全部种子。出口覆盖以快照的块号与出口序号去重，包含返回、陷阱和展开出口。执行只模拟正常路径。解码核对固定反汇编基址，对齐寄存器别名、整数字面值和同一位型的有符号显示后比较完整助记符和操作数。

间接跳转调查按可达边传播寄存器来源和入口 SP 相对的栈槽，合流取相同事实。LR 区分从保存槽重载、沿用入口值、已改写和不明。从参数或先前读取的指针作零偏移指针读取后再按正偏移取指针，记为类指针链形态。指向装入段的基址或从中取得的相对偏移可构成映像表来源。目标依赖索引读取时标记疑表。分类仅供统计。

逐指令核对从 FDE 取真实指令字，在原地址执行一条，用相同具体寄存器输入解释提升结果。比较全部整数和向量寄存器、NZCV、线程指针以及每个访存事件。它覆盖固定环境下整函数未走到的指令，结果单列。
