using Cpp2CS.Tools.LiftCheck;

if (args is ["format"])
{
    // 从已有指令字频表重新核对文本，无需再提升全部函数。
    while (Console.ReadLine() is { } line)
    {
        var fields = line.Split('\t');
        uint word = Convert.ToUInt32(fields[0], 16);
        Console.WriteLine($"{fields[0]}\t{fields[1]}\t{Cpp2CS.Target.AssemblyText.Format(Cpp2CS.Target.Decoder.Decode(word), 0x100000000)}");
    }
    return;
}

if (args.Length < 4) throw new ArgumentException("用法：scan ELF 元数据 输出前缀；check ELF 元数据 输出前缀 抽样数 [Unicorn库 Capstone库]。抽样数 0 表示全量");
var scan = new Scan(args[1], args[2], args[3]);
switch (args[0])
{
    case "scan" when args.Length == 4: scan.Inventory(); break;
    case "scan" when args.Length == 6: scan.Inventory(Convert.ToUInt64(args[4], 16), Convert.ToUInt64(args[5], 16)); break;
    case "layouts" when args.Length == 4: scan.Layouts(); break;
    case "branches": BranchSurvey.Write(scan, args[3]); break;
    case "step": case "inspect": case "check":
        NativeApi.Load(args.ElementAtOrDefault(5) ?? Environment.GetEnvironmentVariable("UNICORN_LIBRARY") ?? "libunicorn.so.2",
            args.ElementAtOrDefault(6) ?? Environment.GetEnvironmentVariable("CAPSTONE_LIBRARY") ?? "libcapstone.so.5");
        NativeApi.uc_version(out uint major, out _);
        if (major != 2) throw new InvalidDataException("需要 Unicorn 2");
        if (args[0] == "step")
        {
            InstructionCheck.Run(scan, args[3]);
            break;
        }
        if (args[0] == "inspect")
        {
            Execution.Inspect(scan, args[3], Convert.ToUInt64(args[4], 16), ulong.Parse(args[7]));
            break;
        }
        var options = args.Skip(7).ToArray();
        ulong from = 0, until = ulong.MaxValue;
        if (options is [.., "--range", var first, var last])
        {
            from = Convert.ToUInt64(first, 16); until = Convert.ToUInt64(last, 16);
            options = options[..^3];
        }
        string? newSnapshots = null;
        if (options is [.., "--new-snapshots", var previousLift]) { newSnapshots = previousLift; options = options[..^2]; }
        string? baseline = null;
        if (options is [.., "--new-tables", var inventory]) { baseline = inventory; options = options[..^2]; }
        if (options.Length > 1) throw new ArgumentException("check 的可选参数是历史执行清单、--new-tables 清单、--new-snapshots 清单、--range 起点 终点");
        Execution.Check(scan, args[3], int.Parse(args[4]), options.FirstOrDefault(), baseline, newSnapshots, from, until); break;
    default: throw new ArgumentException("未知核对模式");
}
