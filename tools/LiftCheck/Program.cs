using Cpp2CS.Tools.LiftCheck;

if (args.Length < 4) throw new ArgumentException("用法：scan ELF 元数据 输出前缀；check ELF 元数据 输出前缀 抽样数 [Unicorn库 Capstone库]。抽样数 0 表示全量");
var scan = new Scan(args[1], args[2], args[3]);
switch (args[0])
{
    case "scan" when args.Length == 4: scan.Inventory(); break;
    case "scan" when args.Length == 6: scan.Inventory(Convert.ToUInt64(args[4], 16), Convert.ToUInt64(args[5], 16)); break;
    case "check":
        NativeApi.Load(args.ElementAtOrDefault(5) ?? Environment.GetEnvironmentVariable("UNICORN_LIBRARY") ?? "libunicorn.so.2",
            args.ElementAtOrDefault(6) ?? Environment.GetEnvironmentVariable("CAPSTONE_LIBRARY") ?? "libcapstone.so.5");
        NativeApi.uc_version(out uint major, out _);
        if (major != 2) throw new InvalidDataException("需要 Unicorn 2");
        Execution.Check(scan, args[3], int.Parse(args[4])); break;
    default: throw new ArgumentException("未知核对模式");
}
