using Cpp2CS.Cli;

try { return RecoverCommand.Run(args); }
catch (Exception error)
{
    // 命令边界保留完整错误；程序错误不得作为恢复成功返回。
    Console.Error.WriteLine(error);
    return 1;
}
