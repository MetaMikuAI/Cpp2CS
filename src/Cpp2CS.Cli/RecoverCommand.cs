using Cpp2CS.Pipeline;

namespace Cpp2CS.Cli;

internal static class RecoverCommand
{
    public static int Run(string binary, string metadata, string output, string[] options)
    {
        var request = RecoveryRequest.Parse(binary, metadata, output, options);
        if (!request.HasScope)
        {
            Console.Error.WriteLine("必须且只能指定一种恢复范围：--all、--assemblies、--namespaces 或 --methods。");
            return 2;
        }
        var result = RecoverySession.Run(request, Console.Error.WriteLine);
        Console.Write(result.Report);
        return 0;
    }
}
