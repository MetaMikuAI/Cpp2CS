using System.Diagnostics;
using System.Text.Json;
using Cpp2CS.Native;

public static class RecoveryProfile
{
    public static void Run(string configuration, ulong address)
    {
        var timer = Stopwatch.StartNew();
        void Phase(ulong method, string phase)
        {
            Console.WriteLine(JsonSerializer.Serialize(new { address = $"0x{method:x}", phase, elapsedMilliseconds = timer.ElapsedMilliseconds }));
            Console.Out.Flush();
        }
        Phase(address, "session");
        using var session = new RecoverySession(JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!) { PhaseStarted = Phase };
        var result = session.Recover(address);
        Phase(address, "render");
        var text = session.Render(result);
        Phase(address, "complete");
        Console.WriteLine(JsonSerializer.Serialize(new { result.RecoveryPath, result.Problems, characters = text.Length }));
    }
}
