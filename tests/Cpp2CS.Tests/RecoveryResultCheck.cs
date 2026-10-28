using Cpp2CS.Recovery;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Tests;

internal static class RecoveryResultCheck
{
    [Command("recovery-result", "恢复阻塞保留因果信息，后续转换不执行；不匹配仍为成功空值", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var failure = new RecoveryFailure(0x100, "证据缺失", Code: "test.missing");
        RecoveryResult<int> blocked = failure;
        var calls = 0;
        var mapped = blocked.Map(value => { calls++; return value + 1; })
            .Bind<int>(value => { calls++; return value + 1; });
        a.True(!mapped.TryGet(out _, out var cause) && ReferenceEquals(cause, failure), "失败与原始证据保持一致");
        a.Equal(0, calls, "失败后不运行转换");
        RecoveryResult<ManagedValue?> noMatch = (ManagedValue?)null;
        a.True(noMatch.TryGet(out var absent, out _) && absent is null, "未匹配是成功空值");
        RecoveryResult<int> success = 2;
        a.True(success.Map(value => value * 3).TryGet(out var value, out _) && value == 6, "成功转换");
        return a.Finish("recovery-result");
    }
}
