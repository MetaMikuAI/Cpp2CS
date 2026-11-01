
namespace Cpp2CS.Pipeline;

/// <summary>运行核心恢复流程。</summary>
public static class RecoverySession
{
    public static RecoveryRunResult Run(RecoveryRequest request, Action<string>? progress = null)
    {
        request.Validate();
        return CoreProfile.Run(request, progress);
    }
}
