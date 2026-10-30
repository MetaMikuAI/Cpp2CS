
namespace Cpp2CS.Pipeline;

/// <summary>按 profile 组合核心阶段与外围扩展。</summary>
public static class RecoverySession
{
    public static RecoveryRunResult Run(RecoveryRequest request, Action<string>? progress = null)
    {
        request.Validate();
        return request.Profile == "core" ? CoreProfile.Run(request, progress) : FullProfile.Run(request, progress);
    }
}
