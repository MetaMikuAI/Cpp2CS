
namespace Cpp2CS.Managed;

/// <summary>稳定诊断编码的类别；分类不依赖原因文本。</summary>
internal static class RecoveryCategories
{
    public static string Of(string code) => code switch
    {
        "recovery.CompareExchangeReference" or "recovery.CreateDelegate" or "recovery.DelegateAllocation" => "call",
        "recovery.Allocations" => "construction",
        "recovery.Build" or "recovery.Check" or "recovery.Edge" or "recovery.Invocation" or "recovery.Translate" or "recovery.TranslateCall" => "control-flow",
        "recovery.BuildExceptionBody" or "recovery.ExceptionCopies" or "recovery.ExceptionEdge" or "recovery.RouteExceptionSources" => "exception",
        "recovery.BoxFrame" or "recovery.FrameSlots" or "recovery.ProveFrameInitialization" => "frame",
        "recovery.LowerSharedValues" or "recovery.SharedAddress" or "recovery.SharedValue" => "generic",
        "recovery.ArrayElementCheck" or "recovery.ArrayStructLocation" or "recovery.FrameLocation" or "recovery.Index" or "recovery.Location" or "recovery.StructAddress" => "memory",
        "recovery.Prepare" => "signature",
        "recovery.Compose" or "recovery.DefineFragment" or "recovery.IndirectInvocation" or "recovery.InsertedFragment" or "recovery.Pack" or "recovery.ProveReturnBuffer" or "recovery.RegisterStructArgument" or "recovery.Run" or "recovery.Slice" or "recovery.StructReturn" => "struct",
        "recovery.Binary" or "recovery.CheckFloatingConstructorOrder" or "recovery.Coerce" or "recovery.Comparison" or "recovery.Conversion" or "recovery.FloatingNegation" or "recovery.InferTypes" or "recovery.LocalOf" or "recovery.Recover" or "recovery.Truth" or "recovery.Variable" or "recovery.unsupported" or "recovery.variable-type" => "type",
        _ => "type",
    };
}
