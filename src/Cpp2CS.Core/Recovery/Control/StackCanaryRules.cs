namespace Cpp2CS.Recovery;

internal static class StackCanaryRules
{
    /// <summary>栈保护识别；调用的栈实参范围由托管调用帧给出。</summary>
    [Step("control.stack-canary", StepPhase.Prepare, StepKind.Rewrite)]
    internal static void RecognizeStackCanary(RecoveryScope scope, PreparedMethod prepared) =>
        StackCanaryRecognition.Run(scope.function, extent: new ManagedCallFrames(scope.facts, prepared.Abi).ArgumentSize);
}
