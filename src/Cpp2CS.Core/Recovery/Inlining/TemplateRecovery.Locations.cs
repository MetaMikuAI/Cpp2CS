using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Inlining;

internal sealed partial class TemplateRecovery
{
    private static bool MayAlias(ManagedValue a, ManagedValue b) => MemoryFootprint.MayAlias(
        MemoryFootprint.Of(a, Unobserve), MemoryFootprint.Of(b, Unobserve));

    private static ManagedValue Unobserve(ManagedValue value) => value is Observed observed ? Unobserve(observed.Read) : value;

    /// <summary>项是否读取了可能与 location 共享存储的位置（包括作为接收者的读取）。</summary>
    private static bool ReadsLocation(ManagedValue value, ManagedValue location) => value switch
    {
        Observed observed => MayAlias(observed.Read, location) || ReadsLocation(observed.Read, location),
        Returned => false,
        _ => ManagedValues.Children(value).Any(child => ReadsLocation(child, location)),
    };
}
