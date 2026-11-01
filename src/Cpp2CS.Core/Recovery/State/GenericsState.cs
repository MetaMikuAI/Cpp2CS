namespace Cpp2CS.Recovery;

/// <summary>Generics 族的证据：共享泛型的动态栈缓冲（按缓冲 Id）。</summary>
internal sealed class GenericsState
{
    internal readonly Dictionary<ulong, LocalValue> sharedBuffers = [];
}
