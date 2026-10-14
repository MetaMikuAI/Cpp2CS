using Cpp2CS.Abi;
using Cpp2CS.Model;

namespace Cpp2CS.Native;

public sealed class NativeAbi(HeaderLayout layouts, ManagedNames managed)
{
    public ManagedNames Managed => managed;
    public string? MutableReceiverType(NativeMethod method) =>
        method.Parameters.FirstOrDefault() is { Name: "__this", Type: var type } &&
        managed.BaseTypeOf(method.Name.Split("$$")[0]) is "System.ValueType" or "System.Enum" ? type.TrimEnd('*') : null;
    public NativeMethod Normalize(NativeMethod method)
    {
        if (method.Parameters.FirstOrDefault() is { Name: "__this" } receiver && !receiver.Type.EndsWith('*') &&
            managed.BaseTypeOf(method.Name.Split("$$")[0]) is "System.ValueType" or "System.Enum")
            return method with { Parameters = method.Parameters.Select((p, i) => i == 0 ? p with { Type = p.Type + "*" } : p).ToArray() };
        return method;
    }
    public CallLayout? Classify(NativeMethod method)
    {
        method = Normalize(method);
        return Aapcs64.Classify(new(new(method.Parameters.Select(p => layouts.Shape(p.Type))), layouts.Shape(method.ReturnType),
            new(EvidenceKind.Derived, "Clang AArch64 layout; managed value-type instance is an unboxed address"))).Layout;
    }
}
