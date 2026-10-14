using Cpp2CS.Abi;

namespace Cpp2CS.Native;

// 逻辑参数与机器载体分开：间接聚合的载体是地址，逻辑值仍是完整聚合。
public sealed record NativeArgument(int Index, NativeParameter Parameter, AbiValue Storage)
{
    public int ValueWidth => checked(Storage.Shape.Size * 8);
    public int CarrierWidth => Storage.Indirect ? 64 : ValueWidth;
    public string CarrierType => Storage.Indirect ? Parameter.Type + "*" : Parameter.Type;
}

public sealed record NativeInterface(NativeMethod Method, CallLayout Layout, NativeArgument[] Arguments)
{
    public static string StorageName(int index) => "parameter_storage_" + index;
    public static NativeInterface? Describe(NativeMethod method, NativeAbi abi)
    {
        method = abi.Normalize(method);
        return abi.Classify(method) is { } layout
            ? new(method, layout, method.Parameters.Select((p, i) => new NativeArgument(i, p, layout.Arguments[i])).ToArray())
            : null;
    }
}
