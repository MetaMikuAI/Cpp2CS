using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class ArrayInitializersRules
{
    // RuntimeHelpers.InitializeArray 的 FieldRVA 数据来自匹配元数据，按数组元素宽度还原常量写入。
    [InvocationRule(4)]
    internal static RecoveryResult<bool> InitializeConstantArray(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (ctx.Values.Resolve(call) is not { Method.Name: "InitializeArray", Method.Owner.FullName: "System.Runtime.CompilerServices.RuntimeHelpers" } || call.Arguments.Length < 2 || ctx.Values.Expand(call.Arguments[1]) is not Symbol { Kind: SymbolKind.Field, Value: FieldRef { Field.InitialValue: { } data } } || call.Arguments[0] is not Use array || !ctx.results.TryGetValue(array.Variable, out var allocation) || allocation.Call is not { Op: { Kind: OpKind.NewArray, Operand: ArrayRef { IsVector: true } type }, Arguments: [_, Const length] } || length.Value > 65536 || ctx.types.Kind(type.Element) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double))
            return false;
        var size = ctx.types.Size(type.Element);
        if (size is not (1 or 2 or 4 or 8) || length.Value * (ulong)size > (ulong)data.Length)
            return false;
        if (!ctx.Values.Recover(array, type).TryGet(out var target, out var failure))
            return failure;
        for (var index = 0; (ulong)index < length.Value; index++)
        {
            ulong bits = 0;
            for (var offset = 0; offset < size; offset++)
                bits |= (ulong)data[index * size + offset] << (offset * 8);
            output.Add(new ManagedStore(call.Address, new ArrayElementValue(target, new ConstantValue((ulong)index, ctx.types.Int32, 32), type.Element, size * 8), new ConstantValue(bits, type.Element, size * 8)));
        }

        return true;
    }
}
