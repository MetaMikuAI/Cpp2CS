using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Facts.Derived;

internal sealed partial class NativeMethodFacts
{
    internal readonly Dictionary<TypeRef, MethodDef[]> conversionCopies = [];
    internal readonly Dictionary<ulong, MethodRef?> nativeConversions = [];
    internal ILookup<ulong, MethodDef>? nativeConversionCandidates;

    internal MethodRef? NativeConversion(ulong target)
    {
        if (nativeConversions.TryGetValue(target, out var known)) return known;
        MethodRef? result = null;
        if (facts.EntriesAt(target).Length == 0 && facts.Unregistered.At(target) is null
            && facts.Code.At(target) is { Region: CodeRegion.Managed } copy && copy.Start == target)
        {
            // 静态运算符的实参可由向量计算生成，未必完整转传入口参数；用完整机器码确定唯一身份。
            nativeConversionCandidates ??= facts.Model.Methods.Where(m => m.IsStatic && m.Address != 0
                && m.Owner.GenericParameters.Count == 0 && m.GenericParameters.Count == 0
                && m.Name is "op_Implicit" or "op_Explicit" && m.Parameters.Count == 1
                && facts.Code.At(m.Address) is { Region: CodeRegion.Managed } original && original.Start == m.Address
                && facts.EntriesAt(m.Address).Select(e => e.Method?.Method).Distinct().Count() == 1)
                .ToLookup(m => facts.Code.At(m.Address)!.Size);
            var matches = nativeConversionCandidates[copy.Size]
                .Where(m => NativeCopy.Equal(copy, facts.Code.At(m.Address)!, facts.Code.Word)).Take(2).ToArray();
            if (matches is [var only]) result = new(only, [], []);
        }
        return nativeConversions[target] = result;
    }

    internal MethodDef[] ConversionCandidates(TypeRef input)
    {
        if (!conversionCopies.TryGetValue(input, out var candidates))
            conversionCopies[input] = candidates = facts.Model.Methods.Where(m => m.IsStatic && m.Address != 0
                && m.Owner.GenericParameters.Count == 0 && m.GenericParameters.Count == 0
                && m.Name is "op_Implicit" or "op_Explicit" && m.Parameters is [{ Type: var parameter }] && parameter.Equals(input)).ToArray();
        return candidates;
    }
}
