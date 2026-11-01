using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class DescribePass
{
    internal static string Describe(Call call)
    {
        var text = call.ToString();
        return text.Length > 300 ? text[..300] : text;
    }
}
