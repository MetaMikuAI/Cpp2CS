using System.Text;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.RuntimeFunctions;

public static class InternalCallNames
{
    /// <summary>只读、无重定位的零结尾串；完整签名存在时逐项核对，不把同名重载混为一谈。</summary>
    public static bool Matches(QueryContext c, StateQueries state, IImage image, Term value, MethodRef method)
    {
        var resolved = c.Get(state.Resolve, value);
        var location = resolved.IsSuccess ? c.Get(state.Locations, new(resolved.Value, 8)) : default;
        if (!location.IsSuccess || location.Value is not { Region: Region.Image, Offset: { } offset } || offset < 0 || offset > ulong.MaxValue) return false;
        ulong address = (ulong)offset; var info = image.Query(address);
        if (info.Writable || info.Storage != StorageKind.FileContent) return false;
        int length = checked((int)Math.Min(info.AvailableBytes, 4096)); var bytes = new byte[length]; image.ReadBytes(address, bytes);
        int end = Array.IndexOf(bytes, (byte)0);
        if (end < 0 || image.HasRelocation(address, (ulong)end + 1)) return false;
        string name = Encoding.UTF8.GetString(bytes, 0, end);
        string shortName = method.Method.Owner.FullName + "::" + method.Method.Name;
        // vm/InternalCalls.cpp: 先查完整名字，失败时才去掉括号及参数表；短名只在包装已给出定义时使用。
        return name == shortName || name == shortName + "(" + string.Join(",", method.Method.Parameters.Select(p => TypeName(method.Concrete(p.Type)))) + ")";
    }
    private static string TypeName(TypeRef type) => type switch
    {
        DefinitionRef { Arguments.Count: 0 } definition => definition.Definition.FullName,
        ByRefRef byref => TypeName(byref.Element) + "&",
        PointerRef pointer => TypeName(pointer.Element) + "*",
        ArrayRef array => TypeName(array.Element) + "[" + new string(',', array.Rank - 1) + "]",
        _ => type.ToString()!,
    };
}
