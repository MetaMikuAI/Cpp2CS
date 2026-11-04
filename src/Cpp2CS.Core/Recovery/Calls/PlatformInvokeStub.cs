using CallingConvention = System.Runtime.InteropServices.CallingConvention;
using CharSet = System.Runtime.InteropServices.CharSet;
using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Storage;

namespace Cpp2CS.Recovery.Calls;

/// <summary>
/// extern 方法的原生入口是 IL2CPP 生成的 P/Invoke 桩：第一次调用时用栈上的 PInvokeArguments 解析函数指针，缓存后转发。
/// 元数据不含 DllImport 的库名与入口，只能从描述符读取：
/// moduleName（指针、长度）、entryPoint（指针、长度）、callingConvention、charSet、parameterSize、isNoMangle。
/// 两个字符串的长度与内容一致才算认出描述符。
/// </summary>
internal static class PlatformInvokeStub
{
    private const int ModuleField = 0, ModuleLength = 8, EntryField = 16, EntryLength = 24, ConventionField = 32, CharacterField = 36, NoMangleField = 44;

    public static NativeImport? Read(MachineFunction function, ImageDocument image, IFrameCallEffects effects)
    {
        var model = new FrameModel(function, effects);
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call { Arguments: [var first, ..] } && model.Slot(first) is { } descriptor
                    && Describe(model, block, i, descriptor, image) is { } import) return import;
        return null;
    }

    private static NativeImport? Describe(FrameModel model, Block block, int index, long descriptor, ImageDocument image)
    {
        ulong? Field(int offset, int width)
        {
            var reach = model.Reach(block, index, descriptor + offset, width / 8);
            if (!reach.Complete) return null;
            var values = reach.Stores.Select(s => model.Slot(s.Target) is { } start
                ? Fold.Extract(s.Value, checked((int)(descriptor + offset - start) * 8), width) as Const : null).Distinct().ToArray();
            return values is [{ } value] ? value.Value : null;
        }
        string? Text(int pointer, int length) => Field(pointer, 64) is { } address && Field(length, 64) is { } size
            && RuntimeHelpers.CString(image, address) is { } text && (ulong)text.Length == size ? text : null;
        if (Text(ModuleField, ModuleLength) is not { } library || Text(EntryField, EntryLength) is not { } entry) return null;
        if (Convention(Field(ConventionField, 32)) is not { } convention || Characters(Field(CharacterField, 32)) is not { } characters) return null;
        return new NativeImport(library, entry) { CallingConvention = convention, CharSet = characters, ExactSpelling = Field(NoMangleField, 8) is not (null or 0) };
    }

    /// <summary>Il2CppCallConvention。</summary>
    private static CallingConvention? Convention(ulong? value) => value switch
    {
        0 => CallingConvention.Winapi,
        1 => CallingConvention.Cdecl,
        2 => CallingConvention.StdCall,
        3 => CallingConvention.ThisCall,
        4 => CallingConvention.FastCall,
        _ => null,
    };

    /// <summary>Il2CppCharSet。</summary>
    private static CharSet? Characters(ulong? value) => value switch
    {
        0 => CharSet.Ansi,
        1 => CharSet.Unicode,
        2 => CharSet.None,
        _ => null,
    };
}
