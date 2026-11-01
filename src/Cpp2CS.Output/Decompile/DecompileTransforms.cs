using ICSharpCode.Decompiler.CSharp;

namespace Cpp2CS.Output;

public enum DecompilePosition { BeforeLegality, AfterLegality, AfterEvents }

/// <summary>在固定位置注册可选的 ILSpy 可读性变换。</summary>
public interface IDecompileTransformProvider
{
    void Register(CSharpDecompiler decompiler, DecompilePosition position);
}
