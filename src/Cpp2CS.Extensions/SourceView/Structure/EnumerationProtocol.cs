
namespace Cpp2CS.Extensions.SourceView;

public sealed record EnumeratorShape(bool Disposable, bool? Reference, bool NonGeneric);

/// <summary>枚举器的类型协议；循环路径与清理时序仍须由各 IR 的适配层证明。</summary>
public static class EnumerationProtocol
{
    public static EnumeratorShape Describe(string name, IEnumerable<string> bases, bool? reference) =>
        new(bases.Contains("System.IDisposable", StringComparer.Ordinal), reference, name == "System.Collections.IEnumerator");

    public static bool IteratorMoveNext(MethodDef method) => method is { Name: "MoveNext", IsStatic: false, Parameters.Count: 0 }
        && method.Owner.Interfaces.OfType<DefinitionRef>().Any(t => t.Definition.FullName == "System.Collections.IEnumerator")
        && method.Owner.CustomAttributes.Any(a => a.Constructor.Owner.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute");

    public static bool IteratorDispose(MethodDef method, TypeDef owner) => method.Owner == owner
        && method.Name == "System.IDisposable.Dispose" && !method.IsStatic && method.Parameters.Count == 0;
}
