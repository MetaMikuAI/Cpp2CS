using System.Reflection;

namespace Cpp2CS.Model;

/// <summary>程序集身份、显式引用和常量来自全局元数据的对应表。</summary>
public sealed record AssemblyIdentity(byte[] PublicKey, byte[] Token, AssemblyFlags Flags,
    AssemblyHashAlgorithm HashAlgorithm, IReadOnlyList<int> References);

public sealed record AssemblyMetadata(IReadOnlyList<AssemblyIdentity> Identities,
    IReadOnlyDictionary<int, object?> FieldConstants, IReadOnlyDictionary<(int Method, int Sequence), object?> ParameterConstants,
    IReadOnlyDictionary<int, (ushort Pack, uint Size)> Layouts, IReadOnlyDictionary<int, byte[]> FieldData,
    IReadOnlyDictionary<(int Method, int Sequence), string> UnknownParameterDefaults);
