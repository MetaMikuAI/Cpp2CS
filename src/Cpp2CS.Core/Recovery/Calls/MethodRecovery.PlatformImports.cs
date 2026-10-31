using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using SR = System.Reflection;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    internal MethodRecoveryResult? PlatformDeclaration(MethodRef method, ulong entry)
    {
        var definition = method.Method;
        if (facts.Model.Image.Architecture != Cpp2CS.Model.Architecture.Arm64
            || (definition.Attributes & SR.MethodAttributes.PinvokeImpl) == 0 || !definition.IsStatic
            || (definition.ImplAttributes & SR.MethodImplAttributes.PreserveSig) == 0
            || method.TypeArguments.Count != 0 || method.MethodArguments.Count != 0
            || !definition.Parameters.All(p => BlittableScalar(p.Type) || p.Type is ByRefRef reference && BlittableScalar(reference.Element) || PlatformImportPattern.IsHandleRef(p.Type))
            || types.Kind(definition.ReturnType) != TypeKind.Void && !BlittableScalar(definition.ReturnType)
            || abi.Classify(method, out _) is not { } signature
            || signature.Arguments.Any(a => PlatformImportPattern.ForwardedPiece(a) is null)
            || signature.Return is { } ret && (ret.Passing != Passing.Registers || ret.Pieces.Length != 1)) return null;
        var resultRead = signature.Return is { } result ? new Read(result.Pieces[0].Register, result.Pieces[0].Width) : null;
        var lifted = lifter.Lift(entry, resultRead);
        if (!lifted.Succeeded || rewriter.Run(lifted.Function).Errors.Count != 0) return null;
        if (lifted.Function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Any(c => c is { Kind: CallKind.Direct, Target: Const target }
            && (facts.Code.RegionOf(target.Value) == CodeRegion.Managed || facts.EntriesAt(target.Value).Length != 0))) return null;
        var imported = PlatformImportPattern.Match(lifted.Function, signature, ReadName, EmptyCache);
        return imported is null ? null : new(method, entry, null, [])
        { Declaration = RuntimeDeclarationKind.PlatformInvoke, PlatformImport = imported };

        bool EmptyCache(ulong address)
        {
            var image = facts.Model.Image;
            if (image.SectionAt(address) is not { Executable: false } section || (section.Flags & 1) == 0
                || section.Size - (address - section.Address) < 8) return false;
            var mapping = image.Resolve(address);
            return mapping.Kind is AddressKind.ZeroFill or AddressKind.FileBacked && mapping.AvailableBytes >= 8 && image.ReadPointer(address) == 0;
        }

        string? ReadName(ulong address, ulong length)
        {
            var image = facts.Model.Image;
            if (length is < 1 or > 1024 || image.SectionAt(address) is not { Executable: false } section
                || (section.Flags & 1) != 0 || length + 1 > section.Size - (address - section.Address)
                || image.Resolve(address) is not { Kind: AddressKind.FileBacked } mapping || mapping.AvailableBytes < length + 1) return null;
            var bytes = image.Read(address, (int)length + 1);
            if (bytes[^1] != 0 || bytes[..^1].ContainsAnyExceptInRange((byte)32, (byte)126)) return null;
            return System.Text.Encoding.ASCII.GetString(bytes[..^1]);
        }
    }

    internal static bool BlittableScalar(TypeRef type) => type is PointerRef or DefinitionRef { Definition.IsEnum: true } || type is DefinitionRef
    {
        Definition:
        {
            Assembly: "mscorlib.dll", Namespace: "System", DeclaringType: null,
            Name: "SByte" or "Byte" or "Int16" or "UInt16" or "Int32" or "UInt32" or "Int64" or "UInt64"
                or "Single" or "Double" or "IntPtr" or "UIntPtr"
        }, Arguments.Count: 0
    };
}
