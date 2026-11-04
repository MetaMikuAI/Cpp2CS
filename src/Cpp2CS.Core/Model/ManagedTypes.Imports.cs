using System.Collections.Concurrent;
using System.Reflection;

namespace Cpp2CS.Model;

public sealed partial class ManagedTypes
{
    private readonly ConcurrentDictionary<string, MethodRef> mathImports = new();

    /// <summary>按已有 libm 依赖和 C 签名建立精确导入，保留原入口的浮点舍入语义。</summary>
    public MethodRef? MathImport(string? symbol)
    {
        if (MathImportSignature.Find(symbol) is not { } signature
            || Model.Image.NeededLibraries.Where(n => n is "libm.so" or "libm.so.6").ToArray() is not [var library]) return null;
        return mathImports.GetOrAdd(symbol!, name =>
        {
            var owner = new TypeDef
            {
                Index = -1, Name = "NativeImports", Namespace = "Cpp2CS", Assembly = "Cpp2CS",
                Token = 0, Attributes = TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit,
                IsValueType = false, IsEnum = false,
            };
            var scalar = signature.Single ? Single : Double;
            var method = new MethodDef
            {
                Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1,
                Attributes = MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.PinvokeImpl,
                ImplAttributes = MethodImplAttributes.PreserveSig, NativeImport = new(library, name), ReturnType = scalar,
                Parameters = signature.Parameters.Select((parameter, i) => new ParameterDef(parameter,
                    signature.IsInteger(i) ? Int32 : scalar, 0, null, false)).ToArray(),
            };
            return new(method, [], []);
        });
    }

    /// <summary>保留 sincosf 的单次调用和两个 float 出参。</summary>
    public MethodRef? SinCosImport()
    {
        if (MathImport("sinf") is not { } scalar) return null;
        return mathImports.GetOrAdd("sincosf", _ =>
        {
            var method = new MethodDef
            {
                Index = -1, Owner = scalar.Method.Owner, Name = "sincosf", Token = 0, Slot = -1,
                Attributes = scalar.Method.Attributes, ImplAttributes = scalar.Method.ImplAttributes,
                NativeImport = new(scalar.Method.NativeImport!.Library, "sincosf"), ReturnType = Corlib("System.Void"),
                Parameters = [new("value", Single, 0, null, false), new("sine", new ByRefRef(Single), 0, null, false),
                    new("cosine", new ByRefRef(Single), 0, null, false)],
            };
            return new(method, [], []);
        });
    }
}
