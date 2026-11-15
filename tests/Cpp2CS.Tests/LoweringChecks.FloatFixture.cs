using Cpp2CS.Model;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static ProgramModel FloatFixture(CecilModel model, string library)
    {
        int headerSize = checked((int)InputCorpusChecks.Spec("arm64-v8a").Layout.ObjectHeaderSize);
        string[] support = ["Object", "String", "ValueType", "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "TypedReference"];
        var selected = model.Program.Types.Where(t => t.Assembly == "input" || t.Assembly == "mscorlib.dll" &&
            (ManagedTypes.PrimitiveName(new DefinitionRef(t, [])) is not null || support.Contains(t.Name) || t.Name == library)).ToArray();
        var mapped = selected.Select((type, index) => (type, copy: new TypeDef { Index = index, Assembly = type.Assembly,
            Namespace = type.Namespace, Name = type.Name, Token = type.Token, Attributes = type.Attributes,
            IsValueType = type.IsValueType, IsEnum = false, PackingSize = 0, ClassSizeIsDefault = true, Size = type.Name == "FloatLeaf" ? 4 : type.IsValueType ? -1 : headerSize })).ToDictionary(p => p.type, p => p.copy);
        TypeRef Type(TypeRef type) => type switch
        {
            DefinitionRef d => new DefinitionRef(mapped[d.Definition], d.Arguments.Select(Type).ToArray()),
            ByRefRef b => new ByRefRef(Type(b.Element)), _ => type,
        };
        var methods = new List<MethodDef>(); var fields = new List<FieldDef>();
        foreach (var original in selected)
        {
            var type = mapped[original];
            if (original.BaseType is DefinitionRef b && mapped.ContainsKey(b.Definition)) type.BaseType = Type(b);
            var members = original.Assembly == "input" ? original.Methods : original.Name == "BitConverter"
                ? original.Methods.Where(m => m.Name is "SingleToInt32Bits" or "Int32BitsToSingle" or "DoubleToInt64Bits" or "Int64BitsToDouble")
                : original.Name == "Math" ? original.Methods.Where(m => m.Name is "Atan2" or "Pow" or "Truncate" or "Sin" or "Cos")
                    .Where(m => ManagedTypes.PrimitiveName(m.ReturnType) == "Double" && m.Parameters.All(p => ManagedTypes.PrimitiveName(p.Type) == "Double"))
                : Enumerable.Empty<MethodDef>();
            type.Methods = members.Select(m => new MethodDef { Index = methods.Count, Owner = type, Name = m.Name, Token = m.Token,
                Attributes = m.Attributes, ImplAttributes = m.ImplAttributes, Slot = -1, ReturnType = Type(m.ReturnType),
                Parameters = m.Parameters.Select(p => p with { Type = Type(p.Type) }).ToArray() }).Select(m => { methods.Add(m); return m; }).ToArray();
            if (original.Assembly == "input")
                type.Fields = original.Fields.Select(f => new FieldDef { Index = fields.Count, Owner = type, Name = f.Name, Type = Type(f.Type),
                    Offset = 0, Attributes = f.Attributes, Token = f.Token }).Select(f => { fields.Add(f); return f; }).ToArray();
        }
        var definitions = mapped.Values.ToArray();
        return new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = fields, RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key, AssemblyName = Path.GetFileNameWithoutExtension(g.Key),
                Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
    }
}
