using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>区分元数据槽位地址和槽位内容。只沿已知重定位、64 位读取和一致的 SSA 来源传播。</summary>
public sealed class MetadataReferences
{
    private abstract record Reference;
    private sealed record Slot(ulong Address) : Reference;
    private sealed record Content(Usage Usage) : Reference;
    private sealed record StaticStorage(DefinitionRef Type, int Offset) : Reference;
    private readonly ProgramModel model;
    private readonly Dictionary<Variable, Reference> references = new();

    public MetadataReferences(ProgramModel model, MachineFunction function)
    {
        this.model = model;
        if (model.MetadataVersion < 27) return;
        var statements = function.Blocks.SelectMany(b => b.Statements).Where(s => s is Define or Phi).ToArray();
        bool changed;
        do
        {
            changed = false;
            foreach (var statement in statements)
            {
                var target = statement is Define d ? d.Target : ((Phi)statement).Target;
                if (references.ContainsKey(target)) continue;
                Reference? reference = statement switch
                {
                    Define define => Resolve(define.Value),
                    Phi phi when phi.Sources.Length > 0 && references.TryGetValue(phi.Sources[0], out var first)
                        && phi.Sources.All(v => references.GetValueOrDefault(v) == first) => first,
                    _ => null,
                };
                if (reference is null) continue;
                references.Add(target, reference);
                changed = true;
            }
        } while (changed);
    }

    public Usage? Usage(Expr expression) => Resolve(expression) is Content content ? content.Usage : null;

    public (DefinitionRef Type, int Offset)? StaticAddress(Expr expression) => Resolve(expression) is StaticStorage storage
        ? (storage.Type, storage.Offset) : null;

    /// <summary>这些变量只供恢复阶段使用；它们的任何普通托管用途仍须单独通过类型恢复。</summary>
    public bool IsRuntimeReference(Variable variable) => references.GetValueOrDefault(variable) is Slot
        or StaticStorage or Content { Usage.Kind: not UsageKind.StringLiteral };

    private Reference? Resolve(Expr expression)
    {
        if (model.MetadataVersion < 27) return null;
        if (expression is Use { Width: 64 } use) return references.GetValueOrDefault(use.Variable);
        if (expression is Binary { Op: BinOp.Add, Width: 64, Right: Const displacement } add
            && Resolve(add.Left) is StaticStorage storage)
            return displacement.Signed >= -storage.Offset && displacement.Signed <= int.MaxValue - storage.Offset
                ? storage with { Offset = storage.Offset + (int)displacement.Signed } : null;
        if (expression is not Load { Width: 64 } load) return null;
        if (RuntimeClassLayout.For(model) is { } layout
            && load.Address is Binary { Op: BinOp.Add, Width: 64, Right: Const offset } field
            && offset.Value == (ulong)layout.StaticFields && Resolve(field.Left) is Content
                { Usage: { Kind: UsageKind.TypeInfo, Value: DefinitionRef owner } }) return new StaticStorage(owner, 0);
        var address = load.Address is Const constant ? constant.Value : Resolve(load.Address) is Slot slot ? slot.Address : (ulong?)null;
        if (address is not { } at) return null;
        if (model.UsageAt(at) is { } usage) return new Content(usage);
        return model.Image.RelocatedPointer(at) is { } target && model.UsageAt(target) is not null ? new Slot(target) : null;
    }
}
