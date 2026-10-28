using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>逐方法的 CIL 写出状态；程序集符号与证据由会话共享。</summary>
internal sealed partial class CilBodyWriter(Skeleton skeleton, ManagedTypes types, EmissionPolicy policy, EmissionSymbols symbols)
{
    private readonly Dictionary<Variable, VariableDefinition> locals = new();
    private readonly Dictionary<PinnedArrayValue, VariableDefinition> pinnedArrays = new();
    private readonly Dictionary<ulong, Instruction> labels = new();
    private Dictionary<ModuleDefinition, (MethodReference At, MethodReference Fail, MethodDefinition Value)> unrecovered => symbols.Unrecovered;
    private Dictionary<ModuleDefinition, (MethodDefinition Of, MethodDefinition Do, MethodDefinition Result, MethodDefinition Completed, MethodDefinition CompletedVoid)> awaits => symbols.Awaits;
    private HashSet<Instruction> ExplicitInitializations => symbols.ExplicitInitializations;
    private MethodDefinition destination = null!;
    private MethodBody body = null!;
    private ILProcessor il = null!;
    private MethodRef methodContext = null!;

    private TypeReference TypeReference(TypeRef type) => skeleton.Reference(destination.Module, type, destination.DeclaringType, destination);
    private FieldReference FieldReference(FieldRef field) => skeleton.Reference(destination.Module, field, destination.DeclaringType, destination);
    private MethodReference MethodReference(MethodRef method) => skeleton.Reference(destination.Module, method, destination.DeclaringType, destination);

    public void Write(ManagedBody recovered, MethodDefinition method)
    {
        destination = method;
        body = new MethodBody(method) { InitLocals = true };
        il = body.GetILProcessor();
        methodContext = recovered.Method;
        regions = recovered.Regions;
        var entryDefaults = policy == EmissionPolicy.Source && Cpp2CS.Structure.EnumerationProtocol.IteratorMoveNext(recovered.Method.Method)
            ? SourceEntryDefaults.Find(recovered) : [];
        foreach (var pinned in recovered.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<PinnedArrayValue>().Distinct())
        {
            var local = new VariableDefinition(new PinnedType(TypeReference(pinned.ArrayType)));
            body.Variables.Add(local);
            pinnedArrays.Add(pinned, local);
        }
        foreach (var block in recovered.Blocks) labels.Add(block.Address, Instruction.Create(OpCodes.Nop));
        foreach (var block in recovered.Blocks)
        {
            currentBlock = block.Address;
            il.Append(labels[block.Address]);
            foreach (var region in regions.Where(r => r.HandlerEntry == block.Address && r.Kind == ManagedRegionKind.Catch))
                il.Emit(OpCodes.Stloc, Local(region.Exception!));
            foreach (var statement in block.Statements)
                if (!entryDefaults.Contains(statement)) Statement(statement);
        }
        WriteExceptionTable(recovered);
        method.Body = body;
    }

    private VariableDefinition Local(LocalValue value)
    {
        if (!locals.TryGetValue(value.Variable, out var local)) locals.Add(value.Variable, local = Temp(value.Type));
        return local;
    }

    private VariableDefinition Temp(TypeRef type)
    {
        var local = new VariableDefinition(TypeReference(type));
        body.Variables.Add(local);
        return local;
    }

}
