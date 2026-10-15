using Cpp2CS.Flow;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Runtime;

namespace Cpp2CS.Managed;

/// <summary>已核对的 64 位 Il2CppClass 布局；其他元数据版本不借用偏移。</summary>
public sealed record RuntimeClassLayout(int StaticFields, int ConstructorFinished)
{
    public static RuntimeClassLayout? For(ProgramModel model) => model.MetadataVersion == 31 && model.Image.Architecture == Architecture.Arm64
        ? new(0xb8, 0xe0) : null;
}

public static class ClassInitialization
{
    public static TypeRef? Target(Call call, MetadataReferences metadata)
    {
        var index = Array.IndexOf(call.Sources, Storage.Gpr(0));
        return index >= 0 && index < call.Arguments.Length && metadata.Usage(call.Arguments[index]) is
            { Kind: UsageKind.TypeInfo, Value: TypeRef type } && type is DefinitionRef or ArrayRef ? type : null;
    }

    public static ManagedInvocation? Invocation(ManagedTypes types, Call call, MetadataReferences metadata, out string? problem)
    {
        problem = null;
        if (Target(call, metadata) is not { } target) { problem = "类初始化的类型信息尚未确定"; return null; }
        var handle = types.CorlibDefinition("System.RuntimeTypeHandle");
        var helper = types.CorlibDefinition("System.Runtime.CompilerServices.RuntimeHelpers");
        if (handle is null || helper is null) { problem = "元数据缺少 CLR 类初始化接口"; return null; }
        var handleType = new DefinitionRef(handle, []);
        var method = helper.Methods.SingleOrDefault(m => m.Name == "RunClassConstructor" && m.IsStatic
            && m.Parameters is [{ Type: var parameter }] && parameter == handleType && ManagedTypes.IsVoid(m.ReturnType));
        if (method is null) { problem = "元数据缺少 RunClassConstructor(RuntimeTypeHandle)"; return null; }
        return new(new MethodRef(method, [], []), null, [new TypeHandleValue(target, handleType, types.Size(handleType) * 8)]);
    }

    /// <summary>只移除同一类型的 cctor_finished 快速分支，初始化路径本身保留。CLR 接口负责一次性执行及异常缓存。</summary>
    public static void NormalizeGuards(CallResolver resolver, MachineFunction function)
    {
        if (RuntimeClassLayout.For(resolver.Model) is not { } layout) return;
        var metadata = new MetadataReferences(resolver.Model, function);
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr expression, HashSet<Variable> seen)
        {
            if (expression is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var source))
                return Fold.Convert(ConvKind.Truncate, Expand(source, seen), use.Width);
            if (expression is Ir.Convert c) return Fold.Convert(c.Kind, Expand(c.Operand, seen), c.Width);
            return expression;
        }
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch branch || block.Handler is not null
                || Expand(branch.Condition, []) is not Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 } } comparison
                || Expand(comparison.Left, []) is not Load { Width: 32, Address: Binary { Op: BinOp.Add, Right: Const offset } address }
                || offset.Value != (ulong)layout.ConstructorFinished
                || metadata.Usage(address.Left) is not { Kind: UsageKind.TypeInfo, Value: TypeRef type }) continue;
            var initializeAt = comparison.Cond == Cond.Eq ? branch.Target : branch.Fallthrough;
            var skipAt = comparison.Cond == Cond.Eq ? branch.Fallthrough : branch.Target;
            if (initializeAt == skipAt) continue;
            var initialize = block.NormalSuccessors.SingleOrDefault(b => b.Start == initializeAt);
            var skip = block.NormalSuccessors.SingleOrDefault(b => b.Start == skipAt);
            if (initialize is null || skip is null || initialize == skip || initialize.Predecessors.Count != 1
                || initialize.Handler is not null || initialize.IsLandingPad || initialize.Successors.Count != 1 || initialize.Successors[0] != skip) continue;
            var calls = initialize.Statements.OfType<Call>().ToArray();
            if (calls is not [var call] || call.Kind != CallKind.Direct || resolver.Resolve(call) is not HelperCallee { Helper.Kind: HelperKind.ClassInit }
                || Target(call, metadata) != type) continue;
            if (!initialize.Statements.All(s => s == call || s is Jump || s is Nop { Text: "branch to next" or "hint #0" or "prfm" }
                || s is Define define && metadata.IsRuntimeReference(define.Target))) continue;
            block.Statements[^1] = new Jump(branch.Address, initializeAt);
            MachineFunction.RemoveEdge(block, skip);
        }
    }
}
