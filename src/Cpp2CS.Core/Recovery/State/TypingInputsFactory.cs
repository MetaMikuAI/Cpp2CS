using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery;

internal static class TypingInputsFactory
{
    internal static (MachineFunction View, Dictionary<Storage, TypeRef> Entry, TypingInputs Input) TypingInputsFor(this RecoveryScope ctx)
    {
        // 不改原 CFG，Build 仍用原始边编号。
        var view = new MachineFunction
        {
            Entry = ctx.function.Entry,
            Range = ctx.function.Range,
            Blocks = ctx.blocks.Select(b => new Block(b.Start) { Index = b.Index, End = b.End, IsLandingPad = b.IsLandingPad, Statements = b.Statements.Select(s => s is Phi phi ? (Stmt)(ctx.State.Exceptions.exceptionPhis.GetValueOrDefault(phi.Target) ?? phi) : s).ToList(), }).ToList(),
        };
        var input = new TypingInputs
        {
            Method = ctx.method,
            Arguments = ctx.State.Signature.arguments.ToDictionary(p => p.Key, p => new EntryArgument(p.Value.Index, p.Value.Type, p.Value.Width)),
            StructArguments = ctx.State.Signature.structArguments.ToDictionary(),
            Dropped = ctx.State.Lowering.dropped.ToHashSet(),
            StoredArguments = ctx.State.Frames.stackArgumentStores.Concat(ctx.State.Construction.boxArgumentStores).Select(p => (p.Key, p.Value.Type)).Concat(ctx.State.Frames.stackEnums.Values.SelectMany(e => e.Stores.Where(s => s.Target is FrameAddress f && f.Offset == e.Offset + Facts.RuntimeLayout.ObjectHeaderSize).Select(s => (s, (TypeRef)e.Type)))).Distinct().ToDictionary(p => p.Item1, p => p.Item2),
            Constructed = ctx.State.Construction.constructed.ToDictionary(),
            DelegateCreations = ctx.State.Construction.delegateCreations.ToDictionary(),
            StackEnumValues = ctx.State.Frames.stackEnums.Values.Select(e => (e.Value, (TypeRef)e.Type)).ToArray(),
            Wrappers = ctx.State.Exceptions.wrappers.ToDictionary(),
            Exceptions = ctx.State.Exceptions.exceptionValues.ToDictionary(),
            HasExceptions = ctx.State.Exceptions.exceptionLayout is { Succeeded: true },
            ReturnSupported = ctx.State.Signature.returnHole is null,
            UnusedInput = ctx.UnusedInput,
            Host = context => new HostTyping(ctx, context),
        };
        var entry = input.Arguments.Where(p => !input.StructArguments.ContainsKey(p.Key) && p.Value.Type is not ByRefRef).ToDictionary(p => p.Key, p => p.Value.Type);
        return (view, entry, input);
    }
}
