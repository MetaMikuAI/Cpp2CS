namespace Cpp2CS.Semantics;

public abstract record Transfer;
public sealed record Jump(int Target) : Transfer;
public sealed record Branch(Value Condition, int True, int False) : Transfer;
public sealed record Select(Value Value, SwitchArm[] Arms, int Default) : Transfer;
public sealed record SwitchArm(ulong Bits, int Target);
public sealed record Finish(Value? Value) : Transfer;
public sealed record FlowBlock(int Id, Origin Source, Statement[] Effects, Transfer Transfer);
public sealed record ControlFlow(Origin Source, int Entry, FlowBlock[] Blocks) : Statement(Source);
