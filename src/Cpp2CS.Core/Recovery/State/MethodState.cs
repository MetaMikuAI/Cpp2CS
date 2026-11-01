
namespace Cpp2CS.Recovery;

internal sealed class MethodState
{
    internal readonly ConstructionState Construction = new();
    internal readonly ArraysState Arrays = new();
    internal readonly CallsState Calls = new();
    internal readonly SignatureState Signature = new();
    internal readonly TypesState Types = new();
    internal readonly RuntimeState Runtime = new();
    internal readonly LoweringState Lowering = new();
    internal readonly FramesState Frames = new();
    internal readonly ExceptionsState Exceptions = new();
    internal readonly StructsState Structs = new();
    internal readonly ControlState Control = new();
    internal readonly GenericsState Generics = new();
    internal IStatementKeyed[] StatementTables => [Arrays, Calls, Construction, Control, Exceptions, Frames, Lowering, Runtime, Structs];
}
