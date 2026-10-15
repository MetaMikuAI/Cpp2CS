using Cpp2CS.Metadata;

namespace Cpp2CS.Semantics;

public sealed record Origin(int Node, string Address);
public abstract record Value(string Type);
public sealed record Local(string Name, string ValueType, bool Argument) : Value(ValueType);
public sealed record Constant(ulong Bits, string ValueType) : Value(ValueType);
public sealed record Conversion(Value Operand, string TargetType) : Value(TargetType);
public sealed record Binary(string Operation, Value Left, Value Right, string ResultType) : Value(ResultType);
public sealed record Unary(string Operation, Value Operand, string ResultType) : Value(ResultType);
public sealed record FieldValue(Local Root, Field Field) : Value(Field.Type);
public sealed record Choice(Value Condition, Value True, Value False, string ResultType) : Value(ResultType);
public sealed record Storage(Local Root, int Offset);
public sealed record Slice(Field Field, int Shift);
public sealed record PackedLoad(Local Root, Slice[] Fields, string ResultType) : Value(ResultType);

public abstract record Statement(Origin Source);
public sealed record Store(Origin Source, Value Target, Value Value) : Statement(Source);
public sealed record PackedStore(Origin Source, Local Root, Slice[] Fields, Value Value, int Width) : Statement(Source);
public sealed record Return(Origin Source, Value? Value) : Statement(Source);
public sealed record If(Origin Source, Value Condition, Statement[] True, Statement[] False) : Statement(Source);
public sealed record BaseInitialize(Origin Source, string NativeAddress) : Statement(Source);
public sealed record Body(Method Method, Local[] Locals, Statement[] Statements);
