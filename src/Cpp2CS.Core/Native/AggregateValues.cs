using Cpp2CS.IR;

namespace Cpp2CS.Native;

public sealed partial class FunctionLifter
{
    private static Expression BooleanValue(Expression expression)
    {
        var value = Unwrap(expression);
        if (value is SliceExpression { BitOffset: 0, BitWidth: > 0 } slice) value = Unwrap(slice.Value);
        if (value is OperationExpression { Operation: ValueOperation.Select, Arguments: [var condition, ConstantExpression { Value: 1 }, ConstantExpression { Value: 0 }] }) return condition;
        return new BinaryExpression("!=", expression, new ConstantExpression(0));
    }
    private readonly Dictionary<Bits, (string Type, Expression Value)> aggregateValues = [];
    private readonly Dictionary<long, (string Name, string Type)> mutableStack = [];
    private readonly Dictionary<Bits, string> aggregateLogicalTypes = [];
    private NativeValue Project(NativeValue value)
    {
        var root = value.Bits is SliceBits slice ? slice.Source : value.Bits;
        var offset = value.Bits is SliceBits part ? part.Offset : 0;
        if (!aggregateValues.TryGetValue(root, out var aggregate)) return value;
        if (offset == 0 && value.Bits.Width == root.Width) return value with { Type = aggregate.Type, Expression = aggregate.Value };
        var field = layouts.ContainingField(aggregate.Type, offset / 8, value.Bits.Width / 8);
        if (offset % 8 != 0 || value.Bits.Width % 8 != 0 || field is null) return value;
        Expression expression = aggregate.Value;
        if (aggregateLogicalTypes.TryGetValue(root, out var logical) && managed.FieldTypeOf(logical, field.Name) is { } fieldType)
        {
            var concrete = symbols.DisplayTypes.Where(p => p.Value == fieldType || !fieldType.Contains('.') && p.Value.EndsWith("." + fieldType)).Select(p => p.Key).Distinct().ToArray();
            var native = concrete.Length == 1 ? concrete[0] + (field.Type.EndsWith('*') ? "*" : "") : field.Type;
            return value with { Type = native, Expression = new MemberExpression(expression, field, Getter(aggregate.Type, offset / 8, value.Bits.Width / 8) ?? field.Name, fieldType) };
        }
        foreach (var path in field.Path.Where(p => p != "fields"))
            expression = new MemberExpression(expression, field, path, null);
        return value with { Type = field.Type, Expression = expression };
    }
    private bool ConstructOnStack(NativeMethod method, NativeValue[] arguments, ulong pc, NativeState state, List<Statement> statements, LiftResult result)
    {
        if (!method.Name.EndsWith("$$.ctor") || arguments[0].Expression is not StackAddressExpression stack ||
            managed.BaseTypeOf(method.Name.Split("$$")[0]) != "System.ValueType") return false;
        var boundary = UnwindBoundary.Read(image, method.Address);
        if (boundary.Start != method.Address || boundary.End <= method.Address || boundary.End - method.Address > 16384) return false;
        if (decoder.Decode(image.Read(method.Address, (int)(boundary.End - method.Address)), method.Address)
            .Any(i => i.Mnemonic is "bl" or "blr" or "b" or "br")) return false;
        var body = new FunctionLifter(image, decoder, symbols, layouts, managed, runtime).Lift(method.Address);
        if (body.Problems.Count > 0 || body.Blocks.Count != 1) return false;
        var writes = body.Blocks.Values.Single().Statements;
        if (writes.LastOrDefault() is not ReturnStatement || writes.SkipLast(1).Any(s => s is not StoreStatement
            { Target: MemberExpression { Receiver: NameExpression { Name: "this" } }, Value: NameExpression })) return false;
        var type = method.Parameters[0].Type.TrimEnd('*');
        var fields = writes.OfType<StoreStatement>().Select(s => ((MemberExpression)s.Target).Field).OrderBy(f => f.Offset).ToArray();
        var end = 0;
        if (fields.Length == 0 || !fields.All(f => { var contiguous = f.Offset == end; end += f.Size; return contiguous; }) || end != layouts.Size(type)) return false;
        foreach (var write in writes.OfType<StoreStatement>())
            if (!method.Parameters.Any(p => p.Name == ((NameExpression)write.Value).Name && p.Name != "__this" && p.Name != "method")) return false;
        var variable = $"constructed_{pc:x}";
        var args = arguments.Skip(1).Take(method.Parameters.Length - 2).Select(a => a.Expression).ToArray();
        statements.Add(new AssignStatement(pc, variable, new InvocationExpression("new " + symbols.Display(type), null, args, false), type));
        var bits = new InputBits(variable, end * 8);
        aggregateValues[bits] = (type, new NameExpression(variable));
        NativeValues.StoreStack(state, stackRegion, stack.Offset, new(bits, type, new NameExpression(variable)), variable);
        Clobber(state, pc);
        result.Proofs.Add(new(pc, "ValueConstructor", "callee contains only complete, non-overlapping receiver field stores from constructor parameters; stack value updated at call"));
        return true;
    }
}
