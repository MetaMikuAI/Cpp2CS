using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    private readonly HashSet<Store> constructorStores = new(ReferenceEqualityComparer.Instance);

    /// <summary>构造函数为无参基类构造及连续字段写入时，用其原生恢复体绑定实际构造参数。</summary>
    private NewObjectValue? ConstructorWithStores(Block block, int index, ResultSym allocation, DefinitionRef allocated, MethodRef baseConstructor)
    {
        if (baseConstructor.Method.Parameters.Count != 0) return null;
        bool Ready(Sym source)
        {
            source = SymTable.Resolve(source);
            if (ReferenceEquals(source, allocation)) return false;
            if (locals.ContainsKey(source)) return true;
            return source switch
            {
                ArgSym or ConstSym or EntitySym => true,
                OpSym op => op.Args.All(Ready),
                SliceSym slice => Ready(slice.Base),
                ConcatSym concat => concat.Parts.All(Ready),
                _ => false,
            };
        }
        foreach (var definition in allocated.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
        {
            var constructor = new MethodRef(definition, allocated.Arguments, []);
            if (summaries(constructor) is not { Body: { Regions.Count: 0 } body }) continue;
            var statements = body.Blocks.SelectMany(b => b.Statements).Where(s => s is not ManagedJump).ToArray();
            if (statements is not [ManagedCall { Tail: false, Result: null, Invocation: { Receiver: ArgumentValue { Index: -1 }, Arguments.Count: 0 } invoke }, .., ManagedReturn { Value: null }]
                || !invoke.Method.Equals(baseConstructor) || statements.Skip(1).SkipLast(1).Any(s => s is not ManagedStore)) continue;
            var writes = statements.Skip(1).SkipLast(1).Cast<ManagedStore>().ToArray();
            if (writes.Length == 0) continue;
            var arguments = new Sym?[definition.Parameters.Count];
            var matched = new List<Store>();
            var cursor = index + 1;
            var valid = true;
            foreach (var write in writes)
            {
                while (cursor < block.Statements.Count && (block.Statements[cursor] is Nop
                    || block.Statements[cursor] is Define && !Reads(block.Statements[cursor]).Any()
                    || block.Statements[cursor] is Call { Op.Kind: OpKind.WriteBarrier })) cursor++;
                if (write.Target is not FieldValue { Receiver: ArgumentValue { Index: -1 } } field
                    || cursor >= block.Statements.Count || block.Statements[cursor] is not Store store)
                { valid = false; break; }
                var operands = values.Operands(store);
                if (oracle.Locate(operands[0], store.Value.Width) is not { Kind: LocationKind.Instance, Base: { } receiver, Path: [var target] } location
                    || !ReferenceEquals(SymTable.Resolve(receiver), allocation) || !target.Equals(field.Field)
                    || store.Value.Width != Width(location.Type) || !Ready(operands[1]))
                { valid = false; break; }
                switch (write.Value)
                {
                    case ArgumentValue { Index: >= 0 } argument when argument.Index < arguments.Length:
                        var type = TypeOracle.Concrete(constructor, definition.Parameters[argument.Index].Type);
                        if (!type.Equals(location.Type)) { valid = false; break; }
                        var value = SymTable.Resolve(operands[1]);
                        if (arguments[argument.Index] is { } prior && !ReferenceEquals(prior, value)) valid = false;
                        arguments[argument.Index] = value;
                        break;
                    case ConstantValue constant when SymTable.Resolve(operands[1]) is ConstSym actual
                        && (actual.Value & Expr.Mask(constant.Width)) == constant.Bits:
                        break;
                    default:
                        valid = false;
                        break;
                }
                if (!valid) break;
                matched.Add(store);
                cursor++;
            }
            if (!valid || arguments.Any(a => a is null)) continue;
            constructorStores.UnionWith(matched);
            return new NewObjectValue(constructor, arguments.Select((a, i) => View(a!, TypeOracle.Concrete(constructor, definition.Parameters[i].Type), block.Statements[index].Address)).ToArray()) { Transparent = true };
        }
        return null;
    }
}
