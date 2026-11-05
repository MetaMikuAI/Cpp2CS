using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>
/// 识别 IL2CPP 为数组字面量生成的内联 RVA 数据复制：元数据槽指向带初值的字段，
/// 原生代码把字段数据逐块写入刚分配的数组。恢复为 RuntimeHelpers.InitializeArray。
/// </summary>
internal static class RvaArrayInitPass
{
    internal static bool RvaArrayInit(this IdiomState state)
    {
        var assembly = state.self?.Method.Owner.Assembly;
        if (assembly is null) return false;

        var changed = false;
        foreach (var call in state.All.OfType<Call>().ToArray())
        {
            if (state.owner.HelperOf(call)?.Kind != HelperKind.InitMetadata
                || call.Arguments.Length == 0
                || state.defs.Expand(call.Arguments[0]) is not Const { Value: var slot }) continue;

            var raw = state.facts.Model.Image.ReadPointer(slot);
            if (raw is not { } token || token >> 29 != 7) continue;
            var index = (int)((token & 0x1FFFFFFF) >> 1);
            var fields = state.facts.Model.FieldRvaFields(assembly);
            if (index < 0 || index >= fields.Count) continue;
            var field = fields[index];
            if (field.Field.InitialValue is not { Length: > 0 } blob) continue;

            var slotLoad = state.All.OfType<Define>()
                .FirstOrDefault(define => define.Value is Load { Width: 64, Address: Const address } && address.Value == slot);
            if (slotLoad is null) continue;
            var slotVariable = slotLoad.Target;

            var allocated = state.All.OfType<Call>()
                .Where(candidate => candidate.Op is { Kind: OpKind.NewArray, Operand: ArrayRef { IsVector: true } }
                    && candidate.Defines.Length == 1 && candidate.Arguments.Length >= 2)
                .Select(candidate => (Call: candidate, Array: (ArrayRef)candidate.Op!.Operand!, Variable: candidate.Defines[0]))
                .ToArray();
            if (allocated.Length == 0) continue;

            var reads = state.All.OfType<Define>()
                .Where(define => LoadsFrom(define.Value, slotVariable))
                .ToArray();
            if (reads.Length == 0) continue;
            var readVariables = reads.Select(read => read.Target).ToHashSet();

            var writes = state.All.OfType<Store>()
                .Where(store => readVariables.Any(variable => ExprMap.Walk(store.Value).OfType<Use>().Any(use => use.Variable == variable)))
                .ToArray();
            if (writes.Length != reads.Length) continue;

            var selected = allocated.FirstOrDefault(candidate =>
                state.defs.Expand(candidate.Call.Arguments[1]) is Const { Value: var length }
                && length <= int.MaxValue
                && state.facts.Layouts.TrySizeAndAlignment(candidate.Array.Element) is { Size: > 0 } element
                && (ulong)(element.Size * (int)length) == (ulong)blob.Length
                && WritesArray(writes, candidate.Variable, blob.Length));
            if (selected.Call is null) continue;

            // 每个读取值只能供一次数组写入，且不能有其他消费者；槽位也只能供这些读取。
            var uses = state.All.SelectMany(statement => ExprMap.Operands(statement)).SelectMany(ExprMap.Walk)
                .OfType<Use>().ToArray();
            var slotReadUses = reads.SelectMany(read => ExprMap.Walk(read.Value).OfType<Use>())
                .Count(use => use.Variable == slotVariable);
            if (readVariables.Any(variable => uses.Count(use => use.Variable == variable) != 1)
                || uses.Count(use => use.Variable == slotVariable) != slotReadUses
                || state.All.OfType<Store>().Any(store => TouchesArray(store.Target, selected.Variable) && !writes.Contains(store)))
                continue;

            var block = state.function.Blocks.FirstOrDefault(candidate => candidate.Statements.Any(statement => ReferenceEquals(statement, selected.Call)));
            if (block is null) continue;
            var at = block.Statements.FindIndex(statement => ReferenceEquals(statement, selected.Call));
            if (at < 0) continue;

            foreach (var statement in reads.Cast<Stmt>().Append(slotLoad).Append(call))
                Replace(state, statement);
            foreach (var statement in writes)
                Replace(state, statement);
            block.Statements.Insert(at + 1, new Call(selected.Call.Address, CallKind.Direct, Expr.C(0, 64))
            {
                Op = new RuntimeOp(OpKind.InitializeArray, field),
                Arguments = [new Use(selected.Variable, 64)],
            });
            changed = true;
        }

        return changed;
    }

    private static void Replace(IdiomState state, Stmt statement)
    {
        foreach (var block in state.function.Blocks)
        {
            var at = block.Statements.FindIndex(candidate => ReferenceEquals(candidate, statement));
            if (at < 0) continue;
            block.Statements[at] = new Nop(statement.Address, "RVA 数组初始化");
            return;
        }
    }

    private static bool LoadsFrom(Expr expression, Variable slot) =>
        ExprMap.Walk(expression).OfType<Load>().Any(load => AddressUses(load.Address, slot));

    private static bool AddressUses(Expr address, Variable slot) => address switch
    {
        Use use => use.Variable == slot,
        Binary { Op: BinOp.Add, Left: var left } => AddressUses(left, slot),
        _ => false,
    };

    private static bool WritesArray(IEnumerable<Store> stores, Variable array, int blobLength) =>
        stores.All(store => store.Target is Binary { Op: BinOp.Add, Left: Use { Variable: var root }, Right: Const { Value: var offset } }
            && root == array && offset >= (ulong)RuntimeLayout.ArrayData && offset < (ulong)RuntimeLayout.ArrayData + (ulong)blobLength);

    private static bool TouchesArray(Expr target, Variable array) =>
        ExprMap.Walk(target).OfType<Use>().Any(use => use.Variable == array);
}
