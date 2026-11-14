using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Structure;

public sealed partial class UnobservableEffects
{
    // codegen/il2cpp-codegen-il2cpp.h: ArrayElementTypeCheck；只折叠目录操作与具名不可变字段组成的区域。
    private bool FoldArrayStoreCheck(QueryContext c, SnapshotRewrite edit, List<StructureRecord> records,
        Dictionary<Term, ImmutableArray<StructureRecord>> rejected)
    {
        var f = c.Snapshot; var t = f.Terms;
        var sameValues = new Dictionary<(Term, Term), bool>();
        bool Same(Term a, Term b)
        {
            if (!sameValues.TryGetValue((a, b), out var same))
                sameValues[(a, b)] = same = names.SameValue(c, a, b) is { IsSuccess: true, Value: true };
            return same;
        }
        var fixedNames = new Dictionary<Term, ValueName?>();
        ValueName? Fixed(Term value)
        {
            if (!fixedNames.TryGetValue(value, out var name))
                fixedNames[value] = name = names.FixedValue(c, value) is { IsSuccess: true } n ? n.Value : null;
            return name;
        }
        MemoryRead[]? reads = null;
        Dictionary<Term, MemoryRead>? readDefinitions = null;
        StructureLiveness? liveness = null;
        Term Offset(Term address, string record, string field) => t.Apply(new CoreOperator(CoreOperation.Subtract), f.AddressWidth,
            address, t.Constant(names.Spec.Layout.Field(record, field).ByteOffset, f.AddressWidth));
        bool Nonnull(Term value, Point point)
        {
            var condition = t.Apply(new CoreOperator(CoreOperation.NotEqual), 1, value, t.Constant(0, value.Width));
            if (c.Get(typeCheckPaths, new(point, condition)) is { IsSuccess: true, Value: PathTruth.True }) return true;
            // 生成器可删除新分配对象的判空；只有目录明确的新对象/数组结果有此凭据。
            return Fixed(value) is CallResultName allocation && c.Get(calls, allocation.Call) is
                { IsSuccess: true, Value: { Operation.Il.Name: "NewObject" or "NewArray", Result.Source: TermSource result } } && Same(result.Term, value);
        }
        bool folded = false;
        foreach (var leaf in f.Blocks.Where(b => b.End is Branch))
        {
            var conditionUses = SnapshotRewrite.Dependencies([((Branch)leaf.End).Condition]);
            foreach (var call in leaf.Statements.OfType<Call>())
            {
                if (!call.Results.Any(r => conditionUses.Contains(r.Value))) continue;
                if (c.Get(calls, call.Identity) is not { IsSuccess: true, Value: { Operation.Name: "IsInstance" } classified }
                    || classified.Inputs?.GetValueOrDefault("class")?.Source is not TermSource cls
                    || classified.Inputs?.GetValueOrDefault("object")?.Source is not TermSource obj
                    || classified.Result?.Source is not TermSource result) continue;
                if (Fixed(cls.Term) is not FieldName { Field: "Il2CppClass.element_class", Owner: FieldName { Field: "Il2CppObject.klass" } arrayClass }) continue;
                void Reject(string code, string message)
                {
                    rejected[result.Term] = [new("array-store-check", call.Trace?.NativeAddress, message, false)
                        { Why = new("structure.array-store-check." + code, message) }];
                }
                reads ??= f.Blocks.SelectMany(b => b.Statements.OfType<MemoryRead>()).ToArray();
                readDefinitions ??= reads.ToDictionary(r => r.Result);
                var elementRead = readDefinitions.GetValueOrDefault(cls.Term) ?? reads.FirstOrDefault(r => Same(r.Result, cls.Term));
                var klass = elementRead is null ? null : Offset(elementRead.Address, "Il2CppClass", "element_class");
                var klassRead = klass is null ? null : readDefinitions.GetValueOrDefault(klass);
                if (klass is not null && (klassRead is null || Fixed(klassRead.Result) != arrayClass))
                    klassRead = reads.FirstOrDefault(r => Same(r.Result, klass) && Fixed(r.Result) == arrayClass);
                if (klassRead is null || klassRead.Acquire || elementRead!.Acquire) { Reject("class", "元素类没有来自同一数组对象头的类读取。"); continue; }
                var array = Offset(klassRead.Address, "Il2CppObject", "klass");
                if (c.Get(names, array) is not { IsSuccess: true, Value.StaticType: ArrayRef arrayType }
                    || !ManagedTypes.IsReferenceType(arrayType.Element))
                { Reject("array", "对象头来源没有引用元素数组的静态类型凭据。"); continue; }
                int at = leaf.Statements.IndexOf(call);
                if (!Nonnull(obj.Term, new(leaf.Identity, at)))
                { Reject("null", "类型判断没有同一 value 的前置非空凭据。"); continue; }
                if (!Nonnull(array, new(leaf.Identity, at)))
                { Reject("array", "数组对象没有前置非空凭据。"); continue; }
                var literal = TypeCheckLiteral(((Branch)leaf.End).Condition);
                if (literal.Value.Operator is not CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual } comparison)
                { Reject("condition", "类型判断结果不是与空值比较的短路条件。"); continue; }
                var operands = literal.Value.Operands;
                if (!(operands[0].ConstantValue == 0 && Same(operands[1], result.Term)
                    || operands[1].ConstantValue == 0 && Same(operands[0], result.Term)))
                { Reject("condition", "短路条件没有检查同一次类型判断的结果。"); continue; }
                var branch = (Branch)leaf.End;
                bool failedTrue = literal.Positive == (comparison.Operation == CoreOperation.Equal);
                var failure = failedTrue ? branch.True : branch.False; var success = failedTrue ? branch.False : branch.True;
                var failed = f.Blocks.Single(b => b.Identity == failure);
                var failedCalls = failed.Statements.OfType<Call>().ToArray();
                bool throwOnly = failed.End is Unreachable && failed.Statements.Length == failedCalls.Length;
                if (throwOnly && failedCalls.Length == 1)
                    throwOnly = c.Get(calls, failedCalls[0].Identity) is { IsSuccess: true, Value.Operation.Name: "ThrowArrayTypeMismatch" };
                else if (throwOnly && failedCalls.Length == 2)
                {
                    throwOnly = c.Get(calls, failedCalls[0].Identity) is { IsSuccess: true, Value: { Operation.Name: "NewArrayTypeMismatchException", Result.Source: TermSource exception } }
                        && c.Get(calls, failedCalls[1].Identity) is { IsSuccess: true, Value: { Operation.Name: "ThrowManaged", Inputs: { } inputs } }
                        && inputs.GetValueOrDefault("exception")?.Source is TermSource thrown && Same(exception.Term, thrown.Term)
                        && inputs.GetValueOrDefault("method")?.Source is TermSource method && method.Term.ConstantValue == 0;
                }
                else throwOnly = false;
                if (!throwOnly || !failedCalls[^1].DoesNotReturn)
                { Reject("throw", "失败出口不是唯一的数组类型不符异常构造及抛出。"); continue; }
                if (call.Unwind is not null || failedCalls.Any(x => x.Unwind is not null) || leaf.Handler is not null || failed.Handler is not null)
                { Reject("region", "检查区域带有尚未证明可迁移的异常边。"); continue; }
                bool TemplateRead(MemoryRead read)
                {
                    if (read.Acquire || Fixed(read.Result) is not FieldName field
                        || field.Field is not ("Il2CppObject.klass" or "Il2CppClass.element_class")) return false;
                    var specification = names.Spec.Layout.Field(field.Record, field.Field[(field.Record.Length + 1)..]);
                    return specification.ImmutableEvidence is { Length: > 0 } && (Same(read.Result, cls.Term) || Same(read.Result, klass!));
                }
                if (leaf.Statements.Skip(at + 1).Any(s => s is not MemoryRead r || !TemplateRead(r)))
                { Reject("event", "类型判断与短路出口之间还有其他事件或读取。"); continue; }
                liveness ??= new(f, EndUses);
                if (call.Results.Any(r => liveness.Outside(r.Value, [failed.Identity], leaf.Identity)))
                { Reject("use", "类型判断结果还有检查区域以外的使用。"); continue; }
                var runtime = RuntimeFunctionCatalog.Select(names.Spec.Layout.UnityVersion, names.Spec.Layout.Triple, names.Spec.Layout.DataModel)
                    .Functions.FirstOrDefault(r => r.Operation.Name == "CheckArrayElementType" && r.Signature is not null);
                var binding = runtime?.Signature is { } signature ? names.Binder.Classify(signature).Value : null;
                if (binding is null || binding.Slots.Parameters.Any(p => p.Pieces.Length != 1 || p.CopyAddress is not null))
                { Reject("binding", "目录操作没有完整的标量 ABI 绑定。"); continue; }
                var check = new Call(new(), new NamedFunction(runtime!.MangledName),
                    [new(binding.Slots.Parameters[0].Pieces[0].Slot, array), new(binding.Slots.Parameters[1].Pieces[0].Slot, obj.Term)], []) { Trace = call.Trace };
                edit.Blocks[leaf.Identity] = leaf with { Statements = leaf.Statements.SetItem(at, check), End = new Jump(success) };
                foreach (var output in call.Results) edit.Replacements[output.Value] = t.Undefined(output.Value.Width);
                rejected.Remove(result.Term);
                records.Add(new("array-store-check", call.Trace?.NativeAddress, "非空 value、同一数组对象头的元素类与唯一数组类型不符抛出，折叠为 CheckArrayElementType", true));
                folded = true;
            }
        }
        return folded;
    }
}
