using System.Collections.Immutable;
using System.Reflection;
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
    private readonly PathFactQuery typeCheckPaths = new(state);
    private readonly PrecedingBranchQuery typeCheckPredecessor = new(state);

    private static (Term Value, bool Positive) TypeCheckLiteral(Term value)
    {
        bool positive = true;
        while (value.Operator is CoreOperator { Operation: CoreOperation.Not } && value.Width == 1)
        { positive = !positive; value = value.Operands[0]; }
        return (value, positive);
    }

    // 仅展开规格登记的短路模板；支配、非空和同值沿用共享设施。
    private bool FoldTypeCheck(QueryContext c, SnapshotRewrite edit,
        IReadOnlyDictionary<BlockIdentity, HashSet<BlockIdentity>> predecessors,
        List<StructureRecord> records, Dictionary<Term, ImmutableArray<StructureRecord>> rejected)
    {
        if (FoldCheckedUnbox(c, edit, records)) return true;
        var f = c.Snapshot; var t = f.Terms;
        var reads = f.Blocks.SelectMany(b => b.Statements.OfType<MemoryRead>().Select(r => (Block: b, Read: r))).ToArray();
        if (reads.Count(p => p.Read.Width == f.AddressWidth) < 2) return false;
        var readDefinitions = reads.ToDictionary(p => p.Read.Result);
        var uses = f.Blocks.ToDictionary(b => b.Identity, b => b.Statements.SelectMany(SnapshotRewrite.Uses).Concat(EndUses(b.End)).ToList());
        foreach (var merge in f.Blocks.SelectMany(b => b.Merges))
            foreach (var input in merge.Inputs) uses[input.Predecessor].Add(input.Value);
        var candidates = f.Blocks.Select(b => (Block: b, Equalities: SnapshotRewrite.Dependencies(uses[b.Identity])
            .Where(v => v.Operator is CoreOperator { Operation: CoreOperation.Equal }
                && v.Operands[0].Width == f.AddressWidth
                && v.Operands.All(x => x.Identity is ResultAtom { Definition: ReadIdentity or MergeIdentity })).ToArray()))
            .Where(p => p.Equalities.Length != 0).ToArray();
        if (candidates.Length == 0) return false;
        ValueName? Name(Term value) => c.Get(names, value) is { IsSuccess: true } n ? n.Value.Name : null;
        var fixedNames = new Dictionary<Term, ValueName?>();
        ValueName? Fixed(Term value)
        {
            if (!fixedNames.TryGetValue(value, out var fixedName))
                fixedNames[value] = fixedName = names.FixedValue(c, value) is { IsSuccess: true } n ? n.Value : null;
            return fixedName;
        }
        bool TypeCheckRead(MemoryRead read) => Name(read.Result) is EntityName { Entity: ClassEntity }
            or FieldName { Field: "Il2CppObject.klass" or "Il2CppClass.typeHierarchyDepth" or "Il2CppClass.typeHierarchy" }
            or ArrayElementName { Array.Field: "Il2CppClass.typeHierarchy" };
        var sameValues = new Dictionary<(Term, Term), bool>();
        bool Same(Term a, Term b)
        {
            if (!sameValues.TryGetValue((a, b), out var same))
                sameValues[(a, b)] = same = names.SameValue(c, a, b) is { IsSuccess: true, Value: true };
            return same;
        }
        Term Op(CoreOperation op, int width, params Term[] values) => t.Apply(new CoreOperator(op), width, values);
        Term Extend(Term value, int width) => value.Width == width ? value : Op(CoreOperation.ZeroExtend, width, value);
        bool EntityInput(Term value) => value.Identity is ResultAtom { Definition: MergeIdentity } || names.DefinitionMethod is not null
            || readDefinitions.TryGetValue(value, out var source) && c.Get(state.Locations, new(source.Read.Address, source.Read.Width))
                is { IsSuccess: true, Value.Region: Region.Image or Region.Frame };
        Dominance? dominance = null;
        bool Dominates(BlockIdentity a, BlockIdentity b) => c.Get(flow.Graph, 0) is { IsSuccess: true } graph
            && graph.Value.Reachable.Contains(a) && graph.Value.Reachable.Contains(b)
            && (a == b || (dominance ??= new(f)).StrictlyDominates(a, 0, b, 0));
        bool Immutable(MemoryRead read)
        {
            if (read.Acquire || Fixed(read.Result) is not { } value) return false;
            if (value is EntityName) return true;
            var field = value is ArrayElementName elementName ? elementName.Array : value as FieldName;
            if (field is null || !names.Spec.Layout.Records.TryGetValue(field.Record, out var record)
                || !field.Field.StartsWith(field.Record + ".", StringComparison.Ordinal)
                || !record.Fields.TryGetValue(field.Field[(field.Record.Length + 1)..], out var specification)) return false;
            return value is ArrayElementName ? specification.ArrayElement?.ImmutableEvidence is { Length: > 0 }
                : specification.ImmutableEvidence is { Length: > 0 };
        }
        foreach (var (leaf, equalities) in candidates)
        {
            var roots = uses[leaf.Identity];
            foreach (var equal in equalities)
            {
                // 定值类来自元数据槽；帧转送、实体合流与泛型上下文仍交给命名查询复核。
                if (!EntityInput(equal.Operands[0]) && !EntityInput(equal.Operands[1])) continue;
                Term? target = null, checkedClass = null; FieldName? klassName = null; ArrayElementName? element = null;
                foreach (var (value, other) in new[] { (equal.Operands[0], equal.Operands[1]), (equal.Operands[1], equal.Operands[0]) })
                {
                    if (Fixed(value) is FieldName { Field: "Il2CppObject.klass" } klass)
                    { checkedClass = value; target = other; klassName = klass; break; }
                    if (Fixed(value) is ArrayElementName { Array.Field: "Il2CppClass.typeHierarchy", Array.Owner: FieldName { Field: "Il2CppObject.klass" } owner } array)
                    { checkedClass = value; target = other; klassName = owner; element = array; break; }
                }
                if (target is null || checkedClass is null || klassName is null) continue;
                // 运行时类之间的比较也用于分派；只有另一端是类输入时才是本模板候选。
                if (Name(target) is not EntityName { Entity: ClassEntity } && c.Get(names, target) is not { IsSuccess: true, Value: { Kind: ValueKind.RuntimePointer, Record: "Il2CppClass" } }) continue;
                var related = reads.Where(p => p.Block == leaf && TypeCheckRead(p.Read)).ToArray();
                if (element is null && readDefinitions.TryGetValue(checkedClass, out var directClass)) related = related.Append(directClass).Distinct().ToArray();
                if (readDefinitions.TryGetValue(target, out var targetRead)) related = related.Append(targetRead).Distinct().ToArray();
                void Reject(string code, string message)
                {
                    var why = new Reason("structure.type-check." + code, message);
                    rejected[equal] = related.Select(p => new StructureRecord("type-check-retained", p.Read.Trace?.NativeAddress ?? p.Block.Trace?.NativeAddress, message, false) { Why = why }).ToImmutableArray();
                }
                if (Name(target) is not EntityName { Entity: ClassEntity entity })
                { Reject("shape", "目标类不是具名的定值类实体，泛型上下文不在本模板范围内。"); continue; }
                if (entity.Type.ContainsGenericParameter()
                    || c.Get(state.Resolve, target) is { IsSuccess: true, Value.Identity: MemoryAtom { Location.Region: Region.Other } })
                { Reject("shape", "目标类含开放类型参数或来自运行时上下文读取，不在本模板范围内。"); continue; }
                if (entity.Type is ArrayRef)
                { Reject("exact", "数组的精确类比较不等于可赋值类型判断。"); continue; }
                if (entity.Type is not DefinitionRef type || type.Definition.IsInterface)
                { Reject(element is null ? "exact" : "shape", "目标类型不是非接口的类定义。"); continue; }
                if (element is null && !type.Definition.IsValueType && (type.Definition.Attributes & TypeAttributes.Sealed) == 0)
                { Reject("exact", "精确类比较的目标没有密封或装箱值类型的元数据凭据。"); continue; }
                var offset = names.Spec.Layout.Field("Il2CppObject", "klass").ByteOffset;
                (Block Block, MemoryRead Read) klassRead = default;
                if (element is null && readDefinitions.TryGetValue(checkedClass, out var direct)) klassRead = direct;
                else if (readDefinitions.TryGetValue(checkedClass, out var elementRead))
                {
                    // 先沿表元素地址的依赖找表及对象类，避免给整个方法的读取逐一命名。
                    var hierarchyOffset = names.Spec.Layout.Field("Il2CppClass", "typeHierarchy").ByteOffset;
                    foreach (var dependency in SnapshotRewrite.Dependencies([elementRead.Read.Address]))
                    {
                        if (dependency.Width != f.AddressWidth || !readDefinitions.TryGetValue(dependency, out var tableRead)
                            || Fixed(dependency) is not FieldName { Field: "Il2CppClass.typeHierarchy", Owner: var tableOwner } || tableOwner != klassName) continue;
                        var baseClass = Op(CoreOperation.Subtract, f.AddressWidth, tableRead.Read.Address, t.Constant(hierarchyOffset, f.AddressWidth));
                        if (!readDefinitions.TryGetValue(baseClass, out var fromTable) || Fixed(fromTable.Read.Result) != klassName) continue;
                        klassRead = fromTable; break;
                    }
                }
                if (klassRead.Read is null) klassRead = reads.Where(p => p.Read.Width == f.AddressWidth && Op(CoreOperation.Subtract, f.AddressWidth,
                        p.Read.Address, t.Constant(offset, f.AddressWidth)).Identity is EntryAtom or ResultAtom)
                        .FirstOrDefault(p => Fixed(p.Read.Result) == klassName);
                if (klassRead.Read is null) klassRead = reads.FirstOrDefault(p => Fixed(p.Read.Result) == klassName);
                if (klassRead.Read is null || klassRead.Block is null) { Reject("shape", "对象类读取没有可重建的原生定义。"); continue; }
                related = related.Append(klassRead).Distinct().ToArray();
                var obj = Op(CoreOperation.Subtract, f.AddressWidth, klassRead.Read.Address, t.Constant(offset, f.AddressWidth));
                var nonnull = Op(CoreOperation.Not, 1, Op(CoreOperation.Equal, 1, obj, t.Constant(0, obj.Width)));
                if (c.Get(typeCheckPaths, new(new(klassRead.Block.Identity, klassRead.Block.Statements.IndexOf(klassRead.Read)), nonnull)) is not { IsSuccess: true, Value: PathTruth.True })
                { Reject("null", "对象类的读取没有前置非空路径事实；直接解引用不能改成允许空值的类型判断。"); continue; }
                var objectName = Fixed(obj);
                var targetName = Fixed(target);
                bool TemplateRead(MemoryRead read)
                {
                    if (!Immutable(read)) return false;
                    var value = Fixed(read.Result);
                    if (value is EntityName) return true;
                    if (value is ArrayElementName && !Same(read.Result, checkedClass)) return false;
                    var field = value is ArrayElementName e ? e.Array : value as FieldName;
                    return field is not null && (field.Owner == objectName || field.Owner == klassName || field.Owner == targetName);
                }

                Block head = leaf;
                var between = ImmutableArray<BlockIdentity>.Empty;
                BlockIdentity? depthFailure = null;
                if (element is not null)
                {
                    var preceding = c.Get(typeCheckPredecessor, leaf.Identity);
                    if (!preceding.IsSuccess)
                    { Reject("shape", "层次表比较没有唯一入边的短路深度前驱。" + preceding.Why!.Message); continue; }
                    between = preceding.Value.Between;
                    head = f.Blocks.Single(b => b.Identity == preceding.Value.Branch);
                    related = related.Concat(reads.Where(p => p.Block == head && TypeCheckRead(p.Read))).Distinct().ToArray();
                    if (head.End is not Branch db)
                    { Reject("shape", "层次表比较的前驱不是深度分支。"); continue; }
                    var literal = TypeCheckLiteral(db.Condition);
                    if (literal.Value.Operator is not CoreOperator { Operation: CoreOperation.UnsignedLess })
                    { Reject("shape", "深度条件不是无符号大小比较。"); continue; }
                    var kd = literal.Value.Operands[0]; var pd = literal.Value.Operands[1];
                    var depthField = names.Spec.Layout.Field("Il2CppClass", "typeHierarchyDepth");
                    var depthBits = depthField.Size * 8;
                    var targetDepth = reads.FirstOrDefault(p => p.Read.Width == depthBits
                        && Name(p.Read.Result) is FieldName { Field: "Il2CppClass.typeHierarchyDepth", Owner: EntityName { Entity: ClassEntity e } } && e == entity);
                    if (pd.Kind == TermKind.Constant || targetDepth.Read is null)
                    { Reject("depth", "深度必须读取同一个目标类的 typeHierarchyDepth，不能使用常量。"); continue; }
                    int depthWidth = targetDepth.Read.Width;
                    if (kd.Width < depthWidth || Fixed(t.Slice(kd, 0, depthWidth)) is not FieldName { Field: "Il2CppClass.typeHierarchyDepth", Owner: var owner } || owner != klassName
                        || !Same(kd, Extend(t.Slice(kd, 0, depthWidth), kd.Width)))
                    { Reject("shape", "深度比较的左侧不是同一对象类的无符号深度。"); continue; }
                    bool SameDepth(Term value) => value.Width >= depthWidth
                        && Same(value, Extend(t.Slice(value, 0, depthWidth), value.Width))
                        && Same(t.Slice(value, 0, depthWidth), targetDepth.Read.Result);
                    if (!SameDepth(pd) || !SameDepth(Op(CoreOperation.Add, element.Index.Width, element.Index, t.Constant(1, element.Index.Width))))
                    { Reject("depth", "比较深度或层次表下标不是同一目标类的深度及深度减一。"); continue; }
                    var enough = literal.Positive ? db.False : db.True;
                    depthFailure = literal.Positive ? db.True : db.False;
                    if (enough != preceding.Value.Successor)
                    { Reject("shape", "深度比较成立的一侧没有短路进入层次表比较。"); continue; }
                    if (f.Blocks.Where(b => b == head || b == leaf || between.Contains(b.Identity)).Any(b => b.Handler is not null
                        || b.Statements.Any(s => s is not MemoryRead r || !TemplateRead(r))))
                    { Reject("shape", "深度与层次表比较之间包含定值、不可变读取以外的语句。"); continue; }
                }

                var literalEnd = leaf.End is Branch branch ? TypeCheckLiteral(branch.Condition) : default;
                bool branchUse = literalEnd.Value == equal;
                var selections = SnapshotRewrite.Dependencies(roots).Where(v => v.Operator is CoreOperator { Operation: CoreOperation.Select }
                    && TypeCheckLiteral(v.Operands[0]).Value == equal
                    && (TypeCheckLiteral(v.Operands[0]).Positive
                        ? Same(v.Operands[1], obj) && v.Operands[2].ConstantValue == 0
                        : Same(v.Operands[2], obj) && v.Operands[1].ConstantValue == 0)).ToHashSet();
                bool selectedBranch = leaf.End is Branch && literalEnd.Value.Operator is CoreOperator { Operation: CoreOperation.Equal }
                    && (literalEnd.Value.Operands[0].ConstantValue == 0 && selections.Contains(literalEnd.Value.Operands[1])
                        || literalEnd.Value.Operands[1].ConstantValue == 0 && selections.Contains(literalEnd.Value.Operands[0]));
                BlockIdentity? success = null, failure = null;
                Call? throwing = null;
                if (branchUse || selectedBranch)
                {
                    var br = (Branch)leaf.End;
                    bool positive = branchUse ? literalEnd.Positive : !literalEnd.Positive;
                    success = positive ? br.True : br.False;
                    failure = positive ? br.False : br.True;
                    if (Dominates(success, head.Identity))
                    { Reject("shape", "成功出口返回检查入口的支配区域，结果没有独立续点。"); continue; }
                    if (depthFailure is not null && depthFailure != failure)
                    { Reject("shape", "深度失败与类比较失败的出口不同。"); continue; }
                    var failBlock = f.Blocks.Single(b => b.Identity == failure);
                    var failCalls = failBlock.Statements.OfType<Call>().ToArray();
                    if (failCalls.Length == 1 && failBlock.End is Unreachable
                        && c.Get(calls, failCalls[0].Identity) is { IsSuccess: true, Value.Operation.Name: "ThrowInvalidCast" } classified)
                    {
                        var call = failCalls[0];
                        if (!call.DoesNotReturn || classified.Value.Inputs?.GetValueOrDefault("object")?.Source is not TermSource inputObject
                            || classified.Value.Inputs?.GetValueOrDefault("class")?.Source is not TermSource inputClass
                            || !Same(inputObject.Term, obj) || !Same(inputClass.Term, target))
                        { Reject("shape", "失败抛出不是同一对象与目标类的唯一不返回转换失败调用。"); continue; }
                        if (failBlock.Statements.Any(s => s != call && (s is not MemoryRead r || !TemplateRead(r))))
                        { Reject("shape", "转换失败出口包含同一对象、对象类、目标类的不可变读取以外的语句。"); continue; }
                        throwing = call;
                    }
                }
                else if (element is not null)
                {
                    // 物化路径必须只有对象或空的值差别，其他出口值仍按同值核对。
                    Term Failed(Term value) => value == equal ? t.Constant(0, 1) : selections.Contains(value) ? t.Constant(0, value.Width)
                        : SnapshotRewrite.Rebuild(value, Failed);
                    if (depthFailure is null)
                    { Reject("shape", "物化的层次判断没有深度失败出口。"); continue; }
                    var failBlock = f.Blocks.Single(b => b.Identity == depthFailure);
                    if (leaf.End is Return returned && failBlock.End is Return failedReturn && failBlock.Statements.IsEmpty && failBlock.Merges.IsEmpty)
                    {
                        var values = failedReturn.Results.Where(r => returnSlots is null || returnSlots.Contains(r.Slot)).ToDictionary(r => r.Slot);
                        var projected = returned.Results.Where(r => returnSlots is null || returnSlots.Contains(r.Slot)).ToArray();
                        if (values.Count != projected.Length || projected.Any(r => !values.TryGetValue(r.Slot, out var old) || !Same(old.Value, Failed(r.Value))))
                        { Reject("shape", "物化判断的失败返回值不等于比较失败时的值。"); continue; }
                    }
                    else if (leaf.End is Jump joinJump)
                    {
                        if (failBlock.Identity != joinJump.Target && !(failBlock.End is Jump fj && fj.Target == joinJump.Target && failBlock.Statements.IsEmpty && failBlock.Merges.IsEmpty))
                        { Reject("shape", "物化判断的深度失败路径含其他效果或不同出口。"); continue; }
                        var join = f.Blocks.Single(b => b.Identity == joinJump.Target);
                        var failedPredecessor = failBlock == join ? head.Identity : failBlock.Identity;
                        var live = new StructureLiveness(f, EndUses);
                        if (join.Merges.Where(m => live.Used(m.Result)).Any(m =>
                            m.Inputs.FirstOrDefault(i => i.Predecessor == failedPredecessor) is not { } a
                            || m.Inputs.FirstOrDefault(i => i.Predecessor == leaf.Identity) is not { } b || !Same(a.Value, Failed(b.Value))))
                        { Reject("shape", "物化判断的其他活跃合流值在深度失败时不同。"); continue; }
                    }
                    else { Reject("shape", "物化的层次判断没有兼容的返回或汇合出口。"); continue; }
                }
                bool cast = throwing is not null;
                if (depthFailure is not null && (branchUse || selectedBranch))
                {
                    var failed = f.Blocks.Single(b => b.Identity == depthFailure);
                    var live = failed.Merges.IsEmpty ? null : new StructureLiveness(f, EndUses);
                    if (failed.Merges.Where(m => live!.Used(m.Result)).Any(m => m.Inputs.FirstOrDefault(i => i.Predecessor == head.Identity) is { } a
                        && m.Inputs.FirstOrDefault(i => i.Predecessor == leaf.Identity) is { } b && !Same(a.Value, b.Value)))
                    { Reject("shape", "短路失败出口的其他合流值不同。"); continue; }
                }

                var runtime = RuntimeFunctionCatalog.Select(names.Spec.Layout.UnityVersion, names.Spec.Layout.Triple, names.Spec.Layout.DataModel)
                    .Functions.FirstOrDefault(r => r.Operation.Name == (cast ? "CastClass" : "IsInstance") && r.Arguments.SequenceEqual(new[] { "object", "class" }) && r.Signature is not null);
                var signature = runtime?.Signature is { } rs ? names.Binder.Classify(rs).Value : null;
                if (signature is null || signature.Slots.Parameters.Any(p => p.Pieces.Length != 1 || p.CopyAddress is not null)
                    || signature.Slots.Return.Pieces.Length != 1 || signature.Slots.Return.BufferAddress is not null)
                { Reject("shape", "目录里的类型判断操作缺少完整的标量 ABI 绑定。"); continue; }
                var candidate = new SnapshotRewrite(f); var moved = new List<MemoryRead>();
                var nativeDominance = dominance ??= new(f);
                var available = new HashSet<Term>();
                bool Available(Term value)
                {
                    if (!available.Add(value)) return true;
                    if (readDefinitions.TryGetValue(value, out var definition))
                    {
                        if (definition.Block == head || nativeDominance.StrictlyDominates(definition.Block.Identity, definition.Block.Statements.IndexOf(definition.Read) + 1, head.Identity, head.Statements.Length)) return true;
                        if (Name(value) is not EntityName || !Immutable(definition.Read) || !Available(definition.Read.Address)) return false;
                        moved.Add(definition.Read); candidate.RemovedStatements.Add(definition.Read); return true;
                    }
                    if (value.Identity is ResultAtom) return value == obj && Dominates(klassRead.Block.Identity, head.Identity);
                    return value.Operands.All(Available);
                }
                if (!Available(target) || !Available(obj))
                { Reject("shape", "对象或目标类不能在短路入口重建。"); continue; }
                ImmutableArray<Merge>? exceptionMerges = null;
                if (throwing?.Unwind is { } handler)
                {
                    var handlerBlock = f.Blocks.Single(b => b.Identity == handler);
                    var changedMerges = ImmutableArray.CreateBuilder<Merge>();
                    bool compatible = true;
                    foreach (var merge in handlerBlock.Merges)
                    {
                        var old = merge.Inputs.Single(i => i.Predecessor == failure);
                        var existing = merge.Inputs.FirstOrDefault(i => i.Predecessor == head.Identity);
                        if (existing is not null ? !Same(existing.Value, old.Value) : !Available(old.Value))
                        { compatible = false; break; }
                        changedMerges.Add(existing is null ? merge with { Inputs = merge.Inputs.Add(new(head.Identity, old.Value)) } : merge);
                    }
                    if (!compatible)
                    { Reject("shape", "转换失败的展开边携带不能在检查入口重建的合流值。"); continue; }
                    exceptionMerges = changedMerges.ToImmutable();
                }
                var id = new CallIdentity(); var result = t.Atom(new ResultAtom(id), f.AddressWidth);
                var runtimeCall = new Call(id, new NamedFunction(runtime!.MangledName),
                    [new(signature.Slots.Parameters[0].Pieces[0].Slot, obj), new(signature.Slots.Parameters[1].Pieces[0].Slot, target)],
                    [new(signature.Slots.Return.Pieces[0].Slot, result)], Unwind: throwing?.Unwind) { Trace = klassRead.Read.Trace ?? head.Trace };
                var test = Op(CoreOperation.Not, 1, Op(CoreOperation.Equal, 1, result, t.Constant(0, result.Width)));
                var replacements = selections.ToDictionary(v => v, _ => result); replacements[equal] = test;
                var cache = new Dictionary<Term, Term>();
                Term Map(Term value)
                {
                    if (replacements.TryGetValue(value, out var replacement)) return replacement;
                    if (cache.TryGetValue(value, out var mapped)) return mapped;
                    return cache[value] = SnapshotRewrite.Rebuild(value, Map);
                }
                foreach (var block in f.Blocks)
                    candidate.Blocks[block.Identity] = block with
                    {
                        Statements = Dominates(head.Identity, block.Identity) ? block.Statements.Select(s => SnapshotRewrite.Rewrite(s, Map)).ToImmutableArray() : block.Statements,
                        End = Dominates(head.Identity, block.Identity) ? SnapshotRewrite.Rewrite(block.End, Map) : block.End,
                        Merges = block.Merges.Select(m => m with { Inputs = m.Inputs.Select(i => i with { Value = Dominates(head.Identity, i.Predecessor) ? Map(i.Value) : i.Value }).ToImmutableArray() }).ToImmutableArray(),
                    };
                // 展开输入属于调用之前的状态，不能替换成仅正常返回后可用的结果。
                if (exceptionMerges is { } handlerMerges)
                    candidate.Blocks[throwing!.Unwind!] = candidate.Blocks[throwing.Unwind!] with { Merges = handlerMerges };
                // 精确比较可在同块的调用输入里物化；操作必须位于该使用之前。
                int insertion = head.Statements.Length;
                if (head == leaf)
                    for (int i = 0; i < head.Statements.Length; i++)
                        if (SnapshotRewrite.Dependencies(SnapshotRewrite.Uses(head.Statements[i])).Contains(equal)) { insertion = i; break; }
                var headBlock = candidate.Blocks[head.Identity];
                candidate.Blocks[head.Identity] = headBlock with { Statements = headBlock.Statements.InsertRange(insertion, moved.Cast<Statement>().Append(runtimeCall)),
                    End = head == leaf ? headBlock.End : new Jump(between.IsEmpty ? leaf.Identity : between[0]) };
                // 移动的实体读取在原位置删除，在新位置保留相同的定义身份。
                foreach (var read in moved)
                {
                    candidate.RemovedStatements.Remove(read);
                    foreach (var block in f.Blocks.Where(b => b.Identity != head.Identity))
                        candidate.Blocks[block.Identity] = candidate.Blocks[block.Identity] with { Statements = candidate.Blocks[block.Identity].Statements.Where(s => s != read).ToImmutableArray() };
                }
                if (cast) candidate.Blocks[leaf.Identity] = candidate.Blocks[leaf.Identity] with { End = new Jump(success!) };
                if (success is not null)
                {
                    var newDefinitions = new HashSet<StableIdentity> { id };
                    var sameObjects = new Dictionary<Term, bool>();
                    bool ObjectValue(Term value)
                    {
                        if (value == obj) return true;
                        if (value.Width != obj.Width || value.Identity is not (EntryAtom or ResultAtom)
                            || value.Identity is ResultAtom atom && newDefinitions.Contains(atom.Definition)) return false;
                        if (!sameObjects.TryGetValue(value, out var same)) sameObjects[value] = same = Same(value, obj);
                        return same;
                    }
                    var edgeCache = new Dictionary<Term, Term>();
                    Term RefineEdge(Term value) => ObjectValue(value) ? result : edgeCache.TryGetValue(value, out var mapped) ? mapped
                        : edgeCache[value] = SnapshotRewrite.Rebuild(value, RefineEdge);
                    var zeroCache = new Dictionary<Term, Term>();
                    Term NullEdge(Term value) => ObjectValue(value) ? t.Constant(0, value.Width) : zeroCache.TryGetValue(value, out var zero) ? zero
                        : zeroCache[value] = SnapshotRewrite.Rebuild(value, NullEdge);
                    var nullEdges = new Dictionary<FlowEdge, bool>();
                    bool NullAtEdge(BlockIdentity previous, BlockIdentity next)
                    {
                        var edge = new FlowEdge(previous, next);
                        if (!nullEdges.TryGetValue(edge, out var known))
                            nullEdges[edge] = known = c.Get(typeCheckPaths, new(new(previous, f.Blocks.Single(b => b.Identity == previous).Statements.Length),
                                Op(CoreOperation.Equal, 1, obj, t.Constant(0, obj.Width)), edge)) is { IsSuccess: true, Value: PathTruth.True };
                        return known;
                    }
                    // 汇合可同时接收几个转换路径；每条成功边细化自己的对象，空边保留空值。
                    var joined = candidate.Blocks[success];
                    candidate.Blocks[success] = joined with { Merges = joined.Merges.Select(m => m with { Inputs = m.Inputs.Select(i => i with
                        { Value = i.Predecessor == leaf.Identity ? RefineEdge(i.Value) : NullAtEdge(i.Predecessor, success) ? NullEdge(i.Value) : i.Value }).ToImmutableArray() }).ToImmutableArray() };
                    Term? refined = null;
                    if (predecessors[success].SetEquals([leaf.Identity])) refined = result;
                    else if (cast && predecessors[success].All(p => p == leaf.Identity || NullAtEdge(p, success)))
                    {
                        var mergeId = new MergeIdentity(); refined = t.Atom(new ResultAtom(mergeId), result.Width);
                        newDefinitions.Add(mergeId);
                        var merge = new Merge(mergeId, refined, predecessors[success].Select(p => new Incoming(p, p == leaf.Identity ? result : t.Constant(0, result.Width))).ToImmutableArray());
                        candidate.Blocks[success] = candidate.Blocks[success] with { Merges = candidate.Blocks[success].Merges.Add(merge) };
                    }
                    if (refined is not null)
                    {
                        var refinedCache = new Dictionary<Term, Term>();
                        Term Refine(Term value) => ObjectValue(value) ? refined : refinedCache.TryGetValue(value, out var known) ? known
                            : refinedCache[value] = SnapshotRewrite.Rebuild(value, Refine);
                        foreach (var block in f.Blocks)
                        {
                            var current = candidate.Blocks[block.Identity];
                            Term IncomingValue(Incoming incoming)
                            {
                                if (Dominates(success, incoming.Predecessor)) return Refine(incoming.Value);
                                var zero = NullEdge(incoming.Value);
                                return zero != incoming.Value && SnapshotRewrite.Targets(candidate.Blocks[incoming.Predecessor].End).Contains(block.Identity)
                                    && NullAtEdge(incoming.Predecessor, block.Identity) ? zero : incoming.Value;
                            }
                            candidate.Blocks[block.Identity] = current with
                            {
                                Statements = Dominates(success, block.Identity) ? current.Statements.Select(s => SnapshotRewrite.Rewrite(s, Refine)).ToImmutableArray() : current.Statements,
                                End = Dominates(success, block.Identity) ? SnapshotRewrite.Rewrite(current.End, Refine) : current.End,
                                Merges = current.Merges.Select(m => m with { Inputs = m.Inputs.Select(i => i with { Value = IncomingValue(i) }).ToImmutableArray() }).ToImmutableArray(),
                            };
                        }
                    }
                }
                // 表元素只能由已折叠的比较消费；否则不能让它越过深度保护。
                if (element is not null)
                {
                    var remaining = SnapshotRewrite.Dependencies(candidate.Blocks.Values.SelectMany(b => b.Statements.SelectMany(SnapshotRewrite.Uses)
                        .Concat(EndUses(b.End)).Concat(b.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)))));
                    if (remaining.Contains(checkedClass) || reads.Any(p => remaining.Contains(p.Read.Result) && Name(p.Read.Result) is ArrayElementName && Same(p.Read.Result, checkedClass)))
                    { Reject("shape", "层次表元素仍有类型判断以外的使用。"); continue; }
                }
                foreach (var (key, value) in candidate.Blocks) edit.Blocks[key] = value;
                foreach (var s in candidate.RemovedStatements) edit.RemovedStatements.Add(s);
                rejected.Remove(equal);
                records.Add(new("type-check", klassRead.Read.Trace?.NativeAddress, (element is null ? "IsInstSealed/CastclassSealed" : "IsInstClass/CastclassClass")
                    + "：非空路径、同一对象与定值类、短路条件及失败实参成立，折叠为 " + runtime.Operation.Name, true));
                return true;
            }
        }
        return false;
    }
}
