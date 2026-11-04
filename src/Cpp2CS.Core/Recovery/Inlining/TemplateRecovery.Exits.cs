using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 内联区域的出口。模板每条返回路径在调用方的终点由 <see cref="Finish"/> 求出：先纳入组成返回值的分段读取，再沿无条件跳转到达续接点。
/// 调用方在续接点观察到的值都是返回值的函数：对一条路径上的值把返回值抽象成结果局部，得到函数 f，再逐路径代入验证。
/// 布尔承接、零扩展、字段投影和比较都只是 f 的不同形式；条件续接的谓词同样如此，常量返回路径直接按谓词的取值选择续接。
/// </summary>
internal sealed partial class TemplateRecovery
{
    private bool ConcludeExit(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks) =>
        ConcludeReturn(match, method) || ConcludeContinuation(match, method, body, blocks);

    /// <summary>模板的一条路径返回：调用方从当前位置沿无条件跳转到达的点是这条路径的出口，连同出口边上的复制记为一个终点。</summary>
    private bool Finish(Walker caller, InlineMatch match, ManagedValue? result)
    {
        if (result is not null && !CaptureReturnValue(caller, match, result)) return false;
        var copies = new List<(LocalValue, ManagedValue)>();
        var continuation = false;
        for (var steps = 0; steps < 16; steps++)
        {
            if (caller.Current is not (ManagedJump or ManagedAssignment)) break;
            // 共享续接保留赋值作为共同终点；跳转复制逐边组合，其他入边仍保留原块。
            continuation |= caller.Index == 0 && caller.Blocks.Values.Count(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == caller.Block)) > 1;
            if (!continuation && caller.Current is ManagedAssignment assignment && NonThrowingInlineValue(assignment.Value)
                && caller.Index == caller.Blocks[caller.Block].Statements.Count - 2
                && caller.Blocks[caller.Block].Statements[^1] is ManagedJump
                && caller.Env.TryGetValue(assignment.Target.Variable, out var previous)
                && Term(caller, assignment.Value) is { } assigned && SameTerm(previous, assigned))
            {
                var locals = ManagedValues.Walk(assignment.Value).OfType<LocalValue>().Select(l => l.Variable)
                    .Append(assignment.Target.Variable).ToHashSet();
                var addressed = caller.Blocks.Values.SelectMany(b => b.Statements).SelectMany(ReadValues).SelectMany(ManagedValues.Walk)
                    .OfType<AddressValue>().SelectMany(a => ManagedValues.Walk(a.Target)).OfType<LocalValue>().Any(l => locals.Contains(l.Variable));
                if (addressed) break;
                if (!continuation) Cover(caller, match);
                caller.Index++;
                continue;
            }
            if (caller.Current is not ManagedJump jump) break;
            if (continuation && jump.Edge.Copies.Any(c => !NonThrowingInlineValue(c.Value))) break;
            if (!continuation) Cover(caller, match);
            var edgeCopies = new List<(LocalValue Target, ManagedValue Value)>();
            foreach (var copy in jump.Edge.Copies)
            {
                if (Term(caller, copy.Value) is not { } value) return false;
                edgeCopies.Add((copy.Target, value));
            }
            foreach (var copy in edgeCopies) caller.Env[copy.Target.Variable] = copy.Value;
            copies.AddRange(edgeCopies);
            if (!caller.Blocks.ContainsKey(jump.Edge.Target)) return false;
            caller.Block = jump.Edge.Target;
            caller.Index = 0;
        }
        var returns = result is null && caller.Current is ManagedReturn { Value: null }
            && !continuation
            && (caller.Index > 0 || caller.Blocks.Values.Count(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == caller.Block)) <= 1);
        if (result is not null && !continuation && caller.Current is ManagedReturn { Value: { } returned }
            && Term(caller, returned) is { } actual)
        {
            var trial = new Dictionary<int, ManagedValue>(match.Binding);
            if (Unify(result, actual, trial))
            {
                foreach (var (key, value) in trial) match.Binding[key] = value;
                returns = true;
            }
        }
        if (returns) Cover(caller, match);
        match.Ends.Add(new InlineEnd((caller.Block, caller.Index), copies, new Dictionary<Variable, ManagedValue>(caller.Env), result, returns, caller.Epoch));
        return true;
    }

    /// <summary>返回表达式的读取可拆成若干赋值；只纳入结果本身及其读取子项，不越过无关求值。</summary>
    private bool CaptureReturnValue(Walker caller, InlineMatch match, ManagedValue result)
    {
        var terms = new List<ManagedValue>();
        void Collect(ManagedValue value)
        {
            if (value is Observed) terms.Add(value);
            MapTerm(value, child => { Collect(child); return child; });
        }
        Collect(result);
        if (terms.Count == 0) return true;
        for (var steps = 0; steps < 256; steps++)
        {
            if (caller.Index >= caller.Blocks[caller.Block].Statements.Count) return false;
            if (caller.Current is ManagedJump jump)
            {
                if (caller.Blocks.Values.Count(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == jump.Edge.Target)) > 1)
                    return true;
                Cover(caller, match);
                if (!Follow(caller, jump.Edge)) return false;
                continue;
            }
            if (caller.Current is not ManagedAssignment assignment || Term(caller, assignment.Value) is not { } value) return true;
            Dictionary<int, ManagedValue>? binding = null;
            var complete = false;
            foreach (var expected in new[] { result }.Concat(terms))
            {
                var trial = new Dictionary<int, ManagedValue>(match.Binding);
                if (!Unify(expected, value, trial)) continue;
                binding = trial;
                complete = ReferenceEquals(expected, result);
                break;
            }
            if (binding is null) return true;
            foreach (var (key, bound) in binding) match.Binding[key] = bound;
            Cover(caller, match);
            caller.Env[assignment.Target.Variable] = value;
            match.Defined[assignment.Target.Variable] = value;
            match.Locals[assignment.Target.Variable] = assignment.Target;
            caller.Index++;
            if (complete) return true;
        }
        return false;
    }

    /// <summary>返回：调用方在每条路径上直接返回模板的返回值（或都返回 void），返回类型可赋给调用方的返回类型。</summary>
    private bool ConcludeReturn(InlineMatch match, MethodRef method)
    {
        var returnedType = method.Concrete(method.Method.ReturnType);
        var callerReturn = caller.Concrete(caller.Method.ReturnType);
        if (match.Ends.Count == 0 || !match.Ends.All(e => e.Returns)
            || !returnedType.Equals(callerReturn) && !types.IsAssignable(returnedType, callerReturn)) return false;
        match.Exit = match.Ends[0].Exit;
        match.ExitCopies = [];
        match.Returns = true;
        return true;
    }

    /// <summary>结果局部与它在某条路径上对应的项：返回值整体，以及结构体返回值的可访问叶子。</summary>
    private IEnumerable<(ManagedValue Actual, ManagedValue Carrier)> Carriers(InlineEnd end, TypeRef returnType, LocalValue result)
    {
        if (end.Result is not { } returned) yield break;
        yield return (returned, result);
        if (returnType is not DefinitionRef structure || types.Kind(structure) != TypeKind.Struct) yield break;
        foreach (var projection in types.Projections(structure))
        {
            ManagedValue carrier = result;
            var accessible = true;
            foreach (var field in projection.Path)
            {
                if (!fields.Accessible(field, carrier.Type)) { accessible = false; break; }
                var fieldType = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
                carrier = new FieldValue(carrier, field, fieldType, Width(fieldType));
            }
            if (accessible && ManagedProjections.Project(types, returned, projection, field => new Observed(field, end.Epoch)) is { Value: var value })
                yield return (value, carrier);
        }
    }

    /// <summary>项本身（不进入它的子项之外的结构）等于 part：字段投影的载体也算。</summary>
    private static bool Contains(ManagedValue value, ManagedValue part)
    {
        if (value.Equals(part)) return true;
        if (part is LocalValue && value is FieldValue) return false;
        var found = false;
        MapTerm(value, child =>
        {
            found |= Contains(child, part);
            return child;
        });
        return found;
    }

    private static bool Mentions(ManagedValue value, LocalValue local)
    {
        if (value is LocalValue found && found.Variable == local.Variable) return true;
        var mentioned = false;
        MapTerm(value, child =>
        {
            mentioned |= Mentions(child, local);
            return child;
        });
        return mentioned;
    }

    /// <summary>把项中等于返回值（或其叶子）的部分换成结果局部。</summary>
    private ManagedValue Abstract(ManagedValue value, IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> carriers, InlineMatch match)
    {
        foreach (var (actual, carrier) in carriers)
        {
            if (actual is ConstantValue) continue;
            if (Unify(actual, value, new(match.Binding))) return carrier;
            // 布尔返回值的取反：调用方的条件常写成相反的比较。
            if (types.Kind(actual.Type) == TypeKind.Bool && Unify(Negate(actual), value, new(match.Binding)))
                return new ComparisonValue(Cond.Eq, carrier, new ConstantValue(0, carrier.Type, carrier.Width), types.Boolean);
        }
        return MapTerm(value, child => Abstract(child, carriers, match));
    }

    /// <summary>把结果局部代入这条路径的返回值，并折叠常量。</summary>
    private ManagedValue Instantiate(ManagedValue value, IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> carriers)
    {
        foreach (var (actual, carrier) in carriers)
            if (carrier.Equals(value)) return actual;
        var mapped = MapTerm(value, child => Instantiate(child, carriers));
        return mapped switch
        {
            ComparisonValue { Left: ConstantValue left, Right: ConstantValue right } comparison when ConstantComparison(comparison.Condition, left, right) is { } truth
                => new ConstantValue(truth ? 1UL : 0UL, types.Boolean, 8),
            NegatedValue { Operand: ConstantValue operand } => new ConstantValue(operand.Bits == 0 ? 1UL : 0UL, types.Boolean, 8),
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate, Operand: ConstantValue operand } conversion
                => new ConstantValue(operand.Bits & Expr.Mask(conversion.Width), conversion.Type, conversion.Width),
            _ => mapped,
        };
    }

    /// <summary>
    /// 续接：各路径或在同一点继续，或按返回值的谓词分到一对续接点。续接点活跃的局部都由结果局部的同一函数给出。
    /// 返回值没有被观察时可以丢弃，但模板额外求值的返回项不得引入异常或副作用。
    /// </summary>
    private bool ConcludeContinuation(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        if (match.Ends.Count == 0) return match.Fail("模板没有返回路径");
        if (match.Ends.Any(e => e.Returns)) return match.Fail("返回路径与续接路径混合");
        var isVoid = ManagedTypes.IsVoid(method.Method.ReturnType);
        var returnType = method.Concrete(method.Method.ReturnType);
        if (!isVoid && match.Ends.Any(e => e.Result is null)) return match.Fail("返回路径没有返回值");
        var result = isVoid ? null : NewLocal(returnType);
        IReadOnlyList<(ManagedValue Actual, ManagedValue Carrier)> Pairs(InlineEnd end) => result is null ? [] : Carriers(end, returnType, result).ToArray();
        Walker At(InlineEnd end) => new() { Blocks = blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Env = new(end.Env), Epoch = end.Epoch };
        // 谓词取自一条在续接点按返回值分支的路径。
        ManagedValue? predicate = null;
        if (result is not null)
            foreach (var end in match.Ends.OrderBy(e => e.Result is ConstantValue ? 1 : 0))
            {
                if (At(end).Current is not ManagedBranch branch || Term(At(end), branch.Condition) is not { } tested) continue;
                var abstracted = Abstract(tested, Pairs(end), match);
                if (Mentions(abstracted, result)) { predicate = abstracted; break; }
            }
        var used = false;
        // 一个续接点的局部复制：逐路径验证同一函数。
        IReadOnlyList<(LocalValue Target, ManagedValue Value)>? Copies(IReadOnlyList<InlineEnd> ends)
        {
            var exit = ends[0].Exit;
            var edged = match.Covered.SelectMany(p => ManagedValues.Edges(blocks[p.Block].Statements[p.Index])).SelectMany(e => e.Copies).Select(c => c.Target)
                .Concat(ends.SelectMany(e => e.Copies.Select(c => c.Target))).DistinctBy(l => l.Variable).ToArray();
            var targets = edged.Concat(match.Locals.Values.Where(l => match.Defined.ContainsKey(l.Variable))).DistinctBy(l => l.Variable).ToArray();
            var copies = new List<(LocalValue, ManagedValue)>();
            foreach (var target in targets)
            {
                var held = ends.Select(e => e.Env.GetValueOrDefault(target.Variable) ?? target).ToArray();
                var isEdge = edged.Any(l => l.Variable == target.Variable);
                if (!LiveAt(body, blocks, exit.Block, exit.Index, target.Variable) && (!isEdge || held.All(NonThrowingInlineValue))) continue;
                var function = Enumerable.Range(0, ends.Count).OrderBy(i => ends[i].Result is ConstantValue ? 1 : 0)
                    .Select(i => Abstract(held[i], Pairs(ends[i]), match)).First();
                // 与返回值无关的区域内定义由保存副本与区域外使用的检查处理。
                if (!isEdge && (result is null || !Mentions(function, result))) continue;
                var trial = new Dictionary<int, ManagedValue>(match.Binding);
                for (var i = 0; i < ends.Count; i++)
                    if (!Unify(Instantiate(function, Pairs(ends[i])), held[i], trial)) { match.Fail("出口复制在各路径上不同"); return null; }
                foreach (var (key, value) in trial) match.Binding[key] = value;
                if (result is not null && Mentions(function, result)) used = true;
                copies.Add((target, function));
            }
            return copies;
        }
        if (predicate is null)
        {
            if (match.Ends.Any(e => e.Exit != match.Ends[0].Exit))
                return match.Fail($"各路径在调用方的出口不同：{string.Join(", ", match.Ends.Select(e => $"0x{e.Exit.Block:x}+{e.Exit.Index}"))}");
            if (Copies(match.Ends) is not { } joined) return false;
            match.Exit = match.Ends[0].Exit;
            match.ExitCopies = joined;
            match.Result = used ? result : null;
            if (!used && !match.Ends.All(e => e.Result is null || NonThrowingInlineValue(e.Result)))
                return match.Fail("返回值没有承接的局部，且无法证明额外求值无副作用");
            // 只观察部分叶子时，其余叶子的求值也不能引入异常。
            if (used && !joined.Any(c => Contains(c.Value, result!)))
                foreach (var end in match.Ends)
                    foreach (var (actual, carrier) in Pairs(end).Skip(1))
                        if (!joined.Any(c => Contains(c.Value, carrier)) && !NonThrowingInlineValue(actual))
                            return match.Fail("结构体返回值未被承接的叶子无法证明额外求值无副作用");
            return true;
        }
        var sides = new Dictionary<bool, List<InlineEnd>> { [true] = [], [false] = [] };
        var covered = new HashSet<(ulong Block, int Index)>();
        bool Along(InlineEnd end, ManagedEdge edge, bool outcome)
        {
            var walker = At(end);
            var copies = end.Copies.ToList();
            foreach (var copy in edge.Copies)
            {
                if (Term(walker, copy.Value) is not { } value) return false;
                copies.Add((copy.Target, value));
            }
            if (!Follow(walker, edge)) return false;
            var trial = new InlineMatch { Binding = [], TypeArguments = match.TypeArguments };
            if (!Finish(walker, trial, null) || trial.Ends.Count != 1) return false;
            covered.UnionWith(trial.Covered);
            sides[outcome].Add(trial.Ends[0] with { Copies = copies.Concat(trial.Ends[0].Copies).ToArray(), Result = end.Result, Epoch = end.Epoch });
            return true;
        }
        foreach (var end in match.Ends)
        {
            var expected = Instantiate(predicate, Pairs(end));
            if (expected is ConstantValue constant)
            {
                if (end.Exit.Index != 0) return match.Fail("条件续接点位于块中间");
                sides[constant.Bits != 0].Add(end);
                continue;
            }
            if (At(end).Current is not ManagedBranch branch || Term(At(end), branch.Condition) is not { } condition)
                return match.Fail("返回路径不受同一条件支配");
            var canonical = Canonical(expected);
            bool same;
            if (Unify(canonical, Canonical(condition), match.Binding)) same = true;
            else if (Unify(canonical, Canonical(Negate(condition)), match.Binding)) same = false;
            else return match.Fail("返回值与调用方的比较不同");
            covered.Add(end.Exit);
            if (!Along(end, branch.Taken, same) || !Along(end, branch.Fallthrough, !same)) return false;
        }
        ManagedEdge? Edge(IReadOnlyList<InlineEnd> ends)
        {
            if (ends.Count == 0) { match.Fail("谓词只有一种结果"); return null; }
            if (ends.Any(e => e.Exit != ends[0].Exit)) { match.Fail("相同返回条件的续接点不同"); return null; }
            if (ends[0].Exit.Index != 0) { match.Fail("条件续接点位于块中间"); return null; }
            return Copies(ends) is { } copies ? new ManagedEdge(ends[0].Exit.Block, copies.Select(c => new ManagedCopy(c.Target, c.Value)).ToArray()) : null;
        }
        if (Edge(sides[true]) is not { } taken || Edge(sides[false]) is not { } fallthrough) return false;
        if (taken.Target == fallthrough.Target) return match.Fail("条件续接点相同");
        match.Covered.UnionWith(covered);
        match.Result = result;
        match.Exit = (taken.Target, 0);
        match.ExitCopies = [];
        match.Continuation = new ManagedBranch(0, predicate, taken, fallthrough);
        return true;
    }

    /// <summary>分支条件的比较形式：布尔值 b 即 b != 0，其否定即 b == 0（0/1 归一后条件可以不带显式比较）。</summary>
    private ComparisonValue? AsComparison(ManagedValue condition) => condition switch
    {
        ComparisonValue comparison => comparison,
        NegatedValue { Operand: var operand } when types.Kind(operand.Type) == TypeKind.Bool
            => new ComparisonValue(Cond.Eq, operand, new ConstantValue(0, operand.Type, operand.Width), types.Boolean),
        _ when types.Kind(condition.Type) == TypeKind.Bool
            => new ComparisonValue(Cond.Ne, condition, new ConstantValue(0, condition.Type, condition.Width), types.Boolean),
        _ => null,
    };

    private static bool? ConstantComparison(Cond condition, ConstantValue left, ConstantValue right)
    {
        if (left.Width != right.Width || left.Width is not (8 or 16 or 32 or 64)) return null;
        var a = left.Bits & Expr.Mask(left.Width);
        var b = right.Bits & Expr.Mask(right.Width);
        var sign = 1UL << (left.Width - 1);
        return condition switch
        {
            Cond.Eq => a == b, Cond.Ne => a != b,
            Cond.Ult => a < b, Cond.Ule => a <= b, Cond.Ugt => a > b, Cond.Uge => a >= b,
            Cond.Slt => (a ^ sign) < (b ^ sign), Cond.Sle => (a ^ sign) <= (b ^ sign),
            Cond.Sgt => (a ^ sign) > (b ^ sign), Cond.Sge => (a ^ sign) >= (b ^ sign),
            _ => null,
        };
    }
}
