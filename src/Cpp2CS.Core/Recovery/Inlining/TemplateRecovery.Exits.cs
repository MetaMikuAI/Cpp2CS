using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 内联区域的出口。模板每条返回路径在调用方的终点由 <see cref="Finish"/> 求出：先纳入组成返回值的分段读取，
/// 再沿无条件跳转到达续接点。各路径的终点按返回值的使用者归为一类，由 <see cref="ConcludeExit"/> 统一判定：
/// 条件（返回值与常量比较后分支）、返回（调用方直接返回该值）、汇合（各路径在同一点继续，返回值由同一个局部承接或被丢弃）。
/// </summary>
internal sealed partial class TemplateRecovery
{
    private bool ConcludeExit(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks) =>
        ConcludeBranch(match, method, body, blocks) || ConcludeReturn(match, method) || ConcludeJoin(match, method, body, blocks);

    /// <summary>模板的一条路径返回：调用方从当前位置沿无条件跳转到达的点是这条路径的出口，连同出口边上的复制记为一个终点。</summary>
    private bool Finish(Walker caller, InlineMatch match, ManagedValue? result)
    {
        if (result is not null && !CaptureReturnValue(caller, match, result)) return false;
        var copies = new List<(LocalValue, ManagedValue)>();
        var continuation = false;
        for (var steps = 0; steps < 16 && caller.Current is ManagedJump jump; steps++)
        {
            // 共享续接中的无副作用复制可旁路；复制逐边组合，其他入边仍保留原块。
            continuation |= caller.Index == 0 && caller.Blocks.Values.Count(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == caller.Block)) > 1;
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

    /// <summary>
    /// 汇合：各路径须在同一点结束。有返回值时，承接它的是调用方在出口处的同一个局部：出口复制的目标（多路径时即合流处的 φ）或区域内定义的局部，
    /// 在每条路径上都等于模板的返回值；其余出口复制在各路径上相同。返回值被丢弃时，额外求值的返回项不得引入异常或副作用。
    /// </summary>
    private bool ConcludeJoin(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        if (match.Ends.Any(e => e.Returns)) return match.Fail("返回路径与续接路径混合");
        if (match.Ends.Count == 0 || match.Ends.Any(e => e.Exit != match.Ends[0].Exit))
            return match.Fail($"各路径在调用方的出口不同：{string.Join(", ", match.Ends.Select(e => $"0x{e.Exit.Block:x}+{e.Exit.Index}"))}");
        LocalValue? result = null;
        LocalValue? returned = null;
        ManagedValue? view = null;
        IReadOnlyList<(LocalValue Target, ManagedValue Value)> projections = [];
        var copied = match.Covered.SelectMany(p => ManagedValues.Edges(blocks[p.Block].Statements[p.Index]))
            .SelectMany(e => e.Copies).Select(c => c.Target)
            .Concat(match.Ends.SelectMany(e => e.Copies.Select(c => c.Target))).DistinctBy(l => l.Variable).ToArray();
        if (!ManagedTypes.IsVoid(method.Method.ReturnType))
        {
            var returnType = method.Concrete(method.Method.ReturnType);
            var first = match.Ends[0];
            if (first.Result is null) return false;
            var candidates = copied.Concat(first.Env.Keys.Where(match.Defined.ContainsKey).Select(v => LocalOf(match, v)).OfType<LocalValue>())
                .Where(l => l.Type.Equals(returnType) || types.Kind(returnType) == TypeKind.Bool && types.Kind(l.Type) == TypeKind.Int).DistinctBy(l => l.Variable);
            foreach (var candidate in candidates)
            {
                var trial = new Dictionary<int, ManagedValue>(match.Binding);
                bool Carries(InlineEnd end)
                {
                    var held = end.Env.GetValueOrDefault(candidate.Variable);
                    return held is not null && end.Result is { } value
                        && Unify(candidate.Type.Equals(returnType) ? value : new ConversionValue(ConvKind.ZeroExtend, value, candidate.Type, candidate.Width), held, trial);
                }
                if (!match.Ends.All(Carries)) continue;
                foreach (var (key, value) in trial) match.Binding[key] = value;
                result = candidate;
                break;
            }
            if (result is null && JoinFields(match, returnType, copied) is { } aggregate)
                (result, projections) = aggregate;
            if (result is null && JoinPredicate(match, returnType, copied) is { } predicate)
                (result, returned, view) = predicate;
            // 调用结果可被丢弃；额外求值的返回项不得引入异常或副作用。区域外使用仍由 Replace 检查。
            if (result is null && !match.Ends.All(e => e.Result is { } value && NonThrowingInlineValue(value)))
                return match.Fail("返回值没有承接的局部，且无法证明额外求值无副作用");
        }
        var rest = projections.ToList();
        ManagedValue Project(InlineEnd end, ManagedValue value)
        {
            foreach (var projection in projections)
                if (end.Env.GetValueOrDefault(projection.Target.Variable) is { } leaf && SameTerm(value, leaf)) return projection.Value;
            return MapTerm(value, child => Project(end, child));
        }
        foreach (var target in copied.Where(c => (result is null || c.Variable != result.Variable)
            && !projections.Any(p => p.Target.Variable == c.Variable)))
        {
            var exit = match.Ends[0].Exit;
            var held = match.Ends.Select(e => e.Env.GetValueOrDefault(target.Variable) ?? target).ToArray();
            if (!LiveAt(body, blocks, exit.Block, exit.Index, target.Variable) && held.All(NonThrowingInlineValue)) continue;
            if (projections.Count > 0) held = match.Ends.Select((end, i) => Project(end, held[i])).ToArray();
            if (held.Skip(1).Any(v => !SameTerm(v, held[0]))) return match.Fail("出口复制在各路径上不同");
            rest.Add((target, held[0]));
        }
        match.Exit = match.Ends[0].Exit;
        match.ExitCopies = rest;
        match.Result = result;
        if (result is not null && view is not null)
        {
            match.ResultStorage = result;
            match.Result = returned;
            match.ExitCopies = [.. rest, (result, view)];
        }
        else if (result is not null && !result.Type.Equals(method.Concrete(method.Method.ReturnType)))
        {
            match.ResultStorage = result;
            match.Result = NewLocal(method.Concrete(method.Method.ReturnType));
            match.ExitCopies = [.. rest, (result, new ConversionValue(ConvKind.ZeroExtend, match.Result, result.Type, result.Width))];
        }
        return true;
    }

    /// <summary>结构体返回值可由多个字段局部承接；每条返回路径都须证明这些局部对应同一组完整叶子。</summary>
    private (LocalValue Result, IReadOnlyList<(LocalValue Target, ManagedValue Value)> Copies)? JoinFields(
        InlineMatch match, TypeRef returnType, IReadOnlyList<LocalValue> copied)
    {
        if (returnType is not DefinitionRef structure || types.Kind(structure) != TypeKind.Struct
            || match.Ends.Any(e => e.Result is null || !e.Result.Type.Equals(returnType))) return null;
        var leaves = types.Leaves(structure).ToArray();
        if (leaves.Length == 0) return null;
        var result = NewLocal(returnType);
        var projections = new List<(LocalValue Target, ManagedValue Value)>();
        var trial = new Dictionary<int, ManagedValue>(match.Binding);
        foreach (var (path, type, _) in leaves)
        {
            ManagedValue value = result;
            foreach (var field in path)
            {
                if (!fields.Accessible(field, value.Type)) return null;
                var fieldType = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
                value = new FieldValue(value, field, fieldType, Width(fieldType));
            }
            bool Carries(InlineEnd end, LocalValue local, Dictionary<int, ManagedValue> binding) =>
                ReturnedField(end, path) is { } expected
                && end.Env.GetValueOrDefault(local.Variable) is { } actual && Unify(expected, actual, binding);
            var matches = 0;
            foreach (var local in copied.Where(c => c.Type.Equals(type) && !projections.Any(p => p.Target.Variable == c.Variable)))
            {
                var binding = new Dictionary<int, ManagedValue>(trial);
                if (!match.Ends.All(e => Carries(e, local, binding))) continue;
                trial = binding;
                projections.Add((local, value));
                matches++;
            }
            if (matches == 0) return null;
        }
        foreach (var (key, value) in trial) match.Binding[key] = value;
        return (result, projections);
    }

    /// <summary>完整结构体项与分散承接的字段比较；字段读取沿用该返回路径的调用代数。</summary>
    private ManagedValue? ReturnedField(InlineEnd end, IReadOnlyList<FieldRef> path)
    {
        if (end.Result is ComposedValue composed)
            return composed.Leaves.FirstOrDefault(l => l.Path.SequenceEqual(path)).Value;
        var value = end.Result!;
        foreach (var field in path)
        {
            var type = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
            value = new Observed(new FieldValue(value, field, type, Width(type)), end.Epoch);
        }
        return value;
    }

    /// <summary>合流可承接返回值的比较结果；用一条非常量路径提出表达式，再逐路径验证，包括已折叠成常量的路径。</summary>
    private (LocalValue Storage, LocalValue Result, ManagedValue View)? JoinPredicate(InlineMatch match, TypeRef returnType, IReadOnlyList<LocalValue> copied)
    {
        var result = NewLocal(returnType);
        ManagedValue? Held(InlineEnd end, LocalValue target) => end.Env.GetValueOrDefault(target.Variable);
        foreach (var end in match.Ends.Where(e => e.Result is not null and not ConstantValue))
        foreach (var target in copied.Where(c => types.Kind(c.Type) == TypeKind.Bool))
        {
            if (Held(end, target) is not { } held || ReturnedPredicate(held, end.Result!, result) is not { } predicate) continue;
            var trial = new Dictionary<int, ManagedValue>(match.Binding);
            bool Carries(InlineEnd path)
            {
                if (path.Result is not { } value || Held(path, target) is not { } actual) return false;
                ManagedValue Substitute(ManagedValue child) => child.Equals(result) ? value : MapTerm(child, Substitute);
                var expected = (ComparisonValue)Substitute(predicate);
                if (expected is { Left: ConstantValue left, Right: ConstantValue right }
                    && ConstantComparison(expected.Condition, left, right) is { } constant)
                    return Unify(new ConstantValue(constant ? 1UL : 0UL, types.Boolean, 8), actual, trial);
                return Unify(expected, actual, trial);
            }
            if (!match.Ends.All(Carries)) continue;
            foreach (var (key, value) in trial) match.Binding[key] = value;
            return (target, result, predicate);
        }
        return null;
    }

    private ComparisonValue? ReturnedPredicate(ManagedValue tested, ManagedValue returned, LocalValue result)
    {
        if (types.Kind(result.Type) == TypeKind.Bool)
        {
            if (SameTerm(tested, returned))
                return new ComparisonValue(Cond.Ne, result, new ConstantValue(0, result.Type, result.Width), types.Boolean);
            if (SameTerm(Negate(tested), returned))
                return new ComparisonValue(Cond.Eq, result, new ConstantValue(0, result.Type, result.Width), types.Boolean);
        }
        if (types.Kind(result.Type) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Reference) || AsComparison(tested) is not { } comparison) return null;
        ManagedValue? Carrier(ManagedValue value) => value switch
        {
            _ when SameTerm(value, returned) => result,
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } conversion when Carrier(conversion.Operand) is { } operand
                => conversion with { Operand = operand },
            _ => null,
        };
        ComparisonValue? predicate = null;
        if (Carrier(comparison.Left) is { } left && comparison.Right is ConstantValue) predicate = comparison with { Left = left };
        else if (Carrier(comparison.Right) is { } right && comparison.Left is ConstantValue) predicate = comparison with { Right = right };
        if (predicate is not null && types.Kind(result.Type) == TypeKind.Reference && (predicate.Condition is not (Cond.Eq or Cond.Ne)
            || predicate.Left is not ConstantValue { Bits: 0 } && predicate.Right is not ConstantValue { Bits: 0 })) return null;
        return predicate;
    }


    /// <summary>条件：返回值直接与常量比较并分支时，证明各路径按比较结果分别到达同一对条件出口。</summary>
    private bool ConcludeBranch(InlineMatch match, MethodRef method, ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        if (ManagedTypes.IsVoid(method.Method.ReturnType) || match.Ends.Count == 0 || match.Ends.Any(e => e.Returns)) return false;
        var returnType = method.Concrete(method.Method.ReturnType);
        if (types.Kind(returnType) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Reference)) return false;
        Walker At(InlineEnd end) => new() { Blocks = blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Env = new(end.Env) };
        ComparisonValue? predicate = null;
        var result = NewLocal(returnType);
        foreach (var end in match.Ends)
        {
            var walker = At(end);
            if (end.Result is not { } returned || returned is ConstantValue || walker.Current is not ManagedBranch branch || Term(walker, branch.Condition) is not { } tested) continue;
            predicate = ReturnedPredicate(tested, returned, result);
            if (predicate is not null) break;
        }
        if (predicate is null) return false;
        ManagedValue Apply(ManagedValue value)
        {
            ManagedValue Substitute(ManagedValue child) => child.Equals(result) ? value : MapTerm(child, Substitute);
            return Substitute(predicate);
        }
        var exits = new Dictionary<bool, InlineEnd>();
        var covered = new HashSet<(ulong Block, int Index)>();
        InlineEnd WithResult(InlineEnd end, ManagedValue returned)
        {
            ManagedValue ReplaceResult(ManagedValue value) => Unify(returned, value, new(match.Binding)) ? result : MapTerm(value, ReplaceResult);
            return end with
            {
                Copies = end.Copies.Select(c => (c.Target, ReplaceResult(c.Value))).ToArray(),
                Env = end.Env.ToDictionary(p => p.Key, p => ReplaceResult(p.Value)),
            };
        }
        bool Note(bool outcome, InlineEnd end)
        {
            if (end.Exit.Index != 0) return match.Fail("条件续接点位于块中间");
            var copies = end.Copies.GroupBy(c => c.Target.Variable).Select(g => g.Last()).ToArray();
            end = end with { Copies = copies };
            if (exits.TryGetValue(outcome, out var prior))
            {
                if (prior.Exit != end.Exit) return match.Fail("相同返回条件的续接点不同");
                var targets = prior.Copies.Select(c => c.Target).Concat(end.Copies.Select(c => c.Target)).DistinctBy(l => l.Variable).ToArray();
                ManagedValue? Held(InlineEnd e, LocalValue target) => e.Copies.FirstOrDefault(c => c.Target.Variable.Equals(target.Variable)).Value ?? e.Env.GetValueOrDefault(target.Variable);
                if (targets.Any(t => Held(prior, t) is not { } value || Held(end, t) is not { } other || !SameTerm(value, other))) return match.Fail("条件续接的局部值不同");
                exits[outcome] = end with { Copies = targets.Select(t => (t, Held(end, t)!)).ToArray() };
                return true;
            }
            exits[outcome] = end;
            return true;
        }
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
            var finish = trial.Ends[0];
            return Note(outcome, WithResult(finish with { Copies = copies.Concat(finish.Copies).ToArray() }, end.Result!));
        }
        foreach (var end in match.Ends)
        {
            if (end.Result is not { } returned) return false;
            var expected = Apply(returned);
            var walker = At(end);
            if (expected is ComparisonValue { Left: ConstantValue left, Right: ConstantValue right } constant
                && ConstantComparison(constant.Condition, left, right) is { } outcome)
            {
                if (!Note(outcome, WithResult(end, returned))) return false;
            }
            else if (walker.Current is ManagedBranch branch && Term(walker, branch.Condition) is { } condition)
            {
                var canonical = Canonical(expected);
                bool same;
                if (Unify(canonical, Canonical(condition), match.Binding)) same = true;
                else if (Unify(canonical, Canonical(Negate(condition)), match.Binding)) same = false;
                else return match.Fail("返回值与调用方的比较不同");
                covered.Add(end.Exit);
                if (!Along(end, branch.Taken, same) || !Along(end, branch.Fallthrough, !same)) return false;
            }
            else return match.Fail("返回路径不受同一条件支配");
        }
        if (!exits.TryGetValue(true, out var yes) || !exits.TryGetValue(false, out var no) || yes.Exit == no.Exit) return false;
        foreach (var candidate in match.Locals.Values.Where(l => l.Type.Equals(returnType)))
        {
            ManagedValue? Held(InlineEnd end) => end.Copies.FirstOrDefault(c => c.Target.Variable == candidate.Variable).Value
                ?? end.Env.GetValueOrDefault(candidate.Variable);
            if (!new[] { yes, no }.Any(e => Held(e) == result)) continue;
            if (!new[] { yes, no }.All(e => Held(e) == result || !LiveAt(body, blocks, e.Exit.Block, e.Exit.Index, candidate.Variable))) continue;
            match.ResultStorage = candidate;
            InlineEnd Carry(InlineEnd end) => end with { Copies = [.. end.Copies.Where(c => c.Target.Variable != candidate.Variable), (candidate, result)] };
            yes = Carry(yes);
            no = Carry(no);
            break;
        }
        ManagedEdge Edge(InlineEnd end) => new(end.Exit.Block, end.Copies.Select(c => new ManagedCopy(c.Target, c.Value)).ToArray());
        match.Covered.UnionWith(covered);
        match.Result = result;
        match.Exit = yes.Exit;
        match.ExitCopies = [];
        match.Continuation = new ManagedBranch(0, predicate, Edge(yes), Edge(no));
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
