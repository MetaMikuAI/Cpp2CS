using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Shape;

using Storage = Cpp2CS.Ir.Storage;

/// <summary>
/// 通用路径拆分：clang 把不同路径上的同构访问合并为“φ 出的地址 + 一次访问”。合流块中某条语句在需要单一实体的位置
/// （读写地址的根、调用目标、调用经指针访问的实参）使用本块的 φ，而 φ 的来源是不同的实体（不同对象或字段的地址、
/// 不同的局部地址、不同的元数据实体）时，把合流块复制回各入边，使每条路径上的访问各自指向一个实体。
/// 这是恢复层唯一修改控制流图的步骤：进入合流块的关键边先切开，合流块连同终结语句复制到每个前驱，
/// φ 在各副本中取对应来源，副本中重复的定义经 <see cref="SsaRepair"/> 恢复为 SSA。
/// </summary>
internal static class PathSplitting
{
    private const ulong SyntheticBase = 0xffff_fff0_0000_0000;
    private const int Rounds = 8;

    private const int MaxStatements = 96;
    /// <summary>复制的语句总量上限；分支很多的 switch 汇到短合流块也在此内。</summary>
    private const int MaxCopiedStatements = 16 * MaxStatements;

    public static int Run(MachineFunction function, Func<MachineFunction, ValueModel> evaluate, Func<ValueModel, TypeOracle> typing, ICallModel calls, Storage stackPointer,
        Func<MachineFunction, bool>? recognize = null)
    {
        var split = 0;
        for (var round = 0; round < Rounds; round++)
        {
            var model = evaluate(function);
            var oracle = typing(model);
            oracle.MergedAddresses = false;
            var merge = Demands(model, oracle).FirstOrDefault(b => b.Handler is null && !b.IsLandingPad && b.Predecessors.Count >= 2
                && b.Statements.Count <= MaxStatements && b.Predecessors.Count * b.Statements.Count <= MaxCopiedStatements && b.Predecessors.Distinct().Count() == b.Predecessors.Count && !b.Successors.Contains(b)
                && b.Predecessors.All(p => !p.IsLandingPad));
            if (merge is null) break;
            SplitCriticalEdges(function, merge);
            if (!Duplicate(function, merge, calls, stackPointer)) break;
            split++;
            var errors = Machine.Ssa.Lowering.Cleanup(function);
            if (errors.Count > 0) throw new InvalidOperationException($"路径拆分后 SSA 不成立：{errors[0]}");
            // 分开合流之后才完整的运行时惯用法。
            if (recognize?.Invoke(function) == true)
            {
                errors = Machine.Ssa.Lowering.Cleanup(function);
                if (errors.Count > 0) throw new InvalidOperationException($"路径拆分后 SSA 不成立：{errors[0]}");
            }
        }
        return split;
    }

    /// <summary>把合流块连同终结语句复制到每个前驱。前驱都以跳转进入合流块。</summary>
    private static bool Duplicate(MachineFunction function, Block merge, ICallModel calls, Storage stackPointer)
    {
        var predecessors = merge.Predecessors.ToArray();
        if (predecessors.Any(p => p.Statements.LastOrDefault() is not Ir.Jump jump || jump.Target != merge.Start)) return false;
        var phis = merge.Statements.OfType<Phi>().ToArray();
        var body = merge.Statements.Where(s => s is not Phi).ToArray();
        var successors = merge.Successors.ToArray();
        var exitSources = successors.Select(s => (s, s.Predecessors.IndexOf(merge))).ToArray();
        var repaired = new HashSet<Variable>(phis.Select(p => p.Target));
        var versions = function.Blocks.SelectMany(b => b.Statements).SelectMany(Defined).GroupBy(v => v.Storage).ToDictionary(g => g.Key, g => g.Max(v => v.Version) + 1);
        foreach (var statement in body)
            if (statement is Define define) repaired.Add(define.Target);
            else if (statement is Call call) repaired.UnionWith(call.Defines.Where(d => d is not null));
        for (var j = 0; j < predecessors.Length; j++)
        {
            var from = predecessors[j];
            from.Statements.RemoveAt(from.Statements.Count - 1);
            foreach (var phi in phis)
                from.Statements.Add(new Define(phi.Address, phi.Target, phi.Sources[j] is { } source ? new Use(source, phi.Target.Width) : new Unknown("φ 来源缺失", phi.Target.Width)));
            foreach (var statement in body)
            {
                if (statement is not Call call) { from.Statements.Add(statement); continue; }
                var fresh = call.Defines.Select(d => d is null ? null! : d with { Version = versions[d.Storage]++ }).ToArray();
                var copy = call.Duplicate() with { Defines = fresh };
                from.Statements.Add(copy);
                for (var r = 0; r < fresh.Length; r++)
                    if (call.Defines[r] is { } original)
                        from.Statements.Insert(from.Statements.Count, new Define(call.Address, original, new Use(fresh[r], original.Width)));
            }
            // 调用之后的复制定义必须位于终结语句之前。
            MoveTerminatorLast(from);
            MachineFunction.RemoveEdge(from, merge);
            foreach (var (successor, index) in exitSources)
            {
                MachineFunction.AddEdge(from, successor);
                for (var i = 0; i < successor.Statements.Count && successor.Statements[i] is Phi phi; i++)
                    successor.Statements[i] = phi with { Sources = [.. phi.Sources, phi.Sources[index]] };
            }
        }
        foreach (var successor in successors) MachineFunction.RemoveEdge(merge, successor);
        function.Renumber();
        SsaRepair.Run(function, repaired, calls, stackPointer);
        return true;
    }

    private static void MoveTerminatorLast(Block block)
    {
        var index = block.Statements.ToList().FindLastIndex(s => s is Ir.Jump or Ir.Branch or IndirectJump or Return or Trap or Call { Kind: CallKind.Tail or CallKind.TailIndirect });
        if (index < 0 || index == block.Statements.Count - 1) return;
        var terminator = block.Statements[index];
        block.Statements.RemoveAt(index);
        block.Statements.Add(terminator);
    }

    private static IEnumerable<Variable> Defined(Stmt statement) => statement switch
    {
        Phi p => [p.Target],
        Define d => [d.Target],
        Call c => c.Defines.OfType<Variable>(),
        _ => [],
    };

    /// <summary>需要拆分的合流块。</summary>
    private static IEnumerable<Block> Demands(ValueModel model, TypeOracle oracle)
    {
        foreach (var block in model.Function.Blocks)
        {
            if (block.Predecessors.Count < 2 || !block.Statements.Any(s => s is Phi)) continue;
            // 访问可能在合流块之后的直线路径上（判空把块切开了）：先拆合流块，φ 随之下移，下一轮再拆。
            var current = block;
            for (var steps = 0; steps < 8; steps++)
            {
                if (current.Statements.Any(statement => Singletons(model, oracle, statement).Any(sym => Distinct(sym, block, oracle))))
                {
                    yield return block;
                    break;
                }
                if (current.NormalSuccessors.ToArray() is not [var next] || next.Predecessors.Count != 1 || next == block) break;
                current = next;
            }
        }
    }

    /// <summary>语句中要求单一实体的符号值：尚不能表示为托管位置的地址、调用目标与经指针访问的实参。</summary>
    private static IEnumerable<Sym> Singletons(ValueModel model, TypeOracle oracle, Stmt statement)
    {
        var operands = model.Operands(statement);
        switch (statement)
        {
            case Store store:
                if (oracle.Locate(operands[0], store.Value.Width) is null) yield return operands[0];
                break;
            case Call call:
                yield return operands[0];
                // 没有解析的间接调用：目标从 φ 选出的对象上读取时也按路径处理（不同类型的委托合流后共用一次调用）。
                if (call is { Op: null, Resolved: null, Kind: CallKind.Indirect or CallKind.TailIndirect })
                    foreach (var read in Reads(operands[0]))
                        yield return read.Address;
                // 局部地址、方法实体及运行时操作的类元数据都要求单一实体。
                for (var i = 0; i < call.Arguments.Length; i++)
                    if (SymTable.Resolve(operands[1 + i]) is PhiSym phi && (phi.Sources.All(s => s is not null
                        && (SymTable.Resolve(s) is LocalSym or EntitySym { Symbol.Kind: SymbolKind.Method }
                            || call.Op is not null && SymTable.Resolve(s) is EntitySym { Symbol.Kind: SymbolKind.Class }))
                        || Entities(phi, call.Op is not null) is { Count: > 1 }))
                        yield return phi;
                break;
        }
        foreach (var operand in operands)
            foreach (var read in Reads(operand))
                if (oracle.Locate(read.Address, read.Width) is null) yield return read.Address;
    }

    /// <summary>
    /// φ 选出的元数据实体，来源可以是同样的 φ（多层合流）；有来源不是实体时为 null。
    /// 经回边转传的 φ 不增加实体：只有一个实体时各路径相同，不需要拆分。
    /// </summary>
    private static HashSet<Sym>? Entities(PhiSym phi, bool runtime, bool addresses = false)
    {
        var entities = new HashSet<Sym>();
        var seen = new HashSet<PhiSym>();
        var pending = new Stack<PhiSym>();
        pending.Push(phi);
        while (pending.TryPop(out var current))
        {
            if (!seen.Add(current)) continue;
            foreach (var source in current.Sources)
                switch (source is null ? null : SymTable.Resolve(source))
                {
                    case EntitySym { Symbol.Kind: SymbolKind.Method } entity: entities.Add(entity); break;
                    case EntitySym { Symbol.Kind: SymbolKind.Class } entity when runtime: entities.Add(entity); break;
                    case EntitySym { Symbol.Kind: SymbolKind.StaticFields } entity when addresses: entities.Add(entity); break;
                    case ConstSym { Value: not 0 } constant when addresses: entities.Add(constant); break;
                    case PhiSym nested: pending.Push(nested); break;
                    default: return null;
                }
        }
        return entities;
    }

    private static IEnumerable<ReadSym> Reads(Sym sym)
    {
        var stack = new Stack<Sym>();
        var seen = new HashSet<Sym>();
        stack.Push(sym);
        while (stack.Count > 0)
        {
            var current = SymTable.Resolve(stack.Pop());
            if (!seen.Add(current)) continue;
            switch (current)
            {
                case ReadSym read: yield return read; stack.Push(read.Address); break;
                case SliceSym slice: stack.Push(slice.Base); break;
                case ConcatSym concat: foreach (var part in concat.Parts) stack.Push(part); break;
                case OpSym op: foreach (var arg in op.Args) stack.Push(arg); break;
            }
        }
    }

    /// <summary>地址（或实体）由本块的 φ 选出，且各来源的身份不全相同。</summary>
    private static bool Distinct(Sym sym, Block block, TypeOracle oracle)
    {
        var root = Root(SymTable.Resolve(sym));
        if (root is not PhiSym phi || !ReferenceEquals(phi.Block, block) || phi.Sources.Any(s => s is null)) return false;
        // 多层合流的实体选择：先拆外层，φ 随之下移到前驱，下一轮再拆。
        if (phi.Sources.Any(s => SymTable.Resolve(s!) is PhiSym) && Entities(phi, true, addresses: true) is { } entities) return entities.Count > 1;
        var identities = phi.Sources.Select(s => Identity(SymTable.Resolve(s!), oracle)).ToArray();
        return identities.All(i => i is not null) && identities.Distinct().Count() > 1;
    }

    /// <summary>地址的根：去掉加常量。</summary>
    private static Sym Root(Sym sym)
    {
        while (sym is OpSym { Op.Kind: OperatorKind.Binary, Args: [var left, ConstSym] } add && add.Op.Binary == BinOp.Add) sym = SymTable.Resolve(left);
        return sym is PhiSym { Projection: { } projection } ? projection.Whole : sym;
    }

    /// <summary>来源的身份：实体、局部地址，或去掉常量偏移后的根与偏移。</summary>
    private static object? Identity(Sym sym, TypeOracle oracle)
    {
        var address = oracle.Decompose(sym);
        if (address.Index is not null && oracle.TypeOf(address.Root) is ArrayRef or PointerRef) return address;
        long offset = 0;
        while (sym is OpSym { Op.Kind: OperatorKind.Binary, Args: [var left, ConstSym c] } add && add.Op.Binary == BinOp.Add)
        {
            offset += c.Signed;
            sym = SymTable.Resolve(left);
        }
        return sym switch
        {
            EntitySym or ArgSym or ReadSym or ResultSym or OutSym => (sym, offset),
            // 非零常量是全局地址，如字符串字面量的槽。
            ConstSym { Value: not 0 } => (sym, offset),
            LocalSym local => (local.Space, local.Offset + offset),
            _ => null,
        };
    }

    /// <summary>以条件分支进入合流块的边插入只含跳转的块，使每个前驱都无条件进入合流块。</summary>
    private static void SplitCriticalEdges(MachineFunction function, Block merge)
    {
        for (var j = 0; j < merge.Predecessors.Count; j++)
        {
            var from = merge.Predecessors[j];
            // 机器块可通过隐式落空边进入后继；复制前把它写成显式跳转。
            if (from.NormalSuccessors.ToArray() is [var only] && only == merge
                && from.Statements.LastOrDefault() is not (Ir.Jump or Ir.Branch or IndirectJump or Return or Trap or Call { Kind: CallKind.Tail or CallKind.TailIndirect }))
            {
                from.Statements.Add(new Ir.Jump(from.End, merge.Start));
                if (from.Handler is null) continue;
            }
            // 从 try 内进入合流块的边也要切开：复制的语句不属于 try，不能并入前驱。
            var last = from.Statements.LastOrDefault();
            if (!(last is Ir.Branch { Target: var target, Fallthrough: var fallthrough } && target != fallthrough || last is Ir.Jump && from.Handler is not null)) continue;
            var address = SyntheticBase + (ulong)function.Blocks.Count(b => b.Start >= SyntheticBase);
            var middle = new Block(address) { End = address };
            middle.Statements.Add(new Ir.Jump(address, merge.Start));
            var k = from.Successors.IndexOf(merge);
            from.Successors[k] = middle;
            middle.Predecessors.Add(from);
            middle.Successors.Add(merge);
            merge.Predecessors[j] = middle;
            from.Statements[^1] = last switch
            {
                Ir.Branch branch => branch.Target == merge.Start ? branch with { Target = address } : branch with { Fallthrough = address },
                Ir.Jump jump => jump with { Target = address },
                _ => last!,
            };
            function.Blocks.Add(middle);
        }
        function.Renumber();
    }
}
