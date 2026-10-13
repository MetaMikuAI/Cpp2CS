using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.SemanticCore;

namespace Cpp2CS.Nir;

public static class NirValidator
{
    public static NirValidationResult Validate(NirModule module)
    {
        var errors = ImmutableArray.CreateBuilder<NirDiagnostic>();
        void Error(string code, string message) => errors.Add(new(code, message));
        if (module.Version != NirModule.FormatVersion) Error("version", "不支持的 NIR 格式版本");
        if (module.Functions.IsDefault || module.Externals.IsDefault || module.MemorySpaces.IsDefault || module.DataObjects.IsDefault)
            return new([new("array", "模块集合必须初始化")]);
        var spaces = new Dictionary<string, NirMemorySpace>(StringComparer.Ordinal);
        foreach (var space in module.MemorySpaces)
        {
            if (string.IsNullOrWhiteSpace(space.Id) || !spaces.TryAdd(space.Id, space)) Error("space", "地址空间身份必须唯一且非空");
            if (space.AddressWidth is < 1 or > 4096 || space.LocalBase < 0 || space.LocalLength < 0 ||
                space.AddressWidth is >= 1 and <= 4096 && space.LocalBase + space.LocalLength > (BigInteger.One << space.AddressWidth))
                Error("space-range", "局部分配区间超出明确的地址宽度");
        }
        var dataIds = new HashSet<string>(StringComparer.Ordinal);
        var initial = new Dictionary<(string, BigInteger), (byte Value, bool Writable)>();
        foreach (var data in module.DataObjects)
        {
            if (string.IsNullOrWhiteSpace(data.Id) || !dataIds.Add(data.Id)) Error("data-id", "数据对象身份必须唯一且非空");
            if (data.Bytes.IsDefault) { Error("data-bytes", "数据对象字节必须初始化"); continue; }
            if (!spaces.TryGetValue(data.Space, out var space) || space.AddressWidth is < 1 or > 4096)
            { Error("data-space", "数据对象引用未知地址空间"); continue; }
            if (data.Address < 0 || data.Address + data.Bytes.Length > (BigInteger.One << space.AddressWidth))
                Error("data-range", "数据对象越过地址空间边界");
            if (data.Address < space.LocalBase + space.LocalLength && data.Address + data.Bytes.Length > space.LocalBase)
                Error("data-local-alias", "模块数据与局部分配区间重叠");
            for (var i = 0; i < data.Bytes.Length; i++)
            {
                var key = (data.Space, data.Address + i);
                var item = (data.Bytes[i], data.Writable);
                if (initial.TryGetValue(key, out var prior) && prior != item) Error("data-conflict", "别名数据对象的初值或权限冲突");
                else initial[key] = item;
            }
        }
        var signatures = new Dictionary<string, NirSignature>(StringComparer.Ordinal);
        var outcomes = new Dictionary<string, NirOutcomes>(StringComparer.Ordinal);
        foreach (var function in module.Functions)
        {
            if (string.IsNullOrWhiteSpace(function.Id) || !signatures.TryAdd(function.Id, function.Signature)) Error("function-id", "函数身份必须唯一且非空");
            else outcomes.Add(function.Id, function.Outcomes);
            CheckSignature(function.Signature, spaces, Error);
            CheckOutcomes(function.Outcomes, Error);
        }
        foreach (var external in module.Externals)
        {
            if (string.IsNullOrWhiteSpace(external.Id) || !signatures.TryAdd(external.Id, external.Signature)) Error("external-id", "外部合同与函数身份必须唯一");
            else outcomes.Add(external.Id, external.Outcomes);
            CheckSignature(external.Signature, spaces, Error);
            CheckOutcomes(external.Outcomes, Error);
            if ((external.Effects & ~(NirExternalEffects.ReadMemory | NirExternalEffects.WriteMemory | NirExternalEffects.Environment)) != 0)
                Error("external-effects", "外部合同含未定义效应");
        }
        if (module.Functions.Any(f => f.Signature.Parameters.IsDefault || f.Signature.Results.IsDefault) ||
            module.Externals.Any(f => f.Signature.Parameters.IsDefault || f.Signature.Results.IsDefault)) return new(errors.ToImmutable());
        foreach (var function in module.Functions) ValidateFunction(function, spaces, signatures, outcomes, errors);
        return new(errors.ToImmutable());
    }

    private static void CheckOutcomes(NirOutcomes outcomes, Action<string, string> error)
    {
        if (outcomes == NirOutcomes.None || (outcomes & ~(NirOutcomes.Return | NirOutcomes.Fault | NirOutcomes.Terminate | NirOutcomes.Diverge)) != 0)
            error("outcomes", "函数必须声明有效的可能结果");
    }
    private static void CheckSignature(NirSignature signature, Dictionary<string, NirMemorySpace> spaces, Action<string, string> error)
    {
        if (signature.Parameters.IsDefault || signature.Results.IsDefault) { error("signature", "签名集合必须初始化"); return; }
        foreach (var type in signature.Parameters.Concat(signature.Results))
        {
            CheckType(type, spaces, error);
            if (type is NirEffectType) error("signature-effect", "Effect 通过显式效应通道传递，不列为逻辑参数或结果");
        }
    }
    private static void CheckType(NirType type, Dictionary<string, NirMemorySpace> spaces, Action<string, string> error)
    {
        switch (type)
        {
            case NirBitsType bits when bits.Width is >= 1 and <= 4096: break;
            case NirEffectType: break;
            case NirAddressType address when spaces.TryGetValue(address.Space, out var space) && address.Width == space.AddressWidth: break;
            case NirFunctionType function: CheckSignature(function.Signature, spaces, error); CheckOutcomes(function.Outcomes, error); break;
            default: error("type", "类型无效、位宽不受支持或地址空间未声明"); break;
        }
    }

    private static void ValidateFunction(NirFunction function, Dictionary<string, NirMemorySpace> spaces,
        Dictionary<string, NirSignature> signatures, Dictionary<string, NirOutcomes> outcomes,
        ImmutableArray<NirDiagnostic>.Builder errors)
    {
        void Error(string code, string message, NirBlockId? block = null, int? op = null) => errors.Add(new(code, message, function.Id, block, op));
        if (function.Blocks.IsDefault || function.AdditionalEntries.IsDefault || function.Signature.Parameters.IsDefault || function.Signature.Results.IsDefault)
        { Error("function-array", "函数集合必须初始化"); return; }
        foreach (var block in function.Blocks)
        {
            if (block.Parameters.IsDefault || block.Operations.IsDefault) { Error("block-array", "块集合必须初始化", block.Id); return; }
            foreach (var operation in block.Operations)
                if (operation is NirPure { Inputs.IsDefault: true } or NirCall { Arguments.IsDefault: true } or NirCall { Results.IsDefault: true })
                { Error("operation-array", "操作集合必须初始化", block.Id); return; }
            if (NirInspection.Edges(block.Terminator).Any(e => e.Arguments.IsDefault) ||
                block.Terminator is NirReturn { Values.IsDefault: true } or NirTailCall { Arguments.IsDefault: true } or NirNoReturnCall { Arguments.IsDefault: true })
            { Error("terminator-array", "终结操作集合必须初始化", block.Id); return; }
        }
        var blocks = new Dictionary<NirBlockId, NirBlock>();
        var definitions = new Dictionary<NirValueId, (NirValue Value, NirBlockId Block, int Position)>();
        foreach (var block in function.Blocks)
        {
            if (block.Id.Id < 0 || !blocks.TryAdd(block.Id, block)) Error("block-id", "块身份必须唯一且非负", block.Id);
            if (block.Parameters.IsDefault || block.Operations.IsDefault) { Error("block-array", "块集合必须初始化", block.Id); continue; }
            void Define(NirValue value, int position)
            {
                CheckType(value.Type, spaces, (c, m) => Error(c, m, block.Id, position));
                if (value.Id.Id < 0 || !definitions.TryAdd(value.Id, (value, block.Id, position))) Error("ssa-definition", "SSA 值必须恰好定义一次", block.Id, position);
            }
            foreach (var parameter in block.Parameters) Define(parameter, -1);
            for (var i = 0; i < block.Operations.Length; i++)
                foreach (var value in NirInspection.Results(block.Operations[i])) Define(value, i);
            if (block.Parameters.Length == 0 || block.Parameters[^1].Type is not NirEffectType || block.Parameters.Count(p => p.Type is NirEffectType) != 1)
                Error("block-effect", "每个块最后一个参数必须是唯一的 Effect", block.Id);
        }
        if (blocks.Count != function.Blocks.Length || function.Blocks.Any(b => b.Parameters.IsDefault || b.Operations.IsDefault)) return;
        var entries = new HashSet<NirBlockId>(function.AdditionalEntries) { function.Entry };
        if (entries.Count != function.AdditionalEntries.Length + 1) Error("entries", "入口不得重复");
        foreach (var entry in entries)
        {
            if (!blocks.TryGetValue(entry, out var block)) { Error("entry", "入口块不存在", entry); continue; }
            if (!NirInspection.TypesEqual(block.Parameters.Select(p => p.Type), function.Signature.Parameters.Append(NirEffectType.Instance)))
                Error("entry-signature", "每个外部入口必须与逻辑签名及 Effect 一致", entry);
        }
        var predecessors = blocks.Keys.ToDictionary(id => id, _ => new HashSet<NirBlockId>());
        foreach (var block in function.Blocks)
            foreach (var edge in NirInspection.Edges(block.Terminator))
            {
                if (!blocks.TryGetValue(edge.Target, out var target)) { Error("edge-target", "边目标不存在", block.Id); continue; }
                predecessors[edge.Target].Add(block.Id);
                if (edge.Arguments.IsDefault || !NirInspection.TypesEqual(edge.Arguments.Select(x => x.Type), target.Parameters.Select(x => x.Type)))
                    Error("edge-arguments", "每条边的参数数量及类型必须匹配目标块", block.Id);
            }
        var reachable = new HashSet<NirBlockId>();
        var pending = new Queue<NirBlockId>(entries.Where(blocks.ContainsKey));
        while (pending.TryDequeue(out var id))
            if (reachable.Add(id)) foreach (var edge in NirInspection.Edges(blocks[id].Terminator)) if (blocks.ContainsKey(edge.Target)) pending.Enqueue(edge.Target);
        foreach (var block in function.Blocks) if (!reachable.Contains(block.Id)) Error("unreachable-block", "块不能从任何声明入口到达", block.Id);
        var dominance = reachable.ToDictionary(id => id, id => entries.Contains(id) ? new HashSet<NirBlockId> { id } : new HashSet<NirBlockId>(reachable));
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var id in reachable.Where(id => !entries.Contains(id)))
            {
                var parents = predecessors[id].Where(reachable.Contains).ToArray();
                var next = parents.Length == 0 ? new HashSet<NirBlockId>() : new HashSet<NirBlockId>(dominance[parents[0]]);
                foreach (var parent in parents.Skip(1)) next.IntersectWith(dominance[parent]);
                next.Add(id);
                if (!next.SetEquals(dominance[id])) { dominance[id] = next; changed = true; }
            }
        }
        if (!function.Outcomes.HasFlag(NirOutcomes.Diverge))
        {
            var degrees = reachable.ToDictionary(id => id, id => predecessors[id].Count(reachable.Contains));
            var acyclic = new Queue<NirBlockId>(degrees.Where(p => p.Value == 0).Select(p => p.Key));
            var removed = 0;
            while (acyclic.TryDequeue(out var id))
            {
                removed++;
                foreach (var target in NirInspection.Edges(blocks[id].Terminator).Select(e => e.Target).Distinct().Where(reachable.Contains))
                    if (--degrees[target] == 0) acyclic.Enqueue(target);
            }
            if (removed != reachable.Count) Error("loop-outcome", "尚无终止证明的控制流环必须允许 Diverge");
        }
        foreach (var block in function.Blocks)
        {
            void Use(NirValue value, int position)
            {
                if (!definitions.TryGetValue(value.Id, out var definition)) { Error("ssa-use", "使用未定义的 SSA 值", block.Id, position); return; }
                if (!NirInspection.TypeEquals(value.Type, definition.Value.Type)) Error("ssa-type", "引用类型与定义不一致", block.Id, position);
                if (definition.Block == block.Id ? definition.Position >= position : !dominance.TryGetValue(block.Id, out var dom) || !dom.Contains(definition.Block))
                    Error("ssa-dominance", "SSA 定义不支配使用", block.Id, position);
            }
            var effect = block.Parameters.LastOrDefault();
            for (var i = 0; i < block.Operations.Length; i++)
            {
                var operation = block.Operations[i];
                foreach (var input in NirInspection.Inputs(operation)) Use(input, i);
                if (NirInspection.Flow(operation) is { } flow)
                {
                    if (flow.Input.Id != effect.Id || flow.Input.Type is not NirEffectType || flow.Output.Type is not NirEffectType)
                        Error("effect-chain", "效应必须按块内顺序接续唯一的 Effect", block.Id, i);
                    effect = flow.Output;
                }
                CheckOperation(operation, signatures, (c, m) => Error(c, m, block.Id, i));
                if (operation is NirFunctionConstant { Result.Type: NirFunctionType reference } symbol &&
                    outcomes.TryGetValue(symbol.Function, out var symbolOutcomes) && (symbolOutcomes & ~reference.Outcomes) != 0)
                    Error("function-outcomes", "函数值合同遗漏实际目标的可能出口", block.Id, i);
                if (operation is NirLoad or NirStore or NirLocalAlloc && !function.Outcomes.HasFlag(NirOutcomes.Fault))
                    Error("memory-outcome", "可能失败的内存操作必须声明函数 Fault 出口", block.Id, i);
                if (operation is NirCall call) CheckCallOutcomes(call.Target, false, function, outcomes, (c, m) => Error(c, m, block.Id, i));
            }
            foreach (var input in NirInspection.Inputs(block.Terminator)) Use(input, block.Operations.Length);
            foreach (var edge in NirInspection.Edges(block.Terminator))
                if (edge.Arguments.Length == 0 || edge.Arguments[^1].Id != effect.Id) Error("edge-effect", "边必须传出当前 Effect", block.Id);
            switch (block.Terminator)
            {
                case NirBranch branch when branch.Condition.Type is not NirBitsType { Width: 1 }: Error("branch-condition", "分支条件必须是 Bits(1)", block.Id); break;
                case NirReturn ret:
                    if (!NirInspection.TypesEqual(ret.Values.Select(v => v.Type), function.Signature.Results)) Error("return-signature", "返回值不匹配函数签名", block.Id);
                    if (ret.Effect.Id != effect.Id || ret.Effect.Type is not NirEffectType) Error("return-effect", "返回必须传出当前 Effect", block.Id);
                    if (!function.Outcomes.HasFlag(NirOutcomes.Return)) Error("return-outcome", "函数合同没有正常返回出口", block.Id);
                    break;
                case NirTailCall tail:
                    CheckCall(tail.Target, tail.Arguments, function.Signature.Results, signatures, (c, m) => Error(c, m, block.Id));
                    CheckCallOutcomes(tail.Target, true, function, outcomes, (c, m) => Error(c, m, block.Id));
                    if (tail.Effect.Id != effect.Id || tail.Effect.Type is not NirEffectType) Error("tail-effect", "尾调用必须传出当前 Effect", block.Id);
                    break;
                case NirNoReturnCall call:
                    var noReturnSignature = call.Target switch
                    {
                        NirDirectTarget direct => signatures.GetValueOrDefault(direct.Function),
                        NirIndirectTarget { Function.Type: NirFunctionType type } => type.Signature,
                        _ => null
                    };
                    CheckCall(call.Target, call.Arguments, noReturnSignature?.Results ?? [], signatures, (c, m) => Error(c, m, block.Id));
                    if (call.Target is NirDirectTarget target && outcomes.TryGetValue(target.Function, out var callOutcomes) && callOutcomes.HasFlag(NirOutcomes.Return))
                        Error("no-return-contract", "无返回调用要求被调合同排除 Return", block.Id);
                    if (call.Target is NirIndirectTarget { Function.Type: NirFunctionType indirect } && indirect.Outcomes.HasFlag(NirOutcomes.Return))
                        Error("no-return-contract", "无返回间接调用要求函数值合同排除 Return", block.Id);
                    CheckCallOutcomes(call.Target, true, function, outcomes, (c, m) => Error(c, m, block.Id));
                    if (call.Effect.Id != effect.Id || call.Effect.Type is not NirEffectType) Error("no-return-effect", "无返回调用必须传出当前 Effect", block.Id);
                    break;
                case NirFault fault:
                    if (!function.Outcomes.HasFlag(NirOutcomes.Fault) || fault.Effect.Id != effect.Id || fault.Effect.Type is not NirEffectType || string.IsNullOrWhiteSpace(fault.Code))
                        Error("fault", "Fault 必须符合函数合同并使用当前 Effect", block.Id);
                    break;
                case NirTerminate stop:
                    if (!function.Outcomes.HasFlag(NirOutcomes.Terminate) || stop.Effect.Id != effect.Id || stop.Effect.Type is not NirEffectType || string.IsNullOrWhiteSpace(stop.Reason))
                        Error("terminate", "Terminate 必须符合函数合同并使用当前 Effect", block.Id);
                    break;
            }
        }
    }

    private static void CheckCallOutcomes(NirCallTarget target, bool tail, NirFunction owner,
        Dictionary<string, NirOutcomes> outcomes, Action<string, string> error)
    {
        var possible = target switch
        {
            NirDirectTarget direct => outcomes.GetValueOrDefault(direct.Function),
            NirIndirectTarget { Function.Type: NirFunctionType type } => type.Outcomes,
            _ => NirOutcomes.None
        };
        if (!tail && !possible.HasFlag(NirOutcomes.Return))
            error("call-outcomes", "排除 Return 的合同必须使用 NirNoReturnCall");
        if (tail && possible.HasFlag(NirOutcomes.Return) && !owner.Outcomes.HasFlag(NirOutcomes.Return))
            error("callee-outcomes", "尾调用可能正常返回，但调用者合同排除 Return");
        if ((possible & (NirOutcomes.Fault | NirOutcomes.Terminate | NirOutcomes.Diverge) & ~owner.Outcomes) != 0)
            error("callee-outcomes", "调用行为超出调用者声明的结果合同");
    }
    private static void CheckCall(NirCallTarget target, ImmutableArray<NirValue> arguments, IEnumerable<NirType> results,
        Dictionary<string, NirSignature> signatures, Action<string, string> error)
    {
        var signature = target switch
        {
            NirDirectTarget direct => signatures.GetValueOrDefault(direct.Function),
            NirIndirectTarget { Function.Type: NirFunctionType type } => type.Signature,
            _ => null
        };
        if (signature is null) { error("call-target", "调用目标没有已声明的逻辑签名"); return; }
        if (arguments.IsDefault || !NirInspection.TypesEqual(arguments.Select(v => v.Type), signature.Parameters) || !NirInspection.TypesEqual(results, signature.Results))
            error("call-signature", "调用参数或结果与逻辑签名不一致");
    }
    private static void CheckOperation(NirOperation operation, Dictionary<string, NirSignature> signatures, Action<string, string> error)
    {
        static int Width(NirType type) => type switch { NirBitsType x => x.Width, NirAddressType x => x.Width, _ => 0 };
        switch (operation)
        {
            case NirConstant constant:
                var width = Width(constant.Result.Type);
                if (width is < 1 or > 4096 || constant.Bits < 0 || constant.Bits > BitVectorMath.Mask(width)) error("constant", "常量类型或位模式超出声明范围");
                break;
            case NirFunctionConstant constant:
                if (constant.Result.Type is not NirFunctionType type || !signatures.TryGetValue(constant.Function, out var signature) || !NirInspection.SignatureEquals(type.Signature, signature))
                    error("function-constant", "函数值必须绑定匹配的逻辑签名");
                break;
            case NirPure pure: CheckPure(pure, error); break;
            case NirLoad load:
                if (load.Address.Type is not NirAddressType || load.Result.Type is not NirBitsType bits || bits.Width % 8 != 0 || !Enum.IsDefined(load.Order))
                    error("load", "读取要求显式地址、完整字节宽度和明确字节顺序");
                break;
            case NirStore store:
                if (store.Address.Type is not NirAddressType || store.Value.Type is not NirBitsType bits2 || bits2.Width % 8 != 0 || !Enum.IsDefined(store.Order))
                    error("store", "写入要求显式地址、完整字节宽度和明确字节顺序");
                break;
            case NirLocalAlloc alloc:
                if (alloc.Result.Type is not NirAddressType || alloc.Size.Type is not NirBitsType || alloc.Alignment <= 0 || (alloc.Alignment & (alloc.Alignment - 1)) != 0)
                    error("local-alloc", "局部存储要求地址结果、整数尺寸和二次幂对齐");
                break;
            case NirCall call: CheckCall(call.Target, call.Arguments, call.Results.Select(v => v.Type), signatures, error); break;
            case NirChoose choose: if (choose.Result.Type is not NirBitsType) error("choose", "Choose 当前仅支持位串结果"); break;
        }
    }
    private static void CheckPure(NirPure pure, Action<string, string> error)
    {
        if (pure.Inputs.IsDefault || !Enum.IsDefined(pure.Code)) { error("pure", "纯操作码或输入集合无效"); return; }
        var inputs = pure.Inputs;
        var count = pure.Code switch
        {
            NirPureCode.Not or NirPureCode.Zext or NirPureCode.Sext or NirPureCode.Extract or NirPureCode.AddressToBits or NirPureCode.BitsToAddress => 1,
            NirPureCode.Select => 3, _ => 2
        };
        if (inputs.Length != count) { error("pure-arity", "纯操作输入数量错误"); return; }
        var rw = (pure.Result.Type as NirBitsType)?.Width ?? 0;
        var a = (inputs[0].Type as NirBitsType)?.Width ?? 0;
        var b = inputs.Length > 1 ? (inputs[1].Type as NirBitsType)?.Width ?? 0 : 0;
        var valid = pure.Code switch
        {
            NirPureCode.AddressAdd => pure.Result.Type is NirAddressType && NirInspection.TypeEquals(pure.Result.Type, inputs[0].Type) && inputs[1].Type is NirBitsType,
            NirPureCode.AddressToBits => inputs[0].Type is NirAddressType address && rw == address.Width,
            NirPureCode.BitsToAddress => pure.Result.Type is NirAddressType address && a == address.Width,
            NirPureCode.Eq => rw == 1 && inputs[0].Type is not NirEffectType && NirInspection.TypeEquals(inputs[0].Type, inputs[1].Type),
            NirPureCode.Ult or NirPureCode.Slt => rw == 1 && a > 0 && a == b,
            NirPureCode.Select => a == 1 && NirInspection.TypeEquals(pure.Result.Type, inputs[1].Type) && NirInspection.TypeEquals(pure.Result.Type, inputs[2].Type) && pure.Result.Type is not NirEffectType,
            NirPureCode.Zext or NirPureCode.Sext => a > 0 && rw > a,
            NirPureCode.Extract => rw > 0 && pure.BitOffset >= 0 && (long)pure.BitOffset + rw <= a,
            NirPureCode.Concat => a > 0 && b > 0 && rw == a + b,
            NirPureCode.Shl or NirPureCode.Shr or NirPureCode.Sar => a > 0 && b > 0 && rw == a,
            NirPureCode.Not => a > 0 && rw == a,
            _ => a > 0 && rw == a && a == b
        };
        if (!valid || pure.Code != NirPureCode.Extract && pure.BitOffset != 0) error("pure-types", "纯操作类型、宽度或位段参数不匹配");
    }
}
