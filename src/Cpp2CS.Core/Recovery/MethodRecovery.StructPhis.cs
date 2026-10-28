using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>一组按 ABI 片汇合的寄存器 φ：整体是一个结构体局部变量，每条入边整体赋值一次。</summary>
        private sealed record StructPhi(LocalValue Local, TypeRef Type, Block Block, Func<int, ManagedValue> Incoming);
        private readonly Dictionary<Variable, (StructPhi Group, AbiPiece Piece)> structPhiMembers = new();
        private readonly List<StructPhi> structPhis = [];

        /// <summary>
        /// 寄存器返回的结构体从多条路径汇合（例如 AsyncUniTaskMethodBuilder.get_Task 返回接口调用的结果、FromException 的结果或 UniTask.CompletedTask）：
        /// 返回值各片的 φ 在每条入边上都来自同一个结构体值（同一次调用的结构体结果，或同一个结构体位置的逐片读取）时，
        /// 这组 φ 是一个结构体局部变量；φ 只被返回使用。逐片读取的定义并入入边上的整体读取。
        /// </summary>
        [Analysis("结构体汇合", 95, After = ["类型"])]
        private RecoveryFailure? StructPhis()
        {
            if (owner.abi.Classify(method, out _)?.Return is not { } returned || !RegisterStruct(returned) || returned.Pieces.Length < 2) return null;
            var type = returned.Type;
            var size = types.Size(type);
            var uses = blocks.SelectMany(b => b.Statements).Where(s => s is not Phi)
                .SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => (u.Variable, Statement: s))).ToLookup(p => p.Variable, p => p.Statement);
            var phiSources = blocks.SelectMany(b => b.Statements).OfType<Phi>().SelectMany(p => p.Sources.Select(s => (s, p))).ToLookup(p => p.s, p => p.p);
            foreach (var block in blocks)
            {
                var members = returned.Pieces.Select(piece => block.Statements.OfType<Phi>().FirstOrDefault(p => p.Target.Storage == piece.Register)).ToArray();
                if (members.Any(m => m is null) || members.Any(m => phiSources[m!.Target].Any() || uses[m.Target].Any(s => s is not Return))) continue;
                var count = members[0]!.Sources.Length;
                var origins = new List<Func<ManagedValue>>();
                var absorbed = new List<Variable>();
                for (var k = 0; k < count && origins.Count == k; k++)
                {
                    var sources = members.Select(m => m!.Sources[k]).ToArray();
                    // 同一次调用的结构体结果：各片依次是该调用的结果寄存器
                    if (sources.Select(s => results.TryGetValue(s, out var r) ? r.Call : null).Distinct().ToArray() is [{ } call]
                        && sources.Zip(returned.Pieces).All(p => results[p.First].Call.Results[results[p.First].Index] == p.Second.Register)
                        && Resolve(call) is { } callee && owner.abi.Classify(callee, out _)?.Return is { } callReturn && RegisterStruct(callReturn) && callReturn.Type.Equals(type))
                    {
                        origins.Add(() => CallStructLocal(call, type));
                        continue;
                    }
                    // 同一个结构体位置的逐片读取：第 i 片读自位置起点 + 片偏移，读取只被这组 φ 使用
                    // 片也可以是零扩展的窄读取，只要它覆盖该片的全部叶子（其余是填充，如 ValueTuple<bool, Nullable<float>> 的末 4 字节）。
                    Load? PieceLoad(Variable v, AbiPiece piece) => values.TryGetValue(v, out var e) && CopiedLoad(e) is { } l
                        && (l.Width == piece.Width || e is not Load && StructPaths(type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)
                            && p.Offset >= piece.Offset && p.Offset < piece.Offset + piece.Width / 8).All(p => p.Offset + types.Size(p.Type) <= piece.Offset + l.Width / 8)) ? l : null;
                    if (sources.Zip(returned.Pieces).All(p => PieceLoad(p.First, p.Second) is not null) && PieceLoad(sources[0], returned.Pieces[0]) is { } first
                        && sources.Zip(returned.Pieces).All(p => PieceLoad(p.First, p.Second) is { } l
                            && Split(l.Address).Offset - Split(first.Address).Offset == p.Second.Offset && Split(l.Address).Base == Split(first.Address).Base)
                        && sources.All(s => !uses[s].Any() && phiSources[s].All(p => members.Contains(p))))
                    {
                        if (!CopyRanges(first.Address, size * 8).TryGet(out var ranges, out var failure)) return failure;
                        if (ranges.FirstOrDefault(r => r.Offset == 0 && r.Type.Equals(type)) is not { } range) continue;
                        origins.Add(() => new IndirectValue(range.Root, type));
                        absorbed.AddRange(sources);
                        continue;
                    }
                }
                if (origins.Count != count) continue;
                var group = new StructPhi(StructLocal(type, 0), type, block, k => origins[k]());
                structPhis.Add(group);
                for (var i = 0; i < members.Length; i++) structPhiMembers[members[i]!.Target] = (group, returned.Pieces[i]);
                foreach (var variable in absorbed)
                    foreach (var definition in blocks.SelectMany(b => b.Statements).OfType<Define>().Where(d => d.Target == variable)) dropped.Add(definition);
            }
            return null;
        }

        /// <summary>
        /// 整体写入结构体位置的整数 φ（内联的 setter：this.f = c ? new Nullable&lt;E&gt;(x) : default）：φ 只被同宽的整体写入使用，
        /// 写入位置是一个大小等于该宽度的结构体，每条入边的来源是同类型结构体位置的整体读取（只被这个 φ 使用）或常量 0（default）时，
        /// φ 是一个该类型的结构体局部变量；读取并入入边上的整体赋值。
        /// </summary>
        [Analysis("结构体写入汇合", 96, After = ["结构体汇合"])]
        private RecoveryFailure? StoredStructPhis()
        {
            var statements = blocks.SelectMany(b => b.Statements).ToArray();
            var uses = statements.Where(s => s is not Phi)
                .SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => (u.Variable, Statement: s))).ToLookup(p => p.Variable, p => p.Statement);
            var phiSources = statements.OfType<Phi>().SelectMany(p => p.Sources.Select(s => (s, p))).ToLookup(p => p.s, p => p.p);
            foreach (var block in blocks)
                foreach (var phi in block.Statements.OfType<Phi>())
                {
                    if (phi.Target.Storage.Bank != Bank.Gpr || structPhiMembers.ContainsKey(phi.Target) || phiSources[phi.Target].Any()) continue;
                    TypeRef? type = null;
                    var width = 0;
                    if (uses[phi.Target].ToArray() is [Store { Value: Use { Width: 64 or 32 } use } store] && use.Variable == phi.Target)
                    {
                        width = use.Width;
                        if (!CopyRanges(store.Target, width).TryGet(out var ranges, out var failure)) return failure;
                        type = ranges.FirstOrDefault(r => r.Offset == 0 && types.Kind(r.Type) == TypeKind.Struct && types.Size(r.Type) * 8 == width)?.Type;
                    }
                    else if (uses[phi.Target].ToArray() is [Return { Value: Use { Width: 64 or 32 } returned }]
                        && returned.Variable == phi.Target && types.Kind(returnType) == TypeKind.Struct && types.Size(returnType) * 8 == returned.Width)
                    {
                        width = returned.Width;
                        type = returnType;
                    }
                    if (type is null) continue;
                    var origins = new List<Func<ManagedValue>>();
                    var absorbed = new List<Variable>();
                    foreach (var source in phi.Sources)
                    {
                        if (!values.TryGetValue(source, out var value)) break;
                        if (value is Const { Value: 0 })
                        {
                            origins.Add(() => new ComposedValue(type, []));
                            continue;
                        }
                        if (value is Load load && load.Width == width && !uses[source].Any() && phiSources[source].All(p => ReferenceEquals(p, phi)))
                        {
                            if (!CopyRanges(load.Address, width).TryGet(out var ranges, out var failure)) return failure;
                            if (ranges.FirstOrDefault(r => r.Offset == 0 && r.Type.Equals(type)) is not { } range) break;
                            origins.Add(() => new IndirectValue(range.Root, type));
                            absorbed.Add(source);
                            continue;
                        }
                        break;
                    }
                    if (origins.Count != phi.Sources.Length || absorbed.Count == 0) continue;
                    var group = new StructPhi(StructLocal(type, 0), type, block, k => origins[k]());
                    structPhis.Add(group);
                    structPhiMembers[phi.Target] = (group, new AbiPiece(phi.Target.Storage, width, 0));
                    foreach (var variable in absorbed)
                        foreach (var definition in statements.OfType<Define>().Where(d => d.Target == variable)) dropped.Add(definition);
                }
            return null;
        }

        /// <summary>结构体 φ 的一片（返回时按 ABI 片读取）。</summary>
        private RecoveryResult<ManagedValue?> StructPhiPiece(Variable variable, int width)
        {
            if (!structPhiMembers.TryGetValue(variable, out var member)) return (ManagedValue?)null;
            var fragment = StructPiece(member.Group.Local, member.Piece);
            if (width == fragment.Width) return fragment;
            return width < fragment.Width ? Slice(fragment, 0, width).Map<ManagedValue?>(value => value)
                : fragment is Fragment f ? ResizeFragment(f, width).Map<ManagedValue?>(value => value)
                : new Fragment([new Part(0, fragment)], types.UInt64, width);
        }
    }
}
