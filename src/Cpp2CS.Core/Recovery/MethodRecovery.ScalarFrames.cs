using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>结构体地址已绑定到有界区域后，恢复地址不逃逸的整数计数槽和已定型的引用槽。</summary>
        [Analysis("整数帧槽", 35, After = ["帧区域"])]
        private void PrepareScalarFrames()
        {
            InferTypes();
            var accesses = new List<(long Offset, int Width, Expr? Written)>();
            var escapes = new List<long>();
            void Visit(Expr expression)
            {
                if (expression is Load load && FrameOffset(load.Address) is { } offset)
                    accesses.Add((offset, load.Width, null));
                else if (FrameOffset(expression) is { } escaped) escapes.Add(escaped);
                else foreach (var child in ExprMap.Children(expression)) Visit(child);
            }
            foreach (var statement in blocks.SelectMany(b => b.Statements))
            {
                if (dropped.Contains(statement) || statement is Call call && (stackEnums.ContainsKey(call) || IsWriteBarrier(call))) continue;
                if (statement is Store store && FrameOffset(store.Target) is { } offset)
                {
                    accesses.Add((offset, store.Value.Width, store.Value));
                    Visit(store.Value);
                }
                else foreach (var operand in ExprMap.Operands(statement)) Visit(operand);
            }
            // 常量本身没有类型；至少一次整数计算或已定型整数写入提供证据。
            (bool Allowed, bool Integer) Written(Expr expression, HashSet<Variable> seen) => expression switch
            {
                Const => (true, false),
                Binary { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor } => (true, true),
                Ir.Convert { Kind: ConvKind.Truncate or ConvKind.ZeroExtend or ConvKind.SignExtend } convert => Written(convert.Operand, seen),
                Use use when known.TryGetValue(use.Variable, out var type) && types.Kind(type) is TypeKind.Int or TypeKind.Bool => (true, true),
                Use use when seen.Add(use.Variable) && values.TryGetValue(use.Variable, out var value) => Written(value, seen),
                _ => (false, false),
            };
            var scalar = new Dictionary<long, FrameRegion>();
            bool? registerCalls = null;
            bool NoStackArguments(Call call)
            {
                if (call.Op?.Kind is OpKind.InitClass or OpKind.RunClassConstructor or OpKind.InitMethodRgctx
                    or OpKind.NewObject or OpKind.NewArray or OpKind.Box or OpKind.Unbox or OpKind.IsInst or OpKind.IsAssignableFrom
                    or OpKind.TypeCheck or OpKind.ThrowIf or OpKind.NullCheck or OpKind.BoundsCheck or OpKind.Throw or OpKind.ThrowNew
                    or OpKind.NewException or OpKind.Rethrow or OpKind.WriteBarrier or OpKind.MemoryBarrier or OpKind.CompareExchangeReference or OpKind.InterfaceInvokeData
                    or OpKind.ResolveGenericVirtual or OpKind.BeginCatch or OpKind.EndCatch or OpKind.ResumeUnwind or OpKind.Terminate or OpKind.ThrowManaged) return true;
                return Resolve(call) is { } target && owner.abi.Classify(target, out _) is { MethodInfo: not null } signature
                    && signature.Arguments.All(a => a.Passing != Facts.Passing.Stack);
            }
            foreach (var group in accesses.GroupBy(a => a.Offset))
            {
                var offset = group.Key;
                if (offset >= 0 || group.Select(a => a.Width).Distinct().ToArray() is not [var width and (32 or 64)]
                    || escapes.Any(at => at <= offset)
                    || frameRegions.Any(r => offset < r.Offset + r.Size && r.Offset < offset + width / 8)
                    || accesses.Any(a => a.Offset != offset && offset < a.Offset + a.Width / 8 && a.Offset < offset + width / 8)) continue;
                if (!group.Any(a => a.Written is null))
                {
                    // 无读取的常量备份只有在所有调用都不从调用者栈取参数时才可删去。
                    if (group.All(a => a.Written is Const) && (registerCalls ??= blocks.SelectMany(b => b.Statements).OfType<Call>().All(NoStackArguments)))
                        dropped.UnionWith(blocks.SelectMany(b => b.Statements).OfType<Store>().Where(s => FrameOffset(s.Target) == offset));
                    continue;
                }
                if (width == 64)
                {
                    TypeRef? Reference(Expr value) => value is Use use && known.TryGetValue(use.Variable, out var type) && types.Kind(type) == TypeKind.Reference ? type : null;
                    var writes = group.Where(a => a.Written is not null).Select(a => a.Written!).ToArray();
                    var candidates = writes.Select(Reference).OfType<TypeRef>().Distinct().ToArray();
                    if (candidates.FirstOrDefault(t => candidates.All(other => types.IsAssignable(other, t))) is { } reference
                        && writes.All(v => v is Const { Value: 0 } || Reference(v) is not null))
                        scalar[offset] = new(offset, reference, 8, StructLocal(reference, 64));
                    continue;
                }
                var written = group.Where(a => a.Written is not null).Select(a => Written(a.Written!, [])).ToArray();
                if (!written.Any(w => w.Integer) || written.Any(w => !w.Allowed)) continue;
                scalar[offset] = new(offset, types.Int32, 4, StructLocal(types.Int32, 32));
            }
            if (scalar.Count == 0) return;
            frameRegions.AddRange(scalar.Values);
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var old = block.Statements[i];
                    if (dropped.Contains(old) || old is Call call && stackEnums.ContainsKey(call)) continue;
                    var mapped = ExprMap.MapOperands(old, e => ExprMap.Map(e, part =>
                        FrameOffset(part) is { } offset && scalar.TryGetValue(offset, out var region) ? new TypedFrame(region) : null));
                    if (ReferenceEquals(old, mapped)) continue;
                    block.Statements[i] = mapped;
                    ledger.Replace(old, mapped);
                }
            definitions = IndexDefinitions();
        }
    }
}
