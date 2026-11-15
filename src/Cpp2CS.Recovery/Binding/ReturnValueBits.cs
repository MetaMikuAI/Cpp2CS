using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Binding;

/// <summary>声明返回值在结果槽中的扩展；不描述其他结果槽或调用保持的输入。</summary>
public sealed record ReturnValueBits(int ValueWidth, bool Signed, int DefinedWidth)
{
    public static Outcome<ReturnValueBits> Prove(NativeFunction function, SignatureBinding signature, TypeRef type,
        Func<Term, Outcome<ReturnValueBits>?>? calls = null)
    {
        Outcome<ReturnValueBits> No(string code, string message, Reason? cause = null) =>
            Outcome<ReturnValueBits>.Failure(new("binding.return-bits." + code, message, cause));
        var scalar = ManagedTypes.Underlying(type);
        if (ManagedTypes.PrimitiveName(scalar) is not ("Boolean" or "Byte" or "SByte" or "Char" or "Int16" or "UInt16")
            || signature.Signature.ReturnType is not Cpp2CS.Native.Abi.CInteger { Bits: 8 or 16 } integer
            || signature.Slots.Return.Pieces is not [{ ValueOffset: 0, SlotOffset: 0 } piece]
            || piece.Length * 8 != integer.Bits)
            return No("type", "声明返回值不是单槽的小整数。");
        var state = new StateQueries();
        var context = state.CreateContext(function);
        var incoming = new IncomingValuesQuery(state);
        var views = calls is null ? null : new ExtensionViewQuery(calls);
        bool signed = ManagedTypes.IsSigned(scalar);
        int returns = 0;
        foreach (var block in function.Blocks)
        {
            if (block.End is not Return returned) continue;
            returns++;
            var slot = returned.Results.SingleOrDefault(r => r.Slot == piece.Slot)?.Value;
            if (slot is null || slot.Width < 32) return No("slot", "返回点缺少完整的 32 位结果槽。");
            var resolved = context.Get(state.Resolve, slot);
            if (!resolved.IsSuccess) return No("resolve", "返回点的结果槽无法解析。", resolved.Why);
            var t = function.Terms;
            var actual = t.Slice(resolved.Value, 0, 32);
            var expected = t.Apply(new CoreOperator(signed ? CoreOperation.SignExtend : CoreOperation.ZeroExtend),
                32, t.Slice(actual, 0, integer.Bits));
            // 低位来自同一个定义；只比较高位，使位运算可沿已有切片规范化求值。
            var equal = t.Apply(new CoreOperator(CoreOperation.Equal), 1, t.Slice(actual, integer.Bits, 32 - integer.Bits),
                t.Slice(expected, integer.Bits, 32 - integer.Bits));
            if (equal.ConstantValue == 1) continue;
            // 汇合点的逐边取值由内核提供；循环或无法投影的值不补私有路径证明。
            var edges = context.Get(incoming, new(equal, block.Identity));
            if (!edges.IsSuccess) return No("merge", "返回点的入边值无法解析。", edges.Why);
            foreach (var condition in edges.Value.IsEmpty ? new[] { equal } : edges.Value.Select(e => e.Value).ToArray())
            {
                var view = views is null ? Outcome<ExtensionView>.Success(new(condition, null)) : context.Get(views, condition);
                if (!view.IsSuccess) return No("view", "返回点的扩展视图无法建立。", view.Why);
                if (view.Value.Value.ConstantValue != 1)
                    return No("return", "至少一个返回点未证明声明返回值扩展到 32 位。", view.Value.Missing);
            }
        }
        return returns == 0 ? No("no-return", "被调方没有正常返回点。")
            : Outcome<ReturnValueBits>.Success(new(integer.Bits, signed, 32));
    }

    private sealed record ExtensionView(Term Value, Reason? Missing);
    /// <summary>只把已证明的调用结果低 32 位换成扩展视图，其他位与原始身份保持不变。</summary>
    private sealed class ExtensionViewQuery(Func<Term, Outcome<ReturnValueBits>?> calls) : Query<Term, ExtensionView>
    {
        public override Outcome<ExtensionView> Compute(QueryContext c, Term key)
        {
            Reason? missing = null;
            if (calls(key) is { } dependency)
            {
                if (dependency.IsSuccess && dependency.Value is { ValueWidth: 8 or 16, DefinedWidth: 32 } bits && key.Width >= 32)
                {
                    var t = key.Table;
                    var low = t.Slice(key, 0, bits.ValueWidth);
                    var extended = t.Apply(new CoreOperator(bits.Signed ? CoreOperation.SignExtend : CoreOperation.ZeroExtend), 32, low);
                    return Outcome<ExtensionView>.Success(new(key.Width == 32 ? extended
                        : t.Concat(extended, t.Slice(key, 32, key.Width - 32)), null));
                }
                missing = dependency.Why;
            }
            var mapped = new Dictionary<Term, Term>();
            foreach (var operand in key.Operands)
            {
                var result = c.Get(this, operand);
                if (!result.IsSuccess) return result;
                mapped[operand] = result.Value.Value;
                missing ??= result.Value.Missing;
            }
            return Outcome<ExtensionView>.Success(new(SnapshotRewrite.Rebuild(key, operand => mapped[operand]), missing));
        }
    }
}

/// <summary>同一次运行共用的被调方摘要；失败与成功都由装配方缓存。</summary>
public interface IReturnValueBitsSource
{
    Outcome<ReturnValueBits> Get(ulong entry, MethodRef method);
}
