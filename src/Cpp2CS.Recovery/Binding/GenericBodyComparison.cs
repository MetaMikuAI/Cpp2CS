using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Binding;

/// <summary>逐项核对两个开放体，不做语义等价改写；原生地址与 T 的实例位宽不属于开放体。</summary>
public static class GenericBodyComparison
{
    public static Reason? Compare(ManagedBody reference, ManagedBody value)
    {
        var leftLocals = new Dictionary<LocalId, int>();
        var rightLocals = new Dictionary<LocalId, int>();
        var leftBlocks = reference.Blocks.Select((b, i) => (b.Address, i)).ToDictionary(p => p.Address, p => p.i);
        var rightBlocks = value.Blocks.Select((b, i) => (b.Address, i)).ToDictionary(p => p.Address, p => p.i);
        static int Local(Dictionary<LocalId, int> ids, LocalId id)
        {
            if (!ids.TryGetValue(id, out int normalized)) ids.Add(id, normalized = ids.Count);
            return normalized;
        }
        string? Difference(object? left, object? right, string path)
        {
            string At(object? a, object? b) => $"{path}：引用={a ?? "空"}；值={b ?? "空"}";
            if (left is null || right is null) return left is null && right is null ? null : At(left, right);
            if (left is LocalId l && right is LocalId r) return Local(leftLocals, l) == Local(rightLocals, r) ? null : At(left, right);
            if (left is TypeRef or MethodRef or FieldRef) return left.Equals(right) ? null : At(left, right);
            if (left is string || left.GetType().IsPrimitive || left.GetType().IsEnum) return left.Equals(right) ? null : At(left, right);
            if (left is IEnumerable ls && right is IEnumerable rs)
            {
                var a = ls.Cast<object?>().ToArray(); var b = rs.Cast<object?>().ToArray();
                for (int i = 0; i < Math.Min(a.Length, b.Length); i++)
                    if (Difference(a[i], b[i], $"{path}[{i}]") is { } item) return item;
                return a.Length == b.Length ? null : $"{path}[{Math.Min(a.Length, b.Length)}]：引用有 {a.Length} 项；值有 {b.Length} 项";
            }
            if (left.GetType() != right.GetType()) return At(left.GetType().Name, right.GetType().Name);
            if (left is ITuple lt && right is ITuple rt)
            {
                if (lt.Length != rt.Length) return At(lt.Length, rt.Length);
                for (int i = 0; i < lt.Length; i++)
                    if (Difference(lt[i], rt[i], $"{path}[{i}]") is { } item) return item;
                return null;
            }
            if (left.GetType().Assembly != typeof(ManagedBody).Assembly) return left.Equals(right) ? null : At(left, right);
            // 托管记录的全部公开属性均参与；新增词汇不会因比较器漏列而被忽略。
            foreach (var property in left.GetType().GetProperties(BindingFlags.Instance | BindingFlags.Public).OrderBy(p => p.MetadataToken))
            {
                if (property.Name == nameof(ManagedBody.WitnessCoverage) && left is ManagedBody
                    || property.Name == "Address" && left is ManagedBlock or ManagedStatement
                    || property.Name == nameof(ManagedValue.Width) && left is ManagedValue { Type: GenericParameterRef }) continue;
                object? a = property.GetValue(left), b = property.GetValue(right);
                if (left is ManagedEdge && property.Name == nameof(ManagedEdge.Target)
                    || left is ManagedRegion && property.Name == nameof(ManagedRegion.HandlerEntry))
                { a = leftBlocks[(ulong)a!]; b = rightBlocks[(ulong)b!]; }
                if (left is ManagedRegion && property.Name is nameof(ManagedRegion.Try) or nameof(ManagedRegion.Handler))
                { a = ((IEnumerable<ulong>)a!).Select(x => leftBlocks[x]).ToArray(); b = ((IEnumerable<ulong>)b!).Select(x => rightBlocks[x]).ToArray(); }
                if (Difference(a, b, path + "." + property.Name) is { } item) return item;
            }
            return null;
        }
        return Difference(reference, value, "方法体") is { } difference
            ? new("lowering.Generic.Specialized", "两个实例恢复出的开放体不同；第一处不同：" + difference) : null;
    }
}
