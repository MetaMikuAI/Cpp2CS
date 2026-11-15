using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.MethodCopies;

public sealed record BodyCorrespondence(Reason? Difference, int Matched)
{
    public bool Isomorphic => Difference is null;
}

/// <summary>从入口同步遍历托管图；只重命名块与局部，条件取反时交换两条边。</summary>
public static class ManagedBodyIsomorphism
{
    public static BodyCorrespondence Compare(ManagedBody left, ManagedBody right) => new Comparison(left, right).Run();

    private sealed class Comparison(ManagedBody left, ManagedBody right)
    {
        private readonly Dictionary<ulong, ManagedBlock> leftBlocks = left.Blocks.ToDictionary(b => b.Address);
        private readonly Dictionary<ulong, ManagedBlock> rightBlocks = right.Blocks.ToDictionary(b => b.Address);
        private readonly Dictionary<ulong, ulong> blocks = [];
        private readonly HashSet<ulong> rightMapped = [];
        private readonly Dictionary<LocalId, LocalId> locals = [];
        private readonly HashSet<LocalId> rightLocals = [];
        private readonly Queue<(ulong Left, ulong Right)> pending = [];
        private int matched;
        private string? difference;
        private bool Fail(string path, object? a, object? b)
        { difference ??= $"{path}：副本={a ?? "空"}；注册={b ?? "空"}"; return false; }
        private bool Block(ulong a, ulong b, string path)
        {
            if (blocks.TryGetValue(a, out var mapped)) return mapped == b || Fail(path, "块对应冲突", "已有对应");
            if (!leftBlocks.ContainsKey(a) || !rightBlocks.ContainsKey(b) || !rightMapped.Add(b)) return Fail(path, "块对应不唯一或缺失", "不能建立对应");
            blocks.Add(a, b); pending.Enqueue((a, b)); return true;
        }
        private bool Equal(object? a, object? b, string path)
        {
            if (a is null || b is null) return a is null && b is null || Fail(path, a, b);
            if (a is LocalId l && b is LocalId r)
            {
                if (locals.TryGetValue(l, out var mapped)) return mapped == r || Fail(path, l, r);
                if (!rightLocals.Add(r)) return Fail(path, l, r);
                locals.Add(l, r); return true;
            }
            if (a is TypeRef or MethodRef or FieldRef || a is string || a.GetType().IsPrimitive || a.GetType().IsEnum)
                return a.Equals(b) || Fail(path, a, b);
            if (a is ManagedHole or HoleValue or PendingAccess) return Fail(path, "未完整恢复", b);
            if (a is ManagedEdge ae && b is ManagedEdge be)
                return Equal(ae.Copies, be.Copies, path + ".赋值") && Block(ae.Target, be.Target, path + ".目标");
            if (a is ManagedBranch ab && b is ManagedBranch bb)
            {
                // 试探条件不得留下失败分支的局部对应。
                var saved = locals.ToArray(); int score = matched;
                if (Equal(ab.Condition, bb.Condition, path + ".条件"))
                    return Equal(ab.Taken, bb.Taken, path + ".真边") && Equal(ab.Fallthrough, bb.Fallthrough, path + ".假边");
                var first = difference;
                locals.Clear(); rightLocals.Clear(); foreach (var pair in saved) { locals.Add(pair.Key, pair.Value); rightLocals.Add(pair.Value); }
                matched = score; difference = null;
                if (Inverse(ab.Condition, bb.Condition, path + ".反条件"))
                    return Equal(ab.Taken, bb.Fallthrough, path + ".真边") && Equal(ab.Fallthrough, bb.Taken, path + ".假边");
                difference = first; return false;
            }
            if (a is IEnumerable aa && b is IEnumerable ba)
            {
                var av = aa.Cast<object?>().ToArray(); var bv = ba.Cast<object?>().ToArray();
                for (int i = 0; i < Math.Min(av.Length, bv.Length); i++) if (!Equal(av[i], bv[i], $"{path}[{i}]")) return false;
                return av.Length == bv.Length || Fail(path + ".项数", av.Length, bv.Length);
            }
            if (a is ITuple at && b is ITuple bt)
            {
                if (at.Length != bt.Length) return Fail(path + ".项数", at.Length, bt.Length);
                for (int i = 0; i < at.Length; i++) if (!Equal(at[i], bt[i], $"{path}[{i}]")) return false;
                return true;
            }
            if (a.GetType() != b.GetType()) return Fail(path, a.GetType().Name, b.GetType().Name);
            if (a.GetType().Assembly != typeof(ManagedBody).Assembly) return a.Equals(b) || Fail(path, a, b);
            // 新增托管词汇的属性默认参与比较；只忽略原生位置。
            foreach (var property in a.GetType().GetProperties(BindingFlags.Instance | BindingFlags.Public).OrderBy(p => p.MetadataToken))
            {
                if (property.Name == "Address" && a is ManagedStatement) continue;
                if (!Equal(property.GetValue(a), property.GetValue(b), path + "." + property.Name)) return false;
            }
            matched++; return true;
        }
        private bool Inverse(ManagedValue a, ManagedValue b, string path)
        {
            if (a is NegatedValue an) return Equal(an.Operand, b, path);
            if (b is NegatedValue bn) return Equal(a, bn.Operand, path);
            return a is ComparisonValue ac && b is ComparisonValue bc && Complement(ac.Condition) == bc.Condition
                && Equal(ac.Type, bc.Type, path + ".类型") && Equal(ac.Left, bc.Left, path + ".左") && Equal(ac.Right, bc.Right, path + ".右");
        }
        private bool Drain()
        {
            while (pending.TryDequeue(out var pair))
                if (!Equal(leftBlocks[pair.Left].Statements, rightBlocks[pair.Right].Statements, $"块[{blocks.Keys.ToList().IndexOf(pair.Left)}].语句")) return false;
            return true;
        }
        public BodyCorrespondence Run()
        {
            if (left.Blocks.Count == 0 || right.Blocks.Count == 0) Fail("入口", left.Blocks.Count, right.Blocks.Count);
            else if (Equal(left.Method, right.Method, "方法") && Block(left.Blocks[0].Address, right.Blocks[0].Address, "入口") && Drain())
            {
                if (left.Regions.Count != right.Regions.Count) Fail("异常子句数", left.Regions.Count, right.Regions.Count);
                else
                {
                    for (int i = 0; i < left.Regions.Count && difference is null; i++)
                    {
                        var a = left.Regions[i]; var b = right.Regions[i]; string path = $"异常子句[{i}]";
                        if (!Equal(a.Kind, b.Kind, path + ".种类") || !Equal(a.CatchType, b.CatchType, path + ".类型")
                            || !Equal(a.Exception, b.Exception, path + ".异常局部") || !Block(a.HandlerEntry, b.HandlerEntry, path + ".入口") || !Drain()) break;
                        if (!Region(a.Try, b.Try, path + ".保护块") || !Region(a.Handler, b.Handler, path + ".处理块")) break;
                    }
                    if (difference is null && (blocks.Count != left.Blocks.Count || rightMapped.Count != right.Blocks.Count))
                        Fail("块覆盖", blocks.Count + "/" + left.Blocks.Count, rightMapped.Count + "/" + right.Blocks.Count);
                }
            }
            return new(difference is null ? null : new("method-copy.body", "托管体不同构；第一处不同：" + difference), matched);
        }
        private bool Region(IReadOnlyList<ulong> a, IReadOnlyList<ulong> b, string path) =>
            a.Count == b.Count && a.All(blocks.ContainsKey) && a.Select(x => blocks[x]).ToHashSet().SetEquals(b) || Fail(path, "区域块集合", "对应不一致");
    }
    private static ComparisonKind? Complement(ComparisonKind kind) => kind switch
    {
        ComparisonKind.Equal => ComparisonKind.NotEqual, ComparisonKind.NotEqual => ComparisonKind.Equal,
        ComparisonKind.SignedLess => ComparisonKind.SignedGreaterOrEqual, ComparisonKind.SignedGreaterOrEqual => ComparisonKind.SignedLess,
        ComparisonKind.SignedLessOrEqual => ComparisonKind.SignedGreater, ComparisonKind.SignedGreater => ComparisonKind.SignedLessOrEqual,
        ComparisonKind.UnsignedLess => ComparisonKind.UnsignedGreaterOrEqual, ComparisonKind.UnsignedGreaterOrEqual => ComparisonKind.UnsignedLess,
        ComparisonKind.UnsignedLessOrEqual => ComparisonKind.UnsignedGreater, ComparisonKind.UnsignedGreater => ComparisonKind.UnsignedLessOrEqual,
        ComparisonKind.FloatEqual => ComparisonKind.FloatUnorderedOrNotEqual, ComparisonKind.FloatUnorderedOrNotEqual => ComparisonKind.FloatEqual,
        ComparisonKind.FloatNotEqual => ComparisonKind.FloatUnorderedOrEqual, ComparisonKind.FloatUnorderedOrEqual => ComparisonKind.FloatNotEqual,
        ComparisonKind.FloatLess => ComparisonKind.FloatUnorderedOrGreaterOrEqual, ComparisonKind.FloatUnorderedOrGreaterOrEqual => ComparisonKind.FloatLess,
        ComparisonKind.FloatLessOrEqual => ComparisonKind.FloatUnorderedOrGreater, ComparisonKind.FloatUnorderedOrGreater => ComparisonKind.FloatLessOrEqual,
        ComparisonKind.FloatGreater => ComparisonKind.FloatUnorderedOrLessOrEqual, ComparisonKind.FloatUnorderedOrLessOrEqual => ComparisonKind.FloatGreater,
        ComparisonKind.FloatGreaterOrEqual => ComparisonKind.FloatUnorderedOrLess, ComparisonKind.FloatUnorderedOrLess => ComparisonKind.FloatGreaterOrEqual,
        ComparisonKind.FloatUnordered => ComparisonKind.FloatOrdered, ComparisonKind.FloatOrdered => ComparisonKind.FloatUnordered,
        _ => null,
    };
}
