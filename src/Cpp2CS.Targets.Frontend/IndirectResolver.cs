using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using static Cpp2CS.Native.Terms.CoreOperation;

namespace Cpp2CS.Targets.Frontend;

/// <summary>在项上证明只读表索引与目标；不使用指令编码或符号名称。</summary>
public static class IndirectResolver
{
    public static IndirectResolution Resolve(Term target, IIndirectContext context)
        => new Resolution(context).Run(target);

    private sealed class Resolution
    {
        private readonly IIndirectContext context;
        private readonly TermRewrite uniqueExpand;
        private readonly TermRewrite expand;
        internal Resolution(IIndirectContext context)
        {
            this.context = context;
            uniqueExpand = new(context.Terms, context.InUniquePredecessor, true);
            expand = new(context.Terms, Expand, true);
        }
        private TermTable Terms => context.Terms;
        private Term? Expand(Term term)
        {
            if (context.InUniquePredecessor(term) is { } predecessor) return predecessor;
            return RelocatedPointer(term) is PointerTarget.Internal pointer
                ? Terms.Apply(new CoreOperator(Add), term.Width, Terms.Atom(new RootAtom(AddressRoot.Image), term.Width), Terms.Constant(pointer.Offset, term.Width))
                : null;
        }
        // 只读常量槽的重定位是链接事实；先解开 GOT，再判断运行期读取的根权限。
        private PointerTarget? RelocatedPointer(Term term)
        {
            if (context.Image is not { } image || context.ReadOf(term) is not { } read || read.Acquire
                || read.Width != image.PointerWidth * 8) return null;
            var address = uniqueExpand.Map(read.Address);
            if (!Walk(address).Any(ImageRoot)) return null;
            var offset = new TermRewrite(Terms, t => ImageRoot(t) ? Terms.Constant(0, t.Width) : null).Map(address);
            if (offset.ConstantValue is not { } constant || constant > ulong.MaxValue) return null;
            ulong slot = (ulong)constant, bytes = (ulong)image.PointerWidth;
            return ReadOnly(image, slot, bytes) && image.HasRelocation(slot, bytes) ? image.ReadPointer(slot) : null;
        }
        private static IndirectUnknown Hole(string code, string message) => new(new("indirect." + code, message));
        private static bool Is(Term t, CoreOperation op) => t.Operator is CoreOperator c && c.Operation == op;
        private static bool ImageRoot(Term t) => t.Identity is RootAtom { Kind: AddressRoot.Image };
        private static IEnumerable<Term> Walk(Term root)
        {
            var seen = new HashSet<Term>(); var pending = new Stack<Term>(); pending.Push(root);
            while (pending.TryPop(out var t))
            {
                if (!seen.Add(t)) continue;
                yield return t;
                foreach (var operand in t.Operands) pending.Push(operand);
            }
        }
        internal IndirectResolution Run(Term original)
        {
            var target = expand.Map(original);
            var reads = new Dictionary<Term, MemoryRead>();
            // 目标的全部来源：运算数、合流入口在各前驱出口的项、读取的地址。每个项只访问一次，循环由 seen 终止。
            var operandUsers = new Dictionary<Term, List<Term>>();
            var mergeUsers = new Dictionary<Term, List<Term>>();
            var pending = new Stack<Term>(); var seen = new HashSet<Term>(); pending.Push(target);
            void Link(Dictionary<Term, List<Term>> users, Term source, Term user)
            {
                if (!users.TryGetValue(source, out var list)) users.Add(source, list = []);
                list.Add(user); pending.Push(source);
            }
            while (pending.TryPop(out var term))
            {
                if (!seen.Add(term)) continue;
                foreach (var operand in term.Operands) Link(operandUsers, operand, term);
                foreach (var source in context.InPredecessors(term)) Link(mergeUsers, expand.Map(source), term);
                if (context.ReadOf(term) is not { } read) continue;
                var address = expand.Map(read.Address);
                reads[term] = read with { Address = address };
                pending.Push(address);
            }
            // 只经运算数可见的映像根；读取不传递。
            HashSet<Term> Reaching()
            {
                var result = new HashSet<Term>(); var work = new Stack<Term>(seen.Where(ImageRoot));
                while (work.TryPop(out var t))
                {
                    if (!result.Add(t)) continue;
                    if (operandUsers.TryGetValue(t, out var users)) foreach (var user in users) work.Push(user);
                }
                return result;
            }
            var visible = Reaching();
            // 在已有依赖图上传播根的权限。已物化地址的常量偏移决定所属段；读取不传递根。
            var readOnly = new HashSet<Term>(); var mergedReadOnly = new HashSet<Term>();
            var roots = new Stack<(Term Term, bool Merged)>(visible.Where(t => !WritableBase(t)).Select(t => (t, false)));
            while (roots.TryPop(out var item))
            {
                if (!(item.Merged ? mergedReadOnly : readOnly).Add(item.Term)) continue;
                if (operandUsers.TryGetValue(item.Term, out var users))
                    foreach (var user in users)
                        if (item.Merged || !visible.Contains(item.Term) || !visible.Contains(user)) roots.Push((user, item.Merged));
                if (mergeUsers.TryGetValue(item.Term, out users)) foreach (var user in users) roots.Push((user, true));
            }
            if (reads.Values.Any(r => mergedReadOnly.Contains(r.Address)))
                return Hole("merge", "读取地址经合流依赖映像地址，不能排除只读表读取。");
            var imageReads = reads.Values.Where(r => readOnly.Contains(r.Address)).ToArray();
            if (imageReads.Length == 0) return new IndirectTailCall(target);
            if (context.Image is not { } image || context.Range is not { } range)
                return Hole("image", "缺少映像或函数范围。");
            if (imageReads.Length > 2)
                return Hole("shape", "目标依赖的映像读取不能表达为一次表读取或两级表读取。");
            var tables = new List<Table>();
            foreach (var read in imageReads)
            {
                var described = Describe(read, image);
                if (described.Failure is { } failure) return failure;
                tables.Add(described.Table!);
            }
            var finals = tables.Where(t => target == t.Read.Result || RelativeShape(target, t.Read.Result)).ToArray();
            if (finals.Length != 1)
                return Hole("shape", "目标不是表项地址或映像基址加扩展后的相对表项。");
            var table = finals[0];
            var first = tables.Count == 1 ? table : tables.Single(t => t != table);
            if (first != table && (!Walk(table.Selector).Contains(first.Read.Result) || Walk(first.Selector).Contains(table.Read.Result)))
                return Hole("shape", "两次表读取没有形成单一下标的依赖链。");
            bool absolute = target == table.Read.Result;
            foreach (var t in tables)
                if ((!absolute || t != table) && image.HasRelocation(t.Begin, t.Bytes))
                    return Hole("pointer", "相对表项或中间下标表含有尚未支持的重定位。");
            var cases = ImmutableArray.CreateBuilder<IndirectCase>();
            for (int i = 0; i <= first.Maximum; i++)
            {
                ulong index = (ulong)i;
                if (first != table)
                {
                    ulong value = image.ReadUnsigned(first.Begin + index * (ulong)(first.Read.Width / 8), first.Read.Width / 8);
                    var selected = new TermRewrite(Terms, t => t == first.Read.Result ? Terms.Constant(value, t.Width) : null).Map(table.Selector);
                    if (selected.ConstantValue is not { } constant) return Hole("shape", "中间表项替换后下标仍含未知值。");
                    if (constant > table.Maximum) return Hole("bound", "第二级表下标不满足已证明的上界。");
                    index = (ulong)constant;
                }
                ulong slot = table.Begin + index * (ulong)(table.Read.Width / 8);
                ulong destination;
                if (absolute)
                {
                    if (table.Read.Width != image.PointerWidth * 8 || image.ReadPointer(slot) is not PointerTarget.Internal pointer)
                        return Hole("pointer", "绝对地址表项不能解析为映像内指针。");
                    destination = pointer.Offset;
                }
                else
                {
                    var value = image.ReadUnsigned(slot, table.Read.Width / 8);
                    var evaluated = new TermRewrite(Terms, t => t == table.Read.Result ? Terms.Constant(value, t.Width)
                        : ImageRoot(t) ? Terms.Constant(0, t.Width) : null).Map(target);
                    if (evaluated.ConstantValue is not { } constant || constant > ulong.MaxValue)
                        return Hole("shape", "相对表项替换后仍含未知值。");
                    destination = (ulong)constant;
                }
                if (destination < range.Start || destination - range.Start >= range.Length)
                    return Hole("target-range", "表目标不在当前函数范围内。");
                cases.Add(new(i, destination));
            }
            // 已覆盖路径上所有可达下标，默认边不可达，复用首项避免引入外部边。
            return new IndirectTable(first.Selector, cases.ToImmutable(), cases[0].Target);
        }
        private bool WritableBase(Term address)
        {
            var parts = new List<Term>(); Flatten(address, parts);
            if (parts.Count(ImageRoot) != 1 || parts.Where(t => !ImageRoot(t)).Any(t => Walk(t).Any(ImageRoot))) return false;
            var offset = parts.Where(t => t.ConstantValue is not null).Aggregate(BigInteger.Zero, (n, t) => n + t.ConstantValue!.Value)
                & ((BigInteger.One << address.Width) - 1);
            return offset <= ulong.MaxValue && context.Image is { } image
                && image.Query((ulong)offset) is { Storage: not StorageKind.Unmapped, Writable: true };
        }
        private sealed record Table(MemoryRead Read, Term Selector, ulong Begin, int Maximum, ulong Bytes);
        private (Table? Table, IndirectUnknown? Failure) Describe(MemoryRead read, IImage image)
        {
            if (read.Width is not (8 or 16 or 32 or 64)) return (null, Hole("shape", "表元素位宽不支持。"));
            var parts = new List<Term>(); Flatten(read.Address, parts);
            var variables = parts.Where(t => !ImageRoot(t) && t.ConstantValue is null).ToArray();
            if (parts.Count(ImageRoot) != 1 || variables.Length != 1) return (null, Hole("shape", "表地址不是映像基址加常量与单一下标。"));
            var selector = Unscale(variables[0], read.Width / 8, out var scale);
            if (scale != read.Width / 8) return (null, Hole("shape", "表索引步长不等于元素宽度。"));
            var start = parts.Where(t => t.ConstantValue is not null).Aggregate(BigInteger.Zero, (n, t) => n + t.ConstantValue!.Value)
                & ((BigInteger.One << read.Address.Width) - 1);
            if (start > ulong.MaxValue) return (null, Hole("storage", "表地址超出映像地址宽度。"));
            var maximum = Maximum(selector);
            foreach (var condition in context.Conditions)
                maximum = BigInteger.Min(maximum, Bound(expand.Map(condition.Condition), condition.IsTrue, selector));
            // 预算只限制可枚举规模，不作为下标的证明。
            if (maximum >= 65536) return (null, Hole("bound", "没有可枚举的已证明下标上界。"));
            if (maximum < 0) return (null, Hole("bound", "到达跳转的条件互相矛盾。"));
            ulong begin = (ulong)start, bytes = (ulong)(maximum + 1) * (ulong)(read.Width / 8);
            if (begin > ulong.MaxValue - bytes || !ReadOnly(image, begin, bytes))
                return (null, Hole("storage", "表不完全位于映像只读数据中。"));
            return (new(read, selector, begin, (int)maximum, bytes), null);
        }
        private static bool ReadOnly(IImage image, ulong start, ulong length)
        {
            while (length > 0)
            {
                var info = image.Query(start);
                if (info.Storage != StorageKind.FileContent || info.Writable || info.Executable || info.AvailableBytes == 0) return false;
                ulong take = Math.Min(length, info.AvailableBytes); start += take; length -= take;
            }
            return true;
        }
        private static void Flatten(Term t, List<Term> parts)
        {
            if (Is(t, Add)) foreach (var child in t.Operands) Flatten(child, parts);
            else parts.Add(t);
        }
        private static Term Unscale(Term t, int stride, out BigInteger scale)
        {
            scale = 1;
            // 常量移位、零扩展均由规范形中的零段表示。
            if (t.Kind == TermKind.Concat)
            {
                var parts = t.Operands.ToList();
                if (parts[0].ConstantValue == 0 && (BigInteger.One << parts[0].Width) == stride)
                { scale = BigInteger.One << parts[0].Width; parts.RemoveAt(0); }
                while (parts.Count > 1 && parts[^1].ConstantValue == 0) parts.RemoveAt(parts.Count - 1);
                t = parts.Count == 1 ? parts[0] : t.Table.Concat(parts.ToArray());
            }
            if (stride != 1 && Is(t, Multiply) && t.Operands.FirstOrDefault(x => x.ConstantValue == stride) is { } factor)
            { scale *= factor.ConstantValue!.Value; t = t.Operands.First(x => x != factor); }
            while (t.Kind == TermKind.Concat && t.Operands.Length == 2 && t.Operands[1].ConstantValue == 0)
                t = t.Operands[0];
            return t;
        }
        private static bool RelativeShape(Term target, Term read)
        {
            var parts = new List<Term>(); Flatten(target, parts);
            if (parts.Count(ImageRoot) != 1) return false;
            var variables = parts.Where(t => !ImageRoot(t) && t.ConstantValue is null).ToArray();
            if (variables.Length != 1) return false;
            return Walk(variables[0]).All(t => t == read || t.ConstantValue is not null
                || t.Kind is TermKind.Concat or TermKind.Slice || Is(t, SignExtend) || Is(t, ZeroExtend) || Is(t, Multiply));
        }
        private static BigInteger Maximum(Term t)
        {
            if (t.ConstantValue is { } c) return c;
            if (t.Kind == TermKind.Concat)
            {
                BigInteger result = 0; int shift = 0;
                foreach (var part in t.Operands) { result += Maximum(part) << shift; shift += part.Width; }
                return result;
            }
            if (Is(t, And)) return t.Operands.Select(Maximum).Min();
            return (BigInteger.One << t.Width) - 1;
        }
        private BigInteger Bound(Term condition, bool truth, Term selector)
        {
            var unlimited = (BigInteger.One << selector.Width) - 1;
            if (Is(condition, Not)) return Bound(condition.Operands[0], !truth, selector);
            if (Is(condition, And) || Is(condition, Or))
            {
                var a = Bound(condition.Operands[0], truth, selector);
                var b = Bound(condition.Operands[1], truth, selector);
                return Is(condition, And) == truth ? BigInteger.Min(a, b) : BigInteger.Max(a, b);
            }
            // zext(x)+c 的进位为假，等价于 x < 2^w-c。
            if (!truth && condition.Kind == TermKind.Slice && condition.Width == 1
                && condition.SliceLow == condition.Operands[0].Width - 1)
            {
                int width = condition.SliceLow.Value;
                var sum = new List<Term>(); Flatten(condition.Operands[0], sum);
                var variables = sum.Where(t => t.ConstantValue is null).ToArray();
                var constant = sum.Where(t => t.ConstantValue is not null).Aggregate(BigInteger.Zero, (n, t) => n + t.ConstantValue!.Value);
                var modulus = BigInteger.One << width;
                if (selector.Width <= width && variables.Length == 1 && constant <= modulus
                    && variables[0] == Terms.Apply(new CoreOperator(ZeroExtend), width + 1, selector))
                    return modulus - constant - 1;
            }
            if (Is(condition, UnsignedLess))
            {
                var a = condition.Operands[0]; var b = condition.Operands[1];
                if (truth && a == selector && b.ConstantValue is { } upper) return upper - 1;
                if (!truth && b == selector && a.ConstantValue is { } inclusive) return inclusive;
            }
            if (Is(condition, Equal) && truth)
            {
                foreach (var (a, b) in new[] { (condition.Operands[0], condition.Operands[1]), (condition.Operands[1], condition.Operands[0]) })
                {
                    if (b.ConstantValue is not { } equal) continue;
                    var value = a;
                    while (value.Kind == TermKind.Concat && value.Operands.Length == 2 && value.Operands[1].ConstantValue == 0)
                        value = value.Operands[0];
                    if (equal >= (BigInteger.One << value.Width)) return -1;
                    var constant = Terms.Constant(equal, value.Width);
                    var selected = new TermRewrite(Terms, t => t == value ? constant : null).Map(selector);
                    if (selected.ConstantValue is { } upper) return upper;
                }
            }
            return unlimited;
        }
    }
}
