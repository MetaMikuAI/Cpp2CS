using Cpp2CS.Ir;
using System.Runtime.CompilerServices;

namespace Cpp2CS.Recovery.Inlining;

internal enum TermKind : byte { Constant, Atom, Operation, Read, Tuple, Address, Location }

/// <summary>原子：调用方入口的局部、调用方实参、模板形参、事件结果、字符串与元数据记号。</summary>
internal enum AtomKind : byte { Entry, Argument, Formal, Result, Text, Token }

internal enum OpCode : byte
{
    Binary, Unary, Convert, Compare, Choice, Not, And, Or,
    /// <summary>0/1 值作为条件（宽度 1）。</summary>
    ToBit,
    /// <summary>isinst：对象是目标类型时为对象，否则为 null。</summary>
    IsInst,
    /// <summary>castclass 失败（对象非空且不是目标类型）。</summary>
    CastFails,
    /// <summary>unbox.any 的值与失败条件（null 或类型不符）。</summary>
    Unbox, UnboxFails,
    /// <summary>unbox 得到的地址。</summary>
    UnboxAddress,
    /// <summary>有符号除法溢出（被除数为最小值且除数为 -1）。</summary>
    DivOverflow,
    /// <summary>固定数组得到首元素地址。</summary>
    Pin,
    /// <summary>多维数组的某一下标越界。</summary>
    OutOfRange,
}

/// <summary>位置的根：实例字段、静态字段、数组元素、多维数组元素、经引用、可取址的局部、装箱内容、不可变的长度与维度。</summary>
internal enum RootKind : byte { Field, Static, Element, MultiElement, Reference, Cell, Length, StringLength, Bound }

/// <summary>驻留的字段路径；同一表内相同序列是同一实例。</summary>
internal sealed class FieldPath
{
    public static readonly FieldPath Empty = new([], 0);
    public readonly FieldRef[] Fields;
    public readonly int Id;
    internal FieldPath(FieldRef[] fields, int id) { Fields = fields; Id = id; }
    public int Count => Fields.Length;
    public override string ToString() => string.Join(".", Fields.Select(f => f.Field.Name));
}

/// <summary>
/// 证明使用的项。项在构造时规范化并驻留：同一张表内语义恒等的项是同一个实例，相等就是引用相等。
/// Hint 是调用方一侧求值得到的托管类型，只供写回，不参与身份。
/// </summary>
internal sealed class Term
{
    public readonly int Id;
    public readonly TermKind Kind;
    /// <summary>原子种类、运算或根的种类。</summary>
    public readonly byte Code;
    /// <summary>运算的子种类（BinOp、UnOp、ConvKind、Cond）、读取的堆版本、可取址局部的帧、维度。</summary>
    public readonly int Aux;
    public readonly int Width;
    /// <summary>原子的键、运算的类型参数、位置的路径。</summary>
    public readonly object? Key;
    public readonly Term[] Args;
    public readonly bool HasFormal;
    /// <summary>值只取 0 或 1。</summary>
    public readonly bool Bit;
    public TypeRef? Hint;

    internal Term(int id, TermKind kind, byte code, int aux, int width, object? key, Term[] args, bool bit)
    {
        (Id, Kind, Code, Aux, Width, Key, Args, Bit) = (id, kind, code, aux, width, key, args, bit);
        HasFormal = kind == TermKind.Atom && code == (byte)AtomKind.Formal || args.Any(a => a.HasFormal);
    }

    public bool IsConstant => Kind == TermKind.Constant;
    public ulong Bits => (ulong)Key!;
    public AtomKind Atom => (AtomKind)Code;
    public OpCode Op => (OpCode)Code;
    public RootKind Root => (RootKind)Code;
    public bool IsAtom(AtomKind kind) => Kind == TermKind.Atom && Code == (byte)kind;
    public bool IsOp(OpCode op) => Kind == TermKind.Operation && Code == (byte)op;
    public BinOp BinOp => (BinOp)Aux;
    public Cond Cond => (Cond)Aux;
    public ConvKind Conv => (ConvKind)Aux;
    /// <summary>位置的路径。</summary>
    public FieldPath Path => TermTable.PathOf(this);
    /// <summary>读取与地址的位置。</summary>
    public Term Location => Args[0];

    public override string ToString() => Kind switch
    {
        TermKind.Constant => Width == 64 && Bits == 0 ? "0" : $"{(long)Bits}",
        TermKind.Atom => Atom switch
        {
            AtomKind.Entry => $"in:{Key}",
            AtomKind.Argument => $"arg:{Key}",
            AtomKind.Formal => $"F:{Key}",
            AtomKind.Result => $"r:{Key}",
            AtomKind.Text => $"\"{Key}\"",
            _ => $"{Key}",
        },
        TermKind.Operation => Op switch
        {
            OpCode.Binary => $"({Args[0]} {BinOp} {Args[1]})",
            OpCode.Unary => $"{(UnOp)Aux}({Args[0]})",
            OpCode.Convert => $"{Conv}{Width}({Args[0]})",
            OpCode.Compare => $"({Args[0]} {Cond} {Args[1]})",
            OpCode.Not => $"!{Args[0]}",
            OpCode.And => $"({Args[0]} && {Args[1]})",
            OpCode.Or => $"({Args[0]} || {Args[1]})",
            OpCode.Choice => $"({Args[0]} ? {Args[1]} : {Args[2]})",
            _ => $"{Op}({string.Join(", ", Args.Select(a => a.ToString()))})",
        },
        TermKind.Read => $"[{Args[0]}]@{Aux}",
        TermKind.Tuple => $"{{{string.Join(", ", Args.Select(a => a.ToString()))}}}",
        TermKind.Address => $"&{Args[0]}",
        _ => Root switch
        {
            RootKind.Field => $"{Args[0]}.{Path}",
            RootKind.Static => $"{Path}",
            RootKind.Element => $"{Args[0]}[{Args[1]}]{(Path.Count > 0 ? "." + Path : "")}",
            RootKind.MultiElement => $"{Args[0]}[{string.Join(",", Args.Skip(1))}]{(Path.Count > 0 ? "." + Path : "")}",
            RootKind.Reference => $"*{Args[0]}{(Path.Count > 0 ? "." + Path : "")}",
            RootKind.Cell => $"cell{Aux}:{TermTable.CellVariable(this)}{(TermTable.PathOf(this).Count > 0 ? "." + TermTable.PathOf(this) : "")}",
            RootKind.Length => $"len({Args[0]})",
            RootKind.StringLength => $"slen({Args[0]})",
            _ => $"bound({Args[0]},{Aux})",
        },
    };
}

/// <summary>项表：驻留、规范化与代换。一次证明（含复核）使用一张表。</summary>
internal sealed class TermTable
{
    private readonly record struct Key(TermKind Kind, byte Code, int Aux, int Width, object? Extra, int A, int B, int C, int[]? More);

    private readonly Dictionary<Key, Term> terms = [];
    private readonly Dictionary<string, FieldPath> paths = new(StringComparer.Ordinal);
    private readonly Dictionary<FieldPath, Dictionary<FieldRef, FieldPath>> extended = [];
    private int next;

    public Term Zero64 { get; }
    public Term True { get; }
    public Term False { get; }

    public TermTable()
    {
        Zero64 = Constant(0, 64);
        True = Constant(1, 1);
        False = Constant(0, 1);
    }

    private Term Intern(TermKind kind, byte code, int aux, int width, object? extra, Term[] args, bool bit)
    {
        var key = new Key(kind, code, aux, width, extra,
            args.Length > 0 ? args[0].Id : -1, args.Length > 1 ? args[1].Id : -1, args.Length > 2 ? args[2].Id : -1,
            args.Length > 3 ? args.Select(a => a.Id).ToArray() : null);
        if (terms.TryGetValue(key, out var known)) return known;
        var term = new Term(next++, kind, code, aux, width, extra, args, bit);
        terms[key] = term;
        return term;
    }

    private sealed class ArrayKey(int[] ids)
    {
        public readonly int[] Ids = ids;
        public override bool Equals(object? obj) => obj is ArrayKey other && Ids.AsSpan().SequenceEqual(other.Ids);
        public override int GetHashCode() { var h = new HashCode(); foreach (var id in Ids) h.Add(id); return h.ToHashCode(); }
    }

    // Key 的 More 字段是数组，记录相等按引用；超过三个子项的项另以 ArrayKey 作 Extra。
    private Term InternMany(TermKind kind, byte code, int aux, int width, object? extra, Term[] args, bool bit) =>
        args.Length <= 3 ? Intern(kind, code, aux, width, extra, args, bit)
            : InternWide(kind, code, aux, width, extra, args, bit);

    private readonly Dictionary<(TermKind, byte, int, int, object?, ArrayKey), Term> wide = [];
    private Term InternWide(TermKind kind, byte code, int aux, int width, object? extra, Term[] args, bool bit)
    {
        var key = (kind, code, aux, width, extra, new ArrayKey(args.Select(a => a.Id).ToArray()));
        if (wide.TryGetValue(key, out var known)) return known;
        var term = new Term(next++, kind, code, aux, width, extra, args, bit);
        wide[key] = term;
        return term;
    }

    // ---- 路径 ----

    /// <summary>
    /// 字段所在类型的存储身份：IL2CPP 对引用类型实参共享代码与布局，共享实例的方法体以 object 代替引用类型实参，
    /// 同一对象上 C&lt;object&gt;.f 与 C&lt;Foo&gt;.f 是同一存储。值类型实参按实际类型区分。
    /// </summary>
    private static string StorageKey(TypeRef type) => type is DefinitionRef { Arguments.Count: > 0 } d
        ? $"{d.Definition.FullName}<{string.Join(",", d.Arguments.Select(a => ManagedTypes.IsReferenceType(a) ? "ref" : StorageKey(a)))}>"
        : type.ToString();

    public FieldPath Path(IReadOnlyList<FieldRef> fields)
    {
        var path = FieldPath.Empty;
        foreach (var field in fields) path = Extend(path, field);
        return path;
    }

    public FieldPath Extend(FieldPath path, FieldRef field)
    {
        if (!extended.TryGetValue(path, out var children)) extended[path] = children = [];
        if (children.TryGetValue(field, out var known)) return known;
        var fields = path.Fields.Append(field).ToArray();
        var text = string.Join("|", fields.Select(f => $"{f.Field.Index}:{StorageKey(f.DeclaringType)}"));
        if (!paths.TryGetValue(text, out var interned)) paths[text] = interned = new FieldPath(fields, paths.Count + 1);
        return children[field] = interned;
    }

    public FieldPath Concat(FieldPath a, FieldPath b)
    {
        foreach (var field in b.Fields) a = Extend(a, field);
        return a;
    }

    public FieldPath Prefix(FieldPath path, int count)
    {
        var result = FieldPath.Empty;
        for (var i = 0; i < count; i++) result = Extend(result, path.Fields[i]);
        return result;
    }

    public FieldPath Suffix(FieldPath path, int from)
    {
        var result = FieldPath.Empty;
        for (var i = from; i < path.Count; i++) result = Extend(result, path.Fields[i]);
        return result;
    }

    // ---- 原子与常量 ----

    public static ulong Mask(int width) => width >= 64 ? ulong.MaxValue : (1UL << width) - 1;

    public Term Constant(ulong bits, int width) => Intern(TermKind.Constant, 0, 0, width, bits & Mask(width), [], (bits & Mask(width)) <= 1);

    public Term Atom(AtomKind kind, object key, int width, bool bit = false) => Intern(TermKind.Atom, (byte)kind, 0, width, key, [], bit);

    // ---- 位置 ----

    public Term FieldRoot(Term obj, FieldPath path) => Intern(TermKind.Location, (byte)RootKind.Field, 0, 0, path, [obj], false);
    public Term StaticRoot(FieldPath path) => Intern(TermKind.Location, (byte)RootKind.Static, 0, 0, path, [], false);
    public Term ElementRoot(Term array, Term index, FieldPath path) =>
        Intern(TermKind.Location, (byte)RootKind.Element, 0, 0, path, [array, Index(index)], false);
    public Term MultiElementRoot(Term array, IReadOnlyList<Term> indices, FieldPath path) =>
        InternMany(TermKind.Location, (byte)RootKind.MultiElement, 0, 0, path, [array, .. indices], false);
    public Term CellRoot(int frame, Variable variable, FieldPath path) =>
        Intern(TermKind.Location, (byte)RootKind.Cell, frame, 0, new CellKey(path, variable), [], false);
    public Term LengthRoot(Term array) => Intern(TermKind.Location, (byte)RootKind.Length, 0, 0, FieldPath.Empty, [array], false);
    public Term StringLengthRoot(Term text) => Intern(TermKind.Location, (byte)RootKind.StringLength, 0, 0, FieldPath.Empty, [text], false);
    public Term BoundRoot(Term array, int dimension, bool lower) =>
        Intern(TermKind.Location, (byte)RootKind.Bound, dimension * 2 + (lower ? 1 : 0), 0, FieldPath.Empty, [array], false);

    /// <summary>经引用的位置：引用是某个位置的地址时就是那个位置（加上路径）。</summary>
    public Term ReferenceRoot(Term address, FieldPath path) => address.Kind == TermKind.Address
        ? Append(address.Location, path)
        : Intern(TermKind.Location, (byte)RootKind.Reference, 0, 0, path, [address], false);

    /// <summary>位置的前缀：只保留路径的前 keep 个字段。</summary>
    public Term? Truncate(Term location, int keep)
    {
        var prefix = Prefix(PathOf(location), keep);
        return location.Root switch
        {
            RootKind.Field when keep >= 1 => FieldRoot(location.Args[0], prefix),
            RootKind.Static when keep >= 1 => StaticRoot(prefix),
            RootKind.Element => ElementRoot(location.Args[0], location.Args[1], prefix),
            RootKind.Cell => CellRoot(location.Aux, CellVariable(location), prefix),
            RootKind.Reference => ReferenceRoot(location.Args[0], prefix),
            _ => null,
        };
    }

    /// <summary>可取址局部的键：路径与变量。</summary>
    internal sealed record CellKey(FieldPath Path, Variable Variable);

    /// <summary>结构体值的叶子原子的键：根（形参序号、实参序号或局部）与叶子路径的 Id。</summary>
    internal readonly record struct LeafKey(object Root, int Path)
    {
        public override string ToString() => $"({Root}, {Path})";
    }

    public static FieldPath PathOf(Term location) => location.Key is CellKey cell ? cell.Path : (FieldPath)location.Key!;
    public static Variable CellVariable(Term location) => ((CellKey)location.Key!).Variable;

    /// <summary>位置加上更深的字段路径。</summary>
    public Term Append(Term location, FieldPath more)
    {
        if (more.Count == 0) return location;
        var path = Concat(PathOf(location), more);
        return location.Root switch
        {
            RootKind.Field => FieldRoot(location.Args[0], path),
            RootKind.Static => StaticRoot(path),
            RootKind.Element => Intern(TermKind.Location, (byte)RootKind.Element, 0, 0, path, location.Args, false),
            RootKind.MultiElement => InternMany(TermKind.Location, (byte)RootKind.MultiElement, 0, 0, path, location.Args, false),
            RootKind.Reference => Intern(TermKind.Location, (byte)RootKind.Reference, 0, 0, path, location.Args, false),
            RootKind.Cell => CellRoot(location.Aux, CellVariable(location), path),
            _ => throw new InvalidOperationException($"不可变位置没有字段：{location}"),
        };
    }

    /// <summary>入口时已知内容的位置：入口读取（版本 0）就是这个值。</summary>
    private readonly Dictionary<Term, Term> initial = new(ReferenceEqualityComparer.Instance);

    /// <summary>记下位置在入口时的内容。入口知识是对入口状态的描述，不是入口之后的写入：它不使别的位置的读取变得不可判定。</summary>
    public void Know(Term location, Term value)
    {
        if (value.Width == 0 && value.Kind != TermKind.Constant) return;
        initial.TryAdd(location, value);
    }

    public Term Read(int version, Term location, int width, bool bit)
    {
        if (Immutable(location)) version = 0;
        if (version == 0 && initial.TryGetValue(location, out var known) && known.Width == width) return known;
        return Intern(TermKind.Read, 0, version, width, null, [location], bit);
    }

    public static bool Immutable(Term location) => location.Root is RootKind.Length or RootKind.StringLength or RootKind.Bound;

    public Term Address(Term location) => Intern(TermKind.Address, 0, 0, 64, null, [location], false);

    public Term Tuple(DefinitionRef type, IReadOnlyList<Term> leaves) =>
        InternMany(TermKind.Tuple, 0, 0, 0, type, leaves.ToArray(), false);

    /// <summary>数组下标：32 位整数的零扩展与符号扩展不区分（越界检查按无符号比较，负数扩展后同样越界）。</summary>
    private Term Index(Term index) =>
        index.IsOp(OpCode.Convert) && index.Conv is ConvKind.ZeroExtend or ConvKind.SignExtend && index.Args[0].Width == 32 ? index.Args[0] : index;

    // ---- 运算 ----

    public Term Operation(OpCode op, int aux, int width, object? extra, params Term[] args) =>
        // null 的类型转换与数组存储永远成立。
        op == OpCode.CastFails && args[^1] is { IsConstant: true, Bits: 0 } ? False
        : InternMany(TermKind.Operation, (byte)op, aux, width, extra, args, op is OpCode.Compare or OpCode.Not or OpCode.And or OpCode.Or or OpCode.ToBit or OpCode.CastFails or OpCode.UnboxFails or OpCode.DivOverflow);

    private static bool Commutative(BinOp op) => op is BinOp.Add or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor
        or BinOp.MulHighS or BinOp.MulHighU or BinOp.FAdd or BinOp.FMul or BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber;

    private static long Signed(ulong bits, int width) => width >= 64 ? (long)bits : (long)(bits << (64 - width)) >> (64 - width);

    public Term Binary(BinOp op, Term a, Term b, int width)
    {
        if (Commutative(op) && a.Id > b.Id) (a, b) = (b, a);
        if (a.IsConstant && b.IsConstant && Fold(op, a.Bits, b.Bits, width) is { } folded) return Constant(folded, width);
        if (Commutative(op) && a.IsConstant) (a, b) = (b, a);
        if (b.IsConstant)
        {
            var k = b.Bits;
            switch (op)
            {
                case BinOp.Sub: return Binary(BinOp.Add, a, Constant(0 - k, width), width);
                case BinOp.Add when k == 0:
                case BinOp.Or when k == 0:
                case BinOp.Xor when k == 0:
                case BinOp.Shl or BinOp.LShr or BinOp.AShr or BinOp.Ror when k == 0:
                case BinOp.Mul when k == 1:
                case BinOp.SDiv or BinOp.UDiv when k == 1:
                    return a;
                case BinOp.And when (k & Mask(width)) == Mask(width):
                    return a;
                case BinOp.And when k == 0:
                case BinOp.Mul when k == 0:
                    return Constant(0, width);
                case BinOp.And when a.Bit && (k & 1) == 1:
                    return a;
                case BinOp.Add when a.IsOp(OpCode.Binary) && a.BinOp == BinOp.Add && a.Args[1].IsConstant:
                    return Binary(BinOp.Add, a.Args[0], Constant(a.Args[1].Bits + k, width), width);
                case BinOp.Xor when a.Bit && (k & Mask(width)) == 1:
                    return Widen(Not(ToBit(a)), width);
            }
        }
        if (op == BinOp.Sub && ReferenceEquals(a, b)) return Constant(0, width);
        if (op is BinOp.Xor && ReferenceEquals(a, b)) return Constant(0, width);
        if (op is BinOp.And or BinOp.Or && ReferenceEquals(a, b)) return a;
        var bit = op is BinOp.And && (a.Bit || b.Bit) || op is BinOp.Or or BinOp.Xor && a.Bit && b.Bit;
        return Intern(TermKind.Operation, (byte)OpCode.Binary, (int)op, width, null, [a, b], bit);
    }

    private static ulong? Fold(BinOp op, ulong x, ulong y, int width)
    {
        var m = Mask(width);
        var shift = (int)(y & (ulong)(width - 1));
        return op switch
        {
            BinOp.Add => (x + y) & m,
            BinOp.Sub => (x - y) & m,
            BinOp.Mul => (x * y) & m,
            BinOp.And => x & y,
            BinOp.Or => x | y,
            BinOp.Xor => x ^ y,
            BinOp.Shl when width is 32 or 64 => (x << shift) & m,
            BinOp.LShr when width is 32 or 64 => (x & m) >> shift,
            BinOp.AShr when width is 32 or 64 => (ulong)(Signed(x, width) >> shift) & m,
            BinOp.UDiv when y != 0 => (x / y) & m,
            BinOp.URem when y != 0 => (x % y) & m,
            BinOp.SDiv when y != 0 && !(Signed(y, width) == -1 && x == 1UL << (width - 1)) => (ulong)(Signed(x, width) / Signed(y, width)) & m,
            BinOp.SRem when y != 0 && Signed(y, width) != -1 => (ulong)(Signed(x, width) % Signed(y, width)) & m,
            _ => null,
        };
    }

    public Term Unary(UnOp op, Term a, int width)
    {
        if (a.IsConstant)
            switch (op)
            {
                case UnOp.Neg: return Constant(0 - a.Bits, width);
                case UnOp.Not: return Constant(~a.Bits, width);
            }
        if (op is UnOp.Neg or UnOp.Not && a.IsOp(OpCode.Unary) && (UnOp)a.Aux == op) return a.Args[0];
        return Intern(TermKind.Operation, (byte)OpCode.Unary, (int)op, width, null, [a], false);
    }

    public Term Convert(ConvKind kind, Term a, int width)
    {
        if (kind is ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate or ConvKind.Bitcast && a.Width == width) return a;
        if (a.IsConstant)
            switch (kind)
            {
                case ConvKind.ZeroExtend: case ConvKind.Truncate: return Constant(a.Bits, width);
                case ConvKind.SignExtend: return Constant((ulong)Signed(a.Bits, a.Width), width);
            }
        if (kind == ConvKind.Truncate && a.IsOp(OpCode.Convert) && a.Conv is ConvKind.ZeroExtend or ConvKind.SignExtend)
        {
            var inner = a.Args[0];
            if (inner.Width == width) return inner;
            if (inner.Width > width) return Convert(ConvKind.Truncate, inner, width);
            return Convert(a.Conv, inner, width);
        }
        if (kind == ConvKind.Truncate && width == 1 && a.Bit) return ToBit(a);
        if (kind == ConvKind.ZeroExtend && a.IsOp(OpCode.ToBit) && a.Args[0].Width == width) return a.Args[0];
        if (kind == ConvKind.ZeroExtend && a.IsOp(OpCode.Convert) && a.Conv == ConvKind.ZeroExtend) return Convert(ConvKind.ZeroExtend, a.Args[0], width);
        if (kind == ConvKind.SignExtend && a.IsOp(OpCode.Convert) && a.Conv is ConvKind.SignExtend or ConvKind.ZeroExtend && a.Args[0].Width < a.Width)
            return Convert(a.Conv, a.Args[0], width);
        if (kind == ConvKind.SignExtend && a.Bit && a.Width > 1) return Convert(ConvKind.ZeroExtend, a, width);
        var bit = kind is ConvKind.ZeroExtend or ConvKind.Truncate && a.Bit;
        return Intern(TermKind.Operation, (byte)OpCode.Convert, (int)kind, width, null, [a], bit);
    }

    /// <summary>0/1 值写成整数：宽度 1 的条件零扩展，或原本就是该宽度的 0/1 值。</summary>
    public Term Widen(Term bit, int width) => bit.Width == width ? bit : Convert(ConvKind.ZeroExtend, bit, width);

    /// <summary>0/1 值作为条件；非 0/1 值的条件是“不等于 0”。</summary>
    public Term ToBit(Term a)
    {
        if (a.Width == 1) return a;
        if (a.IsConstant) return a.Bits != 0 ? True : False;
        if (!a.Bit) return Compare(Cond.Ne, a, Constant(0, a.Width));
        if (a.IsOp(OpCode.Convert) && a.Conv == ConvKind.ZeroExtend) return ToBit(a.Args[0]);
        return Intern(TermKind.Operation, (byte)OpCode.ToBit, 0, 1, null, [a], true);
    }

    public Term Not(Term a)
    {
        a = ToBit(a);
        if (a.IsConstant) return a.Bits != 0 ? False : True;
        if (a.IsOp(OpCode.Not)) return a.Args[0];
        if (a.IsOp(OpCode.Compare) && Negate(a.Cond) is { } negated) return Compare(negated, a.Args[0], a.Args[1]);
        if (a.IsOp(OpCode.And)) return Or(Not(a.Args[0]), Not(a.Args[1]));
        if (a.IsOp(OpCode.Or)) return And(Not(a.Args[0]), Not(a.Args[1]));
        return Intern(TermKind.Operation, (byte)OpCode.Not, 0, 1, null, [a], true);
    }

    public Term And(Term a, Term b)
    {
        a = ToBit(a); b = ToBit(b);
        if (a.IsConstant) return a.Bits != 0 ? b : False;
        if (b.IsConstant) return b.Bits != 0 ? a : False;
        if (ReferenceEquals(a, b)) return a;
        if (ReferenceEquals(Not(a), b)) return False;
        if (a.Id > b.Id) (a, b) = (b, a);
        return Intern(TermKind.Operation, (byte)OpCode.And, 0, 1, null, [a, b], true);
    }

    public Term Or(Term a, Term b)
    {
        a = ToBit(a); b = ToBit(b);
        if (a.IsConstant) return a.Bits != 0 ? True : b;
        if (b.IsConstant) return b.Bits != 0 ? True : a;
        if (ReferenceEquals(a, b)) return a;
        if (ReferenceEquals(Not(a), b)) return True;
        if (a.Id > b.Id) (a, b) = (b, a);
        return Intern(TermKind.Operation, (byte)OpCode.Or, 0, 1, null, [a, b], true);
    }

    public Term Choice(Term condition, Term a, Term b, int width)
    {
        condition = ToBit(condition);
        if (condition.IsConstant) return condition.Bits != 0 ? a : b;
        if (ReferenceEquals(a, b)) return a;
        if (condition.IsOp(OpCode.Not)) return Choice(condition.Args[0], b, a, width);
        if (a.IsConstant && b.IsConstant && a.Bits == 1 && b.Bits == 0) return Widen(condition, width);
        if (a.IsConstant && b.IsConstant && a.Bits == 0 && b.Bits == 1) return Widen(Not(condition), width);
        if (width == 1 && b.IsConstant && b.Bits == 0) return And(condition, a);
        if (width == 1 && a.IsConstant && a.Bits == 1) return Or(condition, b);
        return Intern(TermKind.Operation, (byte)OpCode.Choice, 0, width, null, [condition, a, b], a.Bit && b.Bit);
    }

    private static Cond? Negate(Cond cond) => cond switch
    {
        Cond.Eq => Cond.Ne, Cond.Ne => Cond.Eq,
        Cond.Slt => Cond.Sge, Cond.Sge => Cond.Slt, Cond.Sle => Cond.Sgt, Cond.Sgt => Cond.Sle,
        Cond.Ult => Cond.Uge, Cond.Uge => Cond.Ult, Cond.Ule => Cond.Ugt, Cond.Ugt => Cond.Ule,
        Cond.FEq => Cond.FUne, Cond.FUne => Cond.FEq, Cond.FNe => Cond.FUeq, Cond.FUeq => Cond.FNe,
        Cond.FLt => Cond.FUge, Cond.FUge => Cond.FLt, Cond.FLe => Cond.FUgt, Cond.FUgt => Cond.FLe,
        Cond.FGt => Cond.FUle, Cond.FUle => Cond.FGt, Cond.FGe => Cond.FUlt, Cond.FUlt => Cond.FGe,
        Cond.FUnordered => Cond.FOrdered, Cond.FOrdered => Cond.FUnordered,
        Cond.Neg => Cond.NotNeg, Cond.NotNeg => Cond.Neg, Cond.Overflow => Cond.NoOverflow, Cond.NoOverflow => Cond.Overflow,
        _ => null,
    };

    private static Cond Swap(Cond cond) => cond switch
    {
        Cond.Slt => Cond.Sgt, Cond.Sgt => Cond.Slt, Cond.Sle => Cond.Sge, Cond.Sge => Cond.Sle,
        Cond.Ult => Cond.Ugt, Cond.Ugt => Cond.Ult, Cond.Ule => Cond.Uge, Cond.Uge => Cond.Ule,
        Cond.FLt => Cond.FGt, Cond.FGt => Cond.FLt, Cond.FLe => Cond.FGe, Cond.FGe => Cond.FLe,
        Cond.FUlt => Cond.FUgt, Cond.FUgt => Cond.FUlt, Cond.FUle => Cond.FUge, Cond.FUge => Cond.FUle,
        _ => cond,
    };

    private static bool Integer(Cond cond) => cond is >= Cond.Eq and <= Cond.Uge;
    private static bool SymmetricCond(Cond cond) => cond is Cond.Eq or Cond.Ne or Cond.FEq or Cond.FNe or Cond.FUnordered or Cond.FOrdered or Cond.FUeq or Cond.FUne;

    /// <summary>
    /// 比较的规范形：整数比较与常量比较时常量在右、严格写成非严格；两侧都不是常量时只用小于、小于等于；
    /// 无符号与 0、1 的边界比较写成判零；0/1 值与 0、1 比较写成该位或其否定；两侧同源扩展时在原宽度比较。
    /// </summary>
    public Term Compare(Cond cond, Term a, Term b)
    {
        if (cond is Cond.Neg or Cond.NotNeg or Cond.Overflow or Cond.NoOverflow)
            return Intern(TermKind.Operation, (byte)OpCode.Compare, (int)cond, 1, null, [a, b], true);
        if (!Integer(cond))
        {
            if (cond is Cond.FGt or Cond.FGe or Cond.FUgt or Cond.FUge) (cond, a, b) = (Swap(cond), b, a);
            if (SymmetricCond(cond) && a.Id > b.Id) (a, b) = (b, a);
            return Intern(TermKind.Operation, (byte)OpCode.Compare, (int)cond, 1, null, [a, b], true);
        }
        var width = Math.Max(a.Width, b.Width);
        if (a.IsConstant && b.IsConstant) return Evaluate(cond, a.Bits, b.Bits, width) ? True : False;
        if (a.IsConstant) (cond, a, b) = (Swap(cond), b, a);
        // 两侧同源扩展：在原宽度比较。
        if (a.IsOp(OpCode.Convert) && a.Conv is ConvKind.ZeroExtend or ConvKind.SignExtend && a.Args[0].Width > 1
            && (b.IsOp(OpCode.Convert) && b.Conv == a.Conv && b.Args[0].Width == a.Args[0].Width
                || b.IsConstant && FitsNarrow(b.Bits, a.Args[0].Width, a.Width, a.Conv == ConvKind.SignExtend)))
        {
            var narrow = a.Args[0].Width;
            var right = b.IsConstant ? Constant(b.Bits, narrow) : b.Args[0];
            var narrowed = a.Conv == ConvKind.ZeroExtend ? Unsigned(cond) : cond;
            return Compare(narrowed, a.Args[0], right);
        }
        if (b.IsConstant)
        {
            var w = a.Width;
            var k = b.Bits & Mask(w);
            var max = Mask(w);
            var smax = Mask(w) >> 1;
            var smin = smax + 1;
            switch (cond)
            {
                case Cond.Slt: if (k == smin) return False; (cond, k) = (Cond.Sle, (k - 1) & max); break;
                case Cond.Sgt: if (k == smax) return False; (cond, k) = (Cond.Sge, (k + 1) & max); break;
                case Cond.Ult: if (k == 0) return False; (cond, k) = (Cond.Ule, k - 1); break;
                case Cond.Ugt: if (k == max) return False; (cond, k) = (Cond.Uge, k + 1); break;
            }
            switch (cond)
            {
                case Cond.Ule when k == 0: cond = Cond.Eq; break;
                case Cond.Uge when k == 1: (cond, k) = (Cond.Ne, 0); break;
                case Cond.Uge when k == 0: return True;
                case Cond.Ule when k == max: return True;
                case Cond.Sle when k == smax: return True;
                case Cond.Sge when k == smin: return True;
            }
            if (a.Bit && cond is Cond.Eq or Cond.Ne && k <= 1)
                return (cond == Cond.Ne) == (k == 0) ? ToBit(a) : Not(ToBit(a));
            if (a.Bit && cond is Cond.Ne && k > 1 || a.Bit && cond is Cond.Eq && k > 1) return cond == Cond.Ne ? True : False;
            return Intern(TermKind.Operation, (byte)OpCode.Compare, (int)cond, 1, null, [a, Constant(k, w)], true);
        }
        if (ReferenceEquals(a, b)) return cond is Cond.Eq or Cond.Sle or Cond.Ule or Cond.Sge or Cond.Uge ? True : False;
        if (cond is Cond.Sgt or Cond.Sge or Cond.Ugt or Cond.Uge) (cond, a, b) = (Swap(cond), b, a);
        if (cond is Cond.Eq or Cond.Ne && a.Id > b.Id) (a, b) = (b, a);
        return Intern(TermKind.Operation, (byte)OpCode.Compare, (int)cond, 1, null, [a, b], true);
    }

    private static Cond Unsigned(Cond cond) => cond switch
    {
        Cond.Slt => Cond.Ult, Cond.Sle => Cond.Ule, Cond.Sgt => Cond.Ugt, Cond.Sge => Cond.Uge,
        _ => cond,
    };

    private static bool FitsNarrow(ulong value, int narrow, int wide, bool signed)
    {
        var m = Mask(wide);
        value &= m;
        if (!signed) return value <= Mask(narrow);
        var s = Signed(value, wide);
        return s >= -(1L << (narrow - 1)) && s < (1L << (narrow - 1));
    }

    public static bool Evaluate(Cond cond, ulong x, ulong y, int width)
    {
        x &= Mask(width); y &= Mask(width);
        long sx = Signed(x, width), sy = Signed(y, width);
        return cond switch
        {
            Cond.Eq => x == y, Cond.Ne => x != y,
            Cond.Slt => sx < sy, Cond.Sle => sx <= sy, Cond.Sgt => sx > sy, Cond.Sge => sx >= sy,
            Cond.Ult => x < y, Cond.Ule => x <= y, Cond.Ugt => x > y, Cond.Uge => x >= y,
            _ => throw new InvalidOperationException(cond.ToString()),
        };
    }

    // ---- 代换 ----

    /// <summary>自底向上代换原子并重新规范化；map 返回 null 表示不变。</summary>
    public Term Substitute(Term term, Func<Term, Term?> map, Dictionary<Term, Term> memo)
    {
        if (memo.TryGetValue(term, out var known)) return known;
        Term result;
        if (term.Kind is TermKind.Atom or TermKind.Constant) result = map(term) ?? term;
        else
        {
            var args = term.Args;
            Term[]? changed = null;
            for (var i = 0; i < args.Length; i++)
            {
                var mapped = Substitute(args[i], map, memo);
                if (!ReferenceEquals(mapped, args[i])) (changed ??= (Term[])args.Clone())[i] = mapped;
            }
            result = changed is null ? term : Rebuild(term, changed);
        }
        memo[term] = result;
        return result;
    }

    /// <summary>自顶向下替换任意子项（map 先作用于整个项，不变时再进入子项），重新规范化。</summary>
    public Term Replace(Term term, Func<Term, Term?> map, Dictionary<Term, Term> memo)
    {
        if (memo.TryGetValue(term, out var known)) return known;
        var result = map(term);
        if (result is null)
        {
            var args = term.Args;
            Term[]? changed = null;
            for (var i = 0; i < args.Length; i++)
            {
                var mapped = Replace(args[i], map, memo);
                if (!ReferenceEquals(mapped, args[i])) (changed ??= (Term[])args.Clone())[i] = mapped;
            }
            result = changed is null ? term : Rebuild(term, changed);
        }
        memo[term] = result;
        return result;
    }

    /// <summary>以新的子项重建同种项（经过规范化）。</summary>
    public Term Rebuild(Term term, Term[] args)
    {
        var rebuilt = term.Kind switch
        {
            TermKind.Operation => term.Op switch
            {
                OpCode.Binary => Binary(term.BinOp, args[0], args[1], term.Width),
                OpCode.Unary => Unary((UnOp)term.Aux, args[0], term.Width),
                OpCode.Convert => Convert(term.Conv, args[0], term.Width),
                OpCode.Compare => Compare(term.Cond, args[0], args[1]),
                OpCode.Choice => Choice(args[0], args[1], args[2], term.Width),
                OpCode.Not => Not(args[0]),
                OpCode.And => And(args[0], args[1]),
                OpCode.Or => Or(args[0], args[1]),
                OpCode.ToBit => ToBit(args[0]),
                OpCode.CastFails => Operation(OpCode.CastFails, term.Aux, term.Width, term.Key, args),
                _ => InternMany(TermKind.Operation, term.Code, term.Aux, term.Width, term.Key, args, term.Bit),
            },
            TermKind.Read => Read(term.Aux, args[0], term.Width, term.Bit),
            TermKind.Tuple => Tuple((DefinitionRef)term.Key!, args),
            TermKind.Address => Address(args[0]),
            TermKind.Location => term.Root switch
            {
                RootKind.Field => FieldRoot(args[0], term.Path),
                RootKind.Element => ElementRoot(args[0], args[1], term.Path),
                RootKind.MultiElement => MultiElementRoot(args[0], args.Skip(1).ToArray(), term.Path),
                RootKind.Reference => ReferenceRoot(args[0], term.Path),
                RootKind.Length => LengthRoot(args[0]),
                RootKind.StringLength => StringLengthRoot(args[0]),
                RootKind.Bound => BoundRoot(args[0], term.Aux / 2, term.Aux % 2 == 1),
                _ => term,
            },
            _ => term,
        };
        rebuilt.Hint ??= term.Hint;
        return rebuilt;
    }

    /// <summary>先序枚举项与全部子项。</summary>
    public static IEnumerable<Term> Walk(Term term)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        var stack = new Stack<Term>();
        stack.Push(term);
        while (stack.TryPop(out var current))
        {
            if (!seen.Add(current)) continue;
            yield return current;
            foreach (var child in current.Args) stack.Push(child);
        }
    }
}
