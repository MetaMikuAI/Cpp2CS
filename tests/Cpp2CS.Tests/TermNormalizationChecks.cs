using System.Diagnostics;
using System.Numerics;
using Cpp2CS.Native.Terms;
using static Cpp2CS.Native.Terms.CoreOperation;

namespace Cpp2CS.Tests;

internal static class TermNormalizationChecks
{
    public const string Command = "term-normalization";
    private const int Seed = 41017;
    private sealed record Input(int Index) : AtomIdentity { public override string StableText => $"test.input.{Index}"; }
    private sealed class Fixture(bool normalize = false, int salt = 0)
    {
        internal readonly TermTable T = new(normalize);
        internal Term X(int width = 32, int index = 0)
        {
            var atom = T.Atom(new Input(index), width);
            return salt == 0 ? atom : width == 1 ? O(Not, 1, atom) : O(Add, width, atom, C(salt & ((BigInteger.One << width) - 1), width));
        }
        internal Term C(BigInteger value, int width = 32) => T.Constant(value, width);
        internal Term O(CoreOperation op, int width, params Term[] args) => T.Apply(new CoreOperator(op), width, args);
    }
    private static Term Copy(Term t, TermTable target, Dictionary<Term, Term>? cache = null)
    {
        cache ??= new();
        if (cache.TryGetValue(t, out var known)) return known;
        var args = t.Operands.Select(x => Copy(x, target, cache)).ToArray();
        var result = t.Kind switch
        {
            TermKind.Constant => target.Constant(t.ConstantValue!.Value, t.Width),
            TermKind.Atom => target.Atom(t.Identity!, t.Width),
            TermKind.Unknown => target.Unknown(t.Width, t.Why!, ((UnknownValue)t.Payload!).Identity),
            TermKind.Undefined => target.Undefined(t.Width),
            TermKind.Operation => target.Apply(t.Operator!, t.Width, args),
            TermKind.Slice => target.Slice(args[0], t.SliceLow!.Value, t.Width),
            TermKind.Concat => target.Concat(args),
            _ => throw new InvalidOperationException()
        };
        cache.Add(t, result);
        return result;
    }
    private static string Shape(Term t) => $"{t.Kind}:{t.Width}:{t.Operator?.Name ?? t.ConstantValue?.ToString() ?? t.SliceLow?.ToString() ?? t.Identity?.StableText}({string.Join(',', t.Operands.Select(Shape))})";
    private static readonly (string Name, Func<Fixture, Term> Build)[] Rules =
    [
        ("constant-fold", f => f.O(Add, 32, f.C(123), f.C(456))),
        ("undefined-fold", f => f.O(UnsignedDivide, 32, f.C(1), f.C(0))),
        ("zero-extend", f => f.O(ZeroExtend, 64, f.X())),
        ("truncate", f => f.O(Truncate, 8, f.X())),
        ("nested-sign", f => f.O(SignExtend, 64, f.O(SignExtend, 32, f.X(8)))),
        ("sign-low-zero", f => f.O(SignExtend, 64, f.T.Concat(f.C(0, 8), f.X(24)))),
        ("sign-known-top", f => f.O(SignExtend, 64, f.T.Concat(f.X(24), f.C(0x80, 8)))),
        ("sign-known-top-zero", f => f.O(SignExtend, 64, f.T.Concat(f.X(24), f.C(0x7f, 8)))),
        ("select-constant", f => f.O(Select, 32, f.C(1, 1), f.X(), f.T.Undefined(32))),
        ("select-same", f => f.O(Select, 32, f.X(1, 1), f.X(), f.X())),
        ("select-bit", f => f.O(Select, 32, f.X(1), f.C(1), f.C(0))),
        ("select-inverted-bit", f => f.O(Select, 32, f.X(1), f.C(0), f.C(1))),
        ("bit-add", f => f.O(Add, 1, f.X(1), f.X(1, 1))),
        ("bit-subtract", f => f.O(Subtract, 1, f.X(1), f.X(1, 1))),
        ("bit-multiply", f => f.O(Multiply, 1, f.X(1), f.X(1, 1))),
        ("double-not", f => f.O(Not, 32, f.O(Not, 32, f.X()))),
        ("double-negate", f => f.O(Negate, 32, f.O(Negate, 32, f.X()))),
        ("not-equal", f => f.O(NotEqual, 1, f.X(), f.X(32, 1))),
        ("signed-nonstrict", f => f.O(SignedLessEqual, 1, f.X(), f.X(32, 1))),
        ("unsigned-nonstrict", f => f.O(UnsignedLessEqual, 1, f.X(), f.X(32, 1))),
        ("operand-order", f => { var x = f.X(); var y = f.X(32, 1); return f.O(Add, 32, y, x); }),
        ("xor-bit-one", f => f.O(Xor, 1, f.X(1), f.C(1, 1))),
        ("concat-undefined", f => f.T.Concat(f.T.Undefined(8), f.T.Undefined(24))),
        ("constant-order", f => f.O(Add, 32, f.C(7), f.X())),
        ("equal-complement-add", f => f.O(Equal, 1, f.O(Add, 32, f.X(), f.O(Not, 32, f.X(32, 1))), f.C(uint.MaxValue))),
        ("equal-bit-zero", f => f.O(Equal, 1, f.O(ZeroExtend, 32, f.X(1)), f.C(0))),
        ("equal-bit-one", f => f.O(Equal, 1, f.X(1), f.C(1, 1))),
        ("compare-zero-extends", f => f.O(SignedLess, 1, f.O(ZeroExtend, 64, f.X()), f.O(ZeroExtend, 64, f.X(32, 1)))),
        ("compare-sign-extends", f => f.O(SignedLess, 1, f.O(SignExtend, 64, f.X()), f.O(SignExtend, 64, f.X(32, 1)))),
        ("shift-left", f => f.O(ShiftLeft, 32, f.X(), f.C(9))),
        ("shift-right", f => f.O(LogicalShiftRight, 32, f.X(), f.C(9))),
        ("shift-signed", f => f.O(ArithmeticShiftRight, 32, f.X(), f.C(9))),
        ("rotate", f => f.O(RotateRight, 32, f.X(), f.C(39))),
        ("shift-zero", f => f.O(ShiftLeft, 32, f.X(), f.C(0))),
        ("shift-invalid", f => f.O(ShiftLeft, 32, f.X(), f.C(32))),
        ("subtract-constant", f => f.O(Subtract, 32, f.X(), f.C(7))),
        ("combine-add", f => f.O(Add, 32, f.O(Add, 32, f.X(), f.C(7)), f.C(9))),
        ("combine-and", f => f.O(And, 32, f.O(And, 32, f.X(), f.C(0xaaaaaaaa)), f.C(0x55555555))),
        ("combine-or", f => f.O(Or, 32, f.O(Or, 32, f.X(), f.C(7)), f.C(9))),
        ("combine-xor", f => f.O(Xor, 32, f.O(Xor, 32, f.X(), f.C(7)), f.C(9))),
        ("combine-multiply", f => f.O(Multiply, 32, f.O(Multiply, 32, f.X(), f.C(3)), f.C(7))),
        ("multiply-power", f => f.O(Multiply, 32, f.X(), f.C(8))),
        ("add-low-zeros", f => f.O(Add, 32, f.T.Concat(f.C(0, 16), f.X(16)), f.T.Concat(f.C(0, 16), f.X(16, 1)))),
        ("subtract-low-zeros", f => f.O(Subtract, 32, f.T.Concat(f.C(0, 16), f.X(16)), f.T.Concat(f.C(0, 16), f.X(16, 1)))),
        ("compare-constant-left", f => f.O(SignedLess, 1, f.C(7), f.X())),
        ("compare-constant-max", f => f.O(UnsignedLess, 1, f.C(uint.MaxValue), f.X())),
        ("add-zero", f => f.O(Add, 32, f.X(), f.C(0))),
        ("or-zero", f => f.O(Or, 32, f.X(), f.C(0))),
        ("xor-zero", f => f.O(Xor, 32, f.X(), f.C(0))),
        ("multiply-one", f => f.O(Multiply, 32, f.X(), f.C(1))),
        ("and-ones", f => f.O(And, 32, f.X(), f.C(uint.MaxValue))),
        ("and-zero", f => f.O(And, 32, f.X(), f.C(0))),
        ("multiply-zero", f => f.O(Multiply, 32, f.X(), f.C(0))),
        ("or-ones", f => f.O(Or, 32, f.X(), f.C(uint.MaxValue))),
        ("mask", f => f.O(And, 32, f.X(), f.C(0xff00ff))),
        ("insert", f => f.O(Or, 32, f.T.Concat(f.X(16), f.C(0, 16)), f.T.Concat(f.C(0, 16), f.X(16, 1)))),
        ("slice-full", f => f.T.Slice(f.X(), 0, 32)),
        ("slice-constant", f => f.T.Slice(f.C(0xabcdef), 3, 9)),
        ("slice-undefined", f => f.T.Slice(f.T.Undefined(32), 3, 9)),
        ("slice-slice", f => f.T.Slice(f.T.Slice(f.X(), 3, 20), 5, 9)),
        ("slice-concat", f => f.T.Slice(f.T.Concat(f.X(16), f.X(16, 1)), 5, 23)),
        ("slice-sign-low", f => f.T.Slice(f.O(SignExtend, 64, f.X()), 3, 12)),
        ("slice-sign-cross", f => f.T.Slice(f.O(SignExtend, 64, f.X()), 19, 32)),
        ("slice-sign-high", f => f.T.Slice(f.O(SignExtend, 64, f.X()), 40, 12)),
        ("slice-bitwise", f => f.T.Slice(f.O(Xor, 32, f.X(), f.X(32, 1)), 3, 12)),
        ("slice-low-arithmetic", f => f.T.Slice(f.O(Multiply, 32, f.X(), f.X(32, 1)), 0, 12)),
        ("slice-high-add", f => f.T.Slice(f.O(Add, 32, f.T.Concat(f.C(0, 16), f.X(16)), f.X(32, 1)), 16, 16)),
        ("slice-high-subtract", f => f.T.Slice(f.O(Subtract, 32, f.X(), f.T.Concat(f.C(0, 16), f.X(16, 1))), 16, 16)),
        ("slice-not", f => f.T.Slice(f.O(Not, 32, f.X()), 3, 12)),
        ("slice-negate", f => f.T.Slice(f.O(Negate, 32, f.X()), 0, 12)),
        ("slice-select", f => f.T.Slice(f.O(Select, 32, f.X(1, 2), f.X(), f.X(32, 1)), 3, 12)),
        ("concat-flat", f => f.T.Concat(f.T.Concat(f.X(8), f.X(8, 1)), f.X(8, 2))),
        ("concat-constants", f => f.T.Concat(f.C(7, 8), f.C(11, 8))),
        ("concat-adjacent", f => f.T.Concat(f.T.Slice(f.X(), 0, 11), f.T.Slice(f.X(), 11, 21))),
        ("concat-single", f => f.T.Concat(f.X()))
    ];

    private static readonly (string Name, Func<Fixture, Term> Before, Func<Fixture, Term> After)[] ReviewRules =
    [
        ("subtract-overflow-bit-sign", f =>
        {
            var x = f.O(And, 32, f.X(), f.X(32, 2)); var y = f.X(32, 1);
            var n = f.T.Slice(f.O(Subtract, 32, x, y), 31, 1);
            var a = f.T.Slice(x, 31, 1); var b = f.T.Slice(f.O(Not, 32, y), 31, 1);
            var v = f.O(And, 1, f.O(Equal, 1, a, b), f.O(NotEqual, 1, a, n));
            return f.O(Equal, 1, n, v);
        }, f => f.O(Not, 1, f.O(SignedLess, 1, f.O(And, 32, f.X(), f.X(32, 2)), f.X(32, 1)))),
        ("same-and", f => f.O(And, 32, f.X(), f.X()), f => f.X()),
        ("same-or", f => f.O(Or, 32, f.X(), f.X()), f => f.X()),
        ("same-xor", f => f.O(Xor, 32, f.X(), f.X()), f => f.C(0)),
        ("same-subtract", f => f.O(Subtract, 32, f.X(), f.X()), f => f.C(0)),
        ("same-equal", f => f.O(Equal, 1, f.X(), f.X()), f => f.C(1, 1)),
        ("same-signed", f => f.O(SignedLess, 1, f.X(), f.X()), f => f.C(0, 1)),
        ("same-unsigned", f => f.O(UnsignedLess, 1, f.X(), f.X()), f => f.C(0, 1)),
        ("unsigned-zero", f => f.O(UnsignedLess, 1, f.X(), f.C(0)), f => f.C(0, 1)),
        ("unsigned-one", f => f.O(UnsignedLess, 1, f.X(), f.C(1)), f => f.O(Equal, 1, f.X(), f.C(0))),
        ("signed-minimum", f => f.O(SignedLess, 1, f.X(), f.C(0x80000000)), f => f.C(0, 1)),
        ("xor-ones", f => f.O(Xor, 32, f.X(), f.C(uint.MaxValue)), f => f.O(Not, 32, f.X())),
        ("zero-subtract", f => f.O(Subtract, 32, f.C(0), f.X()), f => f.O(Negate, 32, f.X())),
        ("add-negate", f => f.O(Add, 32, f.X(), f.O(Negate, 32, f.X(32, 1))), f => f.O(Subtract, 32, f.X(), f.X(32, 1))),
        ("negate-add", f => f.O(Add, 32, f.O(Negate, 32, f.X(32, 1)), f.X()), f => f.O(Subtract, 32, f.X(), f.X(32, 1))),
        ("subtract-negate", f => f.O(Subtract, 32, f.X(), f.O(Negate, 32, f.X(32, 1))), f => f.O(Add, 32, f.X(), f.X(32, 1))),
        ("equal-subtract", f => f.O(Equal, 1, f.O(Subtract, 32, f.X(), f.X(32, 1)), f.C(0)), f => f.O(Equal, 1, f.X(), f.X(32, 1))),
        ("equal-xor", f => f.O(Equal, 1, f.O(Xor, 32, f.X(), f.X(32, 1)), f.C(0)), f => f.O(Equal, 1, f.X(), f.X(32, 1))),
        ("equal-complement-add", f => f.O(Equal, 1, f.O(Add, 32, f.X(), f.O(Not, 32, f.X(32, 1))), f.C(uint.MaxValue)), f => f.O(Equal, 1, f.X(), f.X(32, 1))),
        ("equal-add", f => f.O(Equal, 1, f.O(Add, 32, f.X(), f.C(7)), f.C(3)), f => f.O(Equal, 1, f.X(), f.C(uint.MaxValue - 3))),
        ("undefined-mask", f => f.O(And, 64, f.T.Concat(f.X(8), f.T.Undefined(56)), f.C(255, 64)), f => f.T.Concat(f.X(8), f.C(0, 56))),
        ("undefined-low-add", f => f.T.Slice(f.O(Add, 64, f.T.Concat(f.X(), f.T.Undefined(32)), f.C(0x123456789, 64)), 0, 32), f => f.O(Add, 32, f.X(), f.C(0x23456789))),
        ("undefined-operation", f => f.O(Add, 32, f.X(), f.T.Undefined(32)), f => f.T.Undefined(32)),
        ("undefined-and-zero", f => f.O(And, 32, f.T.Undefined(32), f.C(0)), f => f.C(0)),
        ("undefined-multiply-zero", f => f.O(Multiply, 32, f.T.Undefined(32), f.C(0)), f => f.C(0)),
        ("undefined-or-ones", f => f.O(Or, 32, f.T.Undefined(32), f.C(uint.MaxValue)), f => f.C(uint.MaxValue)),
        ("undefined-select", f => f.O(Select, 32, f.T.Undefined(1), f.X(), f.X()), f => f.X()),
        ("undefined-slice", f => f.T.Slice(f.T.Concat(f.X(), f.T.Undefined(32)), 0, 32), f => f.X())
    ];

    public static int Run()
    {
        var assertions = new Assertions();
        var random = new Random(Seed);
        var timer = Stopwatch.StartNew();
        foreach (var (name, build) in Rules)
        {
            var raw = build(new());
            var table = new TermTable();
            // 项内次序由本表驻留顺序确定；先登记较小操作数，才能观测交换规则。
            if (name == "operand-order") Copy(raw.Operands[1], table);
            var normalized = Copy(raw, table);
            assertions.True(Shape(raw) != Shape(normalized), $"规则未触发 {name}");
            Check(assertions, random, raw, normalized, name, 96);
            assertions.True(ReferenceEquals(normalized, Copy(normalized, normalized.Table)), $"幂等 {name}");
            for (var variant = 0; variant < 6; variant++)
            {
                var varied = build(new(false, random.Next(1, int.MaxValue)));
                var result = Copy(varied, new());
                Check(assertions, random, varied, result, $"{name}/variant={variant}", 16);
                assertions.True(ReferenceEquals(result, Copy(result, result.Table)), $"变体幂等 {name}/{variant}");
            }
        }
        foreach (var (name, before, after) in ReviewRules)
        {
            var raw = before(new());
            var normalized = Copy(raw, new());
            assertions.True(Shape(raw) != Shape(normalized), "规则未触发 " + name);
            Check(assertions, random, raw, normalized, name, 96);
            assertions.True(ReferenceEquals(normalized, Copy(normalized, normalized.Table)), "幂等 " + name);
            var fixture = new Fixture(true);
            assertions.True(ReferenceEquals(before(fixture), after(fixture)), "同实例 " + name);
            for (var variant = 0; variant < 6; variant++)
            {
                var varied = before(new(false, random.Next(1, int.MaxValue)));
                var result = Copy(varied, new());
                Check(assertions, random, varied, result, name + "/variant=" + variant, 16);
                assertions.True(ReferenceEquals(result, Copy(result, result.Table)), "变体幂等 " + name);
            }
        }
        SubtractionFlags(assertions);
        StrictDomains(assertions);
        Pairs(assertions);
        Scale(assertions);
        var deepTimer = Stopwatch.StartNew();
        const int count = 600;
        long normalizeTicks = 0;
        for (var i = 0; i < count; i++)
        {
            var fixture = new Fixture();
            var raw = Generate(fixture, random, 7, new[] { 1, 8, 16, 32, 65 }[i % 5]);
            var started = Stopwatch.GetTimestamp();
            var normalized = Copy(raw, new());
            normalizeTicks += Stopwatch.GetTimestamp() - started;
            Check(assertions, random, raw, normalized, $"deep/{i}", 8);
            assertions.True(ReferenceEquals(normalized, Copy(normalized, normalized.Table)), $"幂等 deep/{i}");
        }
        deepTimer.Stop();
        var bench = new Fixture(true);
        var x = bench.X(); var c = bench.C(7);
        var add = new CoreOperator(Add);
        const int requests = 200000;
        for (var i = 0; i < 20000; i++) bench.T.Apply(add, 32, x, c);
        var micro = Stopwatch.StartNew();
        var allocated = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < requests; i++) bench.T.Apply(add, 32, x, c);
        allocated = GC.GetAllocatedBytesForCurrentThread() - allocated;
        micro.Stop();
        assertions.True(allocated == 0, $"常见驻留入口不分配：{allocated} bytes");
        Console.WriteLine($"规范化：seed={Seed}，规则={Rules.Length + ReviewRules.Length}，常见驻留入口={micro.Elapsed.TotalNanoseconds / requests:F0} ns/项，分配={allocated} bytes，深项仅规范化={count * (double)Stopwatch.Frequency / normalizeTicks:F0} 项/秒，深项构造+规范化+8次求值={count / deepTimer.Elapsed.TotalSeconds:F0} 项/秒，总耗时={timer.Elapsed.TotalSeconds:F2}s");
        const int freshCount = 20000;
        var fresh = new Fixture(true);
        var left = fresh.X();
        var rights = Enumerable.Range(1, freshCount).Select(i => fresh.X(32, i)).ToArray();
        micro.Restart();
        for (var i = 0; i < freshCount; i++) fresh.T.Apply(add, 32, left, rights[i]);
        micro.Stop();
        Console.WriteLine($"无规则二元新项：{micro.Elapsed.TotalNanoseconds / freshCount:F0} ns/项（包含驻留存储）");
        var rawBench = new Fixture();
        left = rawBench.X();
        rights = Enumerable.Range(1, freshCount).Select(i => rawBench.X(32, i)).ToArray();
        micro.Restart();
        for (var i = 0; i < freshCount; i++) rawBench.T.Apply(add, 32, left, rights[i]);
        micro.Stop();
        Console.WriteLine($"关闭规范化的新项存储基线：{micro.Elapsed.TotalNanoseconds / freshCount:F0} ns/项");
        return assertions.Finish("项规范化");
    }

    private static void SubtractionFlags(Assertions checks)
    {
        for (int width = 1; width <= 4; width++)
        {
            var f = new Fixture(); var x = f.X(width); var y = f.X(width, 1);
            var full = f.O(Add, width + 1, f.O(Add, width + 1, f.O(ZeroExtend, width + 1, x),
                f.O(ZeroExtend, width + 1, f.O(Not, width, y))), f.C(1, width + 1));
            var carry = f.T.Slice(full, width, 1);
            var zero = width == 1 ? f.O(Equal, 1, x, y) : f.O(Equal, 1, f.T.Slice(full, 0, width), f.C(0, width));
            var hi = f.O(And, 1, carry, f.O(Not, 1, zero));
            var result = f.T.Slice(full, 0, width);
            var signA = f.T.Slice(x, width - 1, 1);
            var signB = f.T.Slice(f.O(Not, width, y), width - 1, 1);
            var negative = f.T.Slice(result, width - 1, 1);
            var overflow = f.O(And, 1, f.O(Equal, 1, signA, signB), f.O(NotEqual, 1, signA, negative));
            var ge = f.O(Equal, 1, negative, overflow);
            var signedGt = f.O(And, 1, ge, f.O(Not, 1, zero));
            var expressions = new[] { carry, f.O(Not, 1, carry), hi, f.O(Not, 1, hi),
                ge, f.O(Not, 1, ge), signedGt, f.O(Not, 1, signedGt) };
            var table = new TermTable();
            var normalized = expressions.Select(e => Copy(e, table)).ToArray();
            var nx = Copy(x, table); var ny = Copy(y, table);
            var lt = table.Apply(new CoreOperator(UnsignedLess), 1, nx, ny);
            var gt = table.Apply(new CoreOperator(UnsignedLess), 1, ny, nx);
            checks.True(normalized[0] == table.Apply(new CoreOperator(Not), 1, lt) && normalized[1] == lt,
                $"{width} 位无借位与借位规范为无符号比较");
            checks.True(normalized[2] == gt && normalized[3] == table.Apply(new CoreOperator(Not), 1, gt),
                $"{width} 位 hi/ls 规范为严格比较及取反");
            if (width > 1)
            {
                var signedLt = table.Apply(new CoreOperator(SignedLess), 1, nx, ny);
                var signedGreater = table.Apply(new CoreOperator(SignedLess), 1, ny, nx);
                checks.True(normalized[4] == table.Apply(new CoreOperator(Not), 1, signedLt) && normalized[5] == signedLt,
                    $"{width} 位溢出与符号组合规范为有符号比较");
                checks.True(normalized[6] == signedGreater && normalized[7] == table.Apply(new CoreOperator(Not), 1, signedGreater),
                    $"{width} 位 gt/le 规范为严格有符号比较及取反");
            }
            var borrowed = f.T.Slice(f.O(Add, width + 1, full.Operands[0], f.C(0, width + 1)), width, 1);
            var borrowedNormalized = Copy(borrowed, new());
            checks.True(borrowedNormalized.Kind == TermKind.Slice, $"{width} 位 +0 不误匹配为无借位减法");
            for (int a = 0; a < 1 << width; a++)
            for (int b = 0; b < 1 << width; b++)
            {
                var evaluator = new TermEvaluator(id => id == x.Identity ? a : b);
                for (int i = 0; i < expressions.Length; i++)
                    checks.True(evaluator.Evaluate(expressions[i]) == evaluator.Evaluate(normalized[i]),
                        $"{width} 位进借位组合 {i} 穷举 {a},{b}");
                checks.True(evaluator.Evaluate(f.T.Slice(full, 0, width)) == evaluator.Evaluate(Copy(f.T.Slice(full, 0, width), new())),
                    $"{width} 位模减法结果穷举 {a},{b}");
                checks.True(evaluator.Evaluate(borrowed) == evaluator.Evaluate(borrowedNormalized),
                    $"{width} 位带借位输入穷举 {a},{b}");
            }
        }
    }

    private static void Check(Assertions assertions, Random random, Term raw, Term normalized, string label, int samples)
    {
        var atoms = new Dictionary<AtomIdentity, int>();
        void Collect(Term t) { if (t.Identity is { } id) atoms[id] = t.Width; foreach (var p in t.Operands) Collect(p); }
        Collect(raw);
        for (var sample = 0; sample < samples; sample++)
        {
            var values = atoms.ToDictionary(p => p.Key, p => RandomBits(random, p.Value, sample));
            var evaluator = new TermEvaluator(id => values[id], unknowns: _ => 0);
            var before = evaluator.Evaluate(raw); var after = evaluator.Evaluate(normalized);
            var same = TermEvaluator.Refines(before, after, raw.Width);
            assertions.True(same, $"seed={Seed} {label} sample={sample} inputs={string.Join(';', values.Select(p => $"{p.Key.StableText}={p.Value:x}"))} before={before} after={after}" + (same ? "" : $" raw={Shape(raw)} normalized={Shape(normalized)}"));
            if (!same) break;
        }
    }
    internal static BigInteger RandomBits(Random random, int width, int index)
    {
        var mask = (BigInteger.One << width) - 1;
        return (index % 13) switch
        {
            0 => BigInteger.Zero, 1 => mask, 2 => BigInteger.One << (width - 1), 3 => mask >> 1, 4 => BigInteger.One,
            _ => new BigInteger(RandomBytes(random, (width + 7) / 8), true) & mask
        };
    }
    private static byte[] RandomBytes(Random random, int length) { var bytes = new byte[length]; random.NextBytes(bytes); return bytes; }
    private static Term Generate(Fixture f, Random random, int depth, int width)
    {
        if (depth == 0) return random.Next(4) switch
        {
            0 => f.C(RandomBits(random, width, random.Next(100)), width),
            1 => f.T.Undefined(width),
            _ => f.X(width, width * 10 + random.Next(3))
        };
        Term Child(int w) => Generate(f, random, depth - 1, w);
        return random.Next(10) switch
        {
            0 => f.T.Slice(Child(width + 7), 3, width),
            1 when width > 1 => f.T.Concat(Child(width / 2), Child(width - width / 2)),
            2 => f.O(Select, width, Child(1), Child(width), Child(width)),
            3 => f.T.Slice(f.O(SignExtend, width + 1, Child(width)), 1, width),
            4 => f.O(UnsignedDivide, width, Child(width), Child(width)),
            5 => f.O(ShiftLeft, width, Child(width), f.C(random.Next(width + 1), width)),
            6 => f.O(Not, width, Child(width)),
            _ => f.O(new[] { Add, Subtract, Multiply, And, Or, Xor }[random.Next(6)], width, Child(width), Child(width))
        };
    }
    private static void StrictDomains(Assertions a)
    {
        var f = new Fixture(true);
        var x = f.X(8);
        var u = f.T.Concat(x, f.T.Undefined(56));
        var low = f.T.Slice(u, 0, 8);
        var zeroExtended = f.T.Concat(x, f.C(0, 56));
        a.True(ReferenceEquals(low, x), "undefined-low-slice");
        a.True(ReferenceEquals(f.O(ZeroExtend, 64, low), zeroExtended), "undefined-low-extend");
        a.True(ReferenceEquals(f.O(And, 64, u, f.C(255, 64)), zeroExtended), "undefined-mask");
        var y = f.X(32, 1);
        var sum = f.O(Add, 64, f.T.Concat(y, f.T.Undefined(32)), f.C(0x123456789, 64));
        a.True(ReferenceEquals(f.T.Slice(sum, 0, 32), f.O(Add, 32, y, f.C(0x23456789))), "undefined-low-add");
        a.True(ReferenceEquals(f.O(And, 64, u, u), u), "undefined-same-and");
        foreach (var op in new[] { Xor, Subtract, Equal })
            a.True(f.O(op, op == Equal ? 1 : 64, u, u).Kind != TermKind.Constant, "undefined-same-" + op);
        a.True(f.O(Add, 32, y, f.T.Undefined(32)).Kind == TermKind.Undefined, "undefined-operation");
        foreach (var op in new[] { And, Multiply })
            a.True(f.O(op, 32, f.T.Undefined(32), f.C(0)).ConstantValue == 0, "undefined-zero-" + op);
        a.True(f.O(Or, 32, f.T.Undefined(32), f.C(uint.MaxValue)).ConstantValue == uint.MaxValue, "undefined-ones");
        a.True(ReferenceEquals(f.O(Select, 32, f.T.Undefined(1), y, y), y), "undefined-select-same");
    }

    private static void Scale(Assertions a)
    {
        var f = new Fixture(true);
        var p = f.X(64);
        var watch = Stopwatch.StartNew();
        for (var i = 0; i < 64; i++)
        {
            p = f.O(Add, 64, f.O(Xor, 64, p, f.O(LogicalShiftRight, 64, p, f.C(7, 64))),
                f.O(ShiftLeft, 64, p, f.C(3, 64)));
            f.T.Slice(p, 0, 32);
            f.T.Slice(p, 0, 8);
        }
        watch.Stop();
        a.True(watch.Elapsed.TotalSeconds < 1, "64 层共享图取片小于一秒");
        Console.WriteLine($"共享图 64 层：{watch.Elapsed.TotalMilliseconds:F2} ms");
        f = new Fixture(true);
        p = f.X(64);
        var y = f.X(64, 1);
        for (var i = 0; i < 2000; i++) p = f.O(Add, 64, p, y);
        watch.Restart();
        var low = f.T.Slice(p, 0, 32);
        watch.Stop();
        a.True(low.Width == 32 && ReferenceEquals(low, f.T.Slice(p, 0, 32)), "2000 层加法链取片");
        Console.WriteLine($"加法链 2000 层取片：{watch.Elapsed.TotalMilliseconds:F2} ms");
    }
    private static void Pairs(Assertions a)
    {
        var f = new Fixture(true); var x = f.X(); var y = f.X(32, 1); var bit = f.X(1, 2);
        (string Name, Term A, Term B)[] pairs =
        [
            ("x+0=x", f.O(Add, 32, x, f.C(0)), x),
            ("x+y=y+x", f.O(Add, 32, x, y), f.O(Add, 32, y, x)),
            ("x-7=x+(-7)", f.O(Subtract, 32, x, f.C(7)), f.O(Add, 32, x, f.C(uint.MaxValue - 6))),
            ("zext=concat", f.O(ZeroExtend, 64, x), f.T.Concat(x, f.C(0))),
            ("shift=concat-slice", f.O(ShiftLeft, 32, x, f.C(8)), f.T.Concat(f.C(0, 8), f.T.Slice(x, 0, 24))),
            ("bit==1=bit", f.O(Equal, 1, bit, f.C(1, 1)), bit),
            ("select10=zext", f.O(Select, 32, bit, f.C(1), f.C(0)), f.O(ZeroExtend, 32, bit)),
            ("le=not-swapped-lt", f.O(SignedLessEqual, 1, x, y), f.O(Not, 1, f.O(SignedLess, 1, y, x))),
            ("adjacent=whole", f.T.Concat(f.T.Slice(x, 0, 7), f.T.Slice(x, 7, 25)), x)
        ];
        foreach (var pair in pairs) a.True(ReferenceEquals(pair.A, pair.B), pair.Name);
    }
}
