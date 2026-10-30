using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Idioms;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class ReadOnlyDataCheck
{
    [Command("readonly-data", "只读表的实际重定位与索引边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var image = facts.Model.Image;
        bool Slot(ulong pointer) => facts.Usages.At(pointer)?.Usage.Kind == UsageKind.StringLiteral;
        var table = image.RelocatedPointers.Select(p => p.Key).First(address => (address & 7) == 0
            && image.SectionAt(address) is { Executable: false } section && section.Contains(address + 23)
            && ((section.Flags & 1) == 0 || image.RelroRanges.Any(r => address >= r.Address && address + 24 <= r.Address + r.Size))
            && Enumerable.Range(0, 3).All(i => image.RelocatedPointer(address + (ulong)i * 8) is { } pointer && Slot(pointer)));
        var input = new Variable(Storage.Gpr(0), 0);
        var checkedIndex = new Variable(Storage.Gpr(8), 1);
        var output = new Variable(Storage.Gpr(0), 1);
        Expr Index(ulong delta = 1) => new Binary(BinOp.Add, new Use(input, 32), Expr.C(delta, 32), 32);
        MachineFunction Sample(Cond condition = Cond.Uge, ulong delta = 1, bool bypass = false, bool snapshot = false, bool wide = false,
            bool ssa = false, bool loaded = false, ConvKind extension = ConvKind.ZeroExtend)
        {
            var entry = new Block(0x1000) { Statements =
            [new Define(0x1000, checkedIndex, snapshot ? new Load(Expr.C(0x100, 64), 64)
                : new Cpp2CS.Ir.Convert(extension, loaded ? new Load(new Use(input, 64), 32) : Index(), 64)),
             new Branch(0x1004, new Compare(condition, new Use(checkedIndex, wide ? 64 : 32), Expr.C(3, wide ? 64 : 32)), 0x1020, 0x1010)] };
            var load = new Block(0x1010) { Statements = [new Define(0x1010, output, new Load(new Binary(BinOp.Add,
                new Binary(BinOp.Shl, ssa ? new Use(checkedIndex, 64) : new Cpp2CS.Ir.Convert(ConvKind.SignExtend, Index(delta), 64), Expr.C(3, 64), 64), Expr.C(table, 64), 64), 64)),
                new Return(0x1014) { Value = new Use(output, 64) }] };
            var exit = new Block(0x1020) { Statements = [bypass ? new Jump(0x1020, load.Start) : new Return(0x1020)] };
            MachineFunction.AddEdge(entry, exit); MachineFunction.AddEdge(entry, load);
            if (bypass) MachineFunction.AddEdge(exit, load);
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x1000, 0x1024, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [entry, load, exit] };
            function.Renumber();
            return function;
        }
        var a = new Assertions();
        var valid = Sample();
        a.True(ReadOnlyDataNormalizer.Run(valid, image, Slot), "窄读取的 SSA 定义与同宽算术索引对应同一上界");
        var expression = valid.Blocks.SelectMany(b => b.Statements).OfType<Define>().Single(d => d.Target == output).Value;
        for (var i = 0; i < 3; i++)
        {
            var value = Fold.Simplify(ExprMap.Map(expression, e => e is Use use && use.Variable == input ? Expr.C(unchecked((uint)(i - 1)), use.Width) : null));
            a.Equal<Expr>(Expr.C(image.RelocatedPointer(table + (ulong)i * 8)!.Value, 64), value, "选择结果与独立读取的实际重定位一致");
        }
        a.True(!ReadOnlyDataNormalizer.Run(Sample(delta: 2), image, Slot), "不同起点不共用上界");
        a.True(!ReadOnlyDataNormalizer.Run(Sample(condition: Cond.Sge), image, Slot), "有符号上界不能排除负索引");
        a.True(!ReadOnlyDataNormalizer.Run(Sample(bypass: true), image, Slot), "能绕过检查的入口不能展开表");
        a.True(!ReadOnlyDataNormalizer.Run(Sample(snapshot: true), image, Slot), "内存快照不等同于索引表达式");
        a.True(!ReadOnlyDataNormalizer.Run(Sample(wide: true), image, Slot), "不同位宽的条件不直接视为同一索引");
        a.True(!ReadOnlyDataNormalizer.Run(Sample(), image, _ => false), "未知重定位目标不当作元数据槽");
        foreach (var extension in new[] { ConvKind.SignExtend, ConvKind.ZeroExtend })
        {
            var loaded = Sample(ssa: true, loaded: true, extension: extension);
            a.True(ReadOnlyDataNormalizer.Run(loaded, image, Slot), "扩展后的地址索引与已检查的低位属于同一 SSA 快照");
            var selected = loaded.Blocks[1].Statements.OfType<Define>().Single().Value;
            for (var i = 0; i < 3; i++)
                a.Equal<Expr>(Expr.C(image.RelocatedPointer(table + (ulong)i * 8)!.Value, 64),
                    Fold.Simplify(ExprMap.Map(selected, e => e is Use use && use.Variable == checkedIndex ? Expr.C((ulong)i, use.Width) : null)),
                    "窄索引选择与原始表项一致");
        }
        a.True(!ReadOnlyDataNormalizer.Run(Sample(ssa: true, snapshot: true), image, Slot), "只检查低位不能约束任意 64 位加载的高位");
        a.True(!ReadOnlyDataNormalizer.Run(Sample(ssa: true, loaded: true, condition: Cond.Sge), image, Slot), "扩展来源不能代替无符号范围检查");
        a.True(!ReadOnlyDataNormalizer.Run(Sample(ssa: true, loaded: true, bypass: true), image, Slot), "索引快照一致仍不能绕过范围检查");
        return a.Finish("readonly-data");
    }
}
