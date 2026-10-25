using System.Buffers.Binary;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Ssa;

namespace Cpp2CS.Lifting;

/// <summary>一个函数的机器层提升结果：寄存器 SSA 形式的控制流图，以及构建过程中的问题。</summary>
public sealed record LiftedFunction(MachineFunction Function, IReadOnlyList<string> Errors)
{
    public bool Succeeded => Errors.Count == 0;
}

/// <summary>
/// 单个函数的机器层提升：CFG → 寄存器 SSA → 传播 ⇄ 常量内存折叠。
/// 常量内存：.got 项（只经重定位写入，加载后由 RELRO 设为只读）读出的是重定位目标；
/// 不可写、不可执行、无重定位的节（.rodata 等）读出的是文件中的字节。
/// 实例不是线程安全的（CFG 构建器缓存不返回判定），并行时每个线程各用一个。
/// </summary>
public sealed class FunctionLifter
{
    private readonly ProgramFacts facts;
    private readonly CfgBuilder cfg;
    private readonly ICallModel calls;
    private readonly ImageSection? got;
    private readonly ImageSection[] constant;

    public FunctionLifter(ProgramFacts facts, ICallModel? calls = null)
    {
        this.facts = facts;
        Machine = new Arm64Machine(facts.Code);
        cfg = new CfgBuilder(Machine, facts.Code);
        this.calls = calls ?? new FactsCallModel(facts, Machine.Convention);
        var image = facts.Model.Image;
        got = image.Section(".got");
        constant = image.Sections.Where(s => (s.Flags & 1) == 0 && !s.Executable && s.Type == 1 /* SHT_PROGBITS */ && s.Name != ".got").ToArray();
    }

    /// <summary>是否做帧槽提升（默认是）；环境变量 CPP2CS_FRAME_SLOTS=off 时关闭，用于对比与排查。</summary>
    public static bool PromoteFrameSlots { get; } = Environment.GetEnvironmentVariable("CPP2CS_FRAME_SLOTS") != "off";

    public Arm64Machine Machine { get; }
    public ICallModel Calls => calls;
    public NoReturnOracle NoReturn => cfg.NoReturn;

    /// <summary>returnValue 为函数自身返回值所在的寄存器读取（按签名）；为 null 时返回语句不读取任何值，返回值的计算会作为死定义删去。</summary>
    public LiftedFunction Lift(ulong entry, Expr? returnValue = null, bool simplify = true)
    {
        var function = cfg.Build(entry);
        var dominators = Dominators.Compute(function);
        SsaBuilder.PrepareCalls(function, calls, returnValue);
        SsaBuilder.Build(function, dominators, s => s.Bank is Bank.Gpr or Bank.Vec or Bank.Flags or Bank.Temp, calls, Machine.Convention.StackPointer);
        var errors = SsaCheck.Verify(function, dominators);
        if (errors.Count > 0) return new(function, errors.Select(e => "构建: " + e).ToList());
        // 参数使用证明需要原始 SSA，不能先删除未使用的读取或简化分支。
        if (!simplify) return new(function, errors);
        do Propagate.Run(function, dominators);
        while (FoldConstantMemory(function));
        // 帧槽提升：不逃逸的标量栈槽成为存储单元，只对栈槽再构建一次 SSA（FrameSlotPromotion 的条件）。
        if (PromoteFrameSlots && FrameSlotPromotion.Run(function) > 0)
        {
            SsaBuilder.Build(function, dominators, s => s.Bank == Bank.Stack, calls, Machine.Convention.StackPointer);
            do Propagate.Run(function, dominators);
            while (FoldConstantMemory(function));
        }
        return new(function, SsaCheck.Verify(function, dominators));
    }

    /// <summary>常量地址上的读取若来自常量内存则替换为常量。返回是否有替换。</summary>
    private bool FoldConstantMemory(MachineFunction function)
    {
        var changed = false;
        Expr? Fold1(Expr e)
        {
            if (e is not Load { Address: Const address } load || ConstantAt(address.Value, load.Width) is not { } value) return null;
            changed = true;
            return Expr.C(value, load.Width);
        }
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var stmt = block.Statements[i];
                if (!ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).Any(e => e is Load { Address: Const })) continue;
                block.Statements[i] = ExprMap.MapOperands(stmt, e => Ir.Fold.Simplify(ExprMap.Map(e, Fold1)));
            }
        return changed;
    }

    /// <summary>常量内存 address 处 width 位的值；不是常量内存返回 null。</summary>
    public ulong? ConstantAt(ulong address, int width)
    {
        var image = facts.Model.Image;
        if (got is not null && got.Contains(address))
            return width == 64 && (address & 7) == 0 ? image.RelocatedPointer(address) : null;
        if (width is not (8 or 16 or 32 or 64)) return null;
        foreach (var section in constant)
        {
            if (!section.Contains(address) || address + (ulong)(width / 8) > section.Address + section.Size) continue;
            for (var a = address & ~7UL; a < address + (ulong)(width / 8); a += 8)
                if (image.RelocatedPointer(a) is not null) return null;
            var bytes = image.ReadUpTo(address, width / 8);
            if (bytes.Length != width / 8) return null;
            return width switch
            {
                8 => bytes[0],
                16 => BinaryPrimitives.ReadUInt16LittleEndian(bytes),
                32 => BinaryPrimitives.ReadUInt32LittleEndian(bytes),
                _ => BinaryPrimitives.ReadUInt64LittleEndian(bytes),
            };
        }
        return null;
    }
}
