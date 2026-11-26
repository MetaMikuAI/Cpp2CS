using Cpp2CS.Snapshot;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// 前端接口的示例：语料用例 Corpus.Fields::ReadInstance 在 ARM64 上的原生代码，按 docs/前端.md 的约定逐条指令抄写。
///
///     str  x30, [sp, #-0x10]!
///     cbz  x0, raise
///     ldr  w0, [x0, #0x10]
///     ldr  x30, [sp], #0x10
///     ret
///   raise:
///     bl   il2cpp_codegen_raise_null_reference_exception
/// </summary>
internal static class SnapshotExample
{
    public static MethodSnapshot Build()
    {
        var snapshot = new SnapshotBuilder(pointerBits: 64);
        var terms = snapshot.Terms;
        var integer0 = new Slot(SlotKind.Integer, 0);
        var stack = new Slot(SlotKind.StackPointer, 0);
        var link = new Slot(SlotKind.ReturnAddress, 0);

        // 入口：用到的槽位各声明一次。
        Term x0 = snapshot.EntryParameter(integer0, 64);
        Term sp = snapshot.EntryParameter(stack, 64);
        Term x30 = snapshot.EntryParameter(link, 64);
        // 返回出口上列出：返回值、实际返回到的地址、栈指针。
        snapshot.SetReturnSlots((integer0, 64), (link, 64), (stack, 64));

        // 块只用自己的参数：load 需要 x0 与帧地址，由边传入。
        BlockId load = snapshot.Block(64, 64);
        BlockId raise = snapshot.Block(64);

        // str x30, [sp, #-0x10]!
        Term frame = terms.Add(sp, terms.Constant(-0x10, 64));
        snapshot.Write(snapshot.Entry, frame, x30, 0x4ce668);
        // cbz x0, raise
        snapshot.Terminate(snapshot.Entry, Terminator.Branch(terms.Eq(x0, terms.Zero(64)),
            Exit.To(raise, frame), Exit.To(load, x0, frame), 0x4ce66c));

        // ldr w0, [x0, #0x10]：写 w0 把 x0 的高 32 位清零。
        Term value = snapshot.Read(load, terms.Add(snapshot.Parameter(load, 0), terms.Constant(0x10, 64)), 32, 0x4ce670);
        // ldr x30, [sp], #0x10
        Term restored = snapshot.Read(load, snapshot.Parameter(load, 1), 64, 0x4ce674);
        // ret
        snapshot.Return(load, terms.ZeroExtend(value, 64), restored, terms.Add(snapshot.Parameter(load, 1), terms.Constant(0x10, 64)));

        // bl il2cpp_codegen_raise_null_reference_exception：其后没有指令，是不返回的调用。实参槽里此刻没有前端已知的值，不列。
        snapshot.Call(raise, terms.Constant(0x448408, 64), [(stack, snapshot.Parameter(raise, 0))], [], 0x4ce67c);
        snapshot.Terminate(raise, Terminator.Single(Exit.NoReturn, 0x4ce67c));
        return snapshot.Build();
    }

    public static int Run()
    {
        var first = Build();
        var second = Build();
        int occurrences = first.Blocks.Sum(b => b.Occurrences.Length);
        Console.WriteLine($"快照示例：块 {first.BlockCount} 个，出现 {occurrences} 个，摘要 {first.DigestText[..16]}…，" +
            $"两次构造摘要{(first.DigestText == second.DigestText ? "相同" : "不同")}");
        Console.WriteLine($"  返回前的内存版本 {first.VersionAtExit(new BlockId(1))}，抛出块里调用之后的内存版本 {first.VersionAtExit(new BlockId(2))}");
        return first.DigestText == second.DigestText ? 0 : 1;
    }
}
