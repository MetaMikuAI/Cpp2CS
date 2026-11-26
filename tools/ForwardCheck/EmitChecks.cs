using System.Collections.Immutable;
using System.Reflection;
using System.Reflection.Emit;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Spec.IL;

namespace Cpp2CS.Tools.ForwardCheck;

internal static class EmitChecks
{
    /// <summary>短形式归一。标号只表示指令间的位置，转移以目标指令在序列里的下标对照。</summary>
    public static void Instructions(ManagedBody body, ImmutableArray<Instruction> decoded, ITokenResolver tokens)
    {
        var labels = new Dictionary<int, int>();
        var expected = new List<ManagedInstruction>();
        foreach (var input in body.Instructions)
        {
            if (input.Opcode == ".label") labels.Add((int)input.Operand, expected.Count);
            else expected.Add(input);
        }
        if (decoded.Length != expected.Count) throw new InvalidDataException("回读的指令数不同");
        for (int i = 0; i < decoded.Length; i++)
        {
            var a = expected[i];
            var b = decoded[i];
            if (a.Opcode != b.Opcode.Canonical) throw new InvalidDataException($"偏移 {b.Offset} 的指令不同");
            bool same = b.Opcode.Operand switch
            {
                OperandKind.Method => tokens.Method((int)b.Operand) == a.Entity,
                OperandKind.Field => tokens.Field((int)b.Operand) == a.Entity,
                OperandKind.Type => tokens.Type((int)b.Operand) == a.Entity,
                OperandKind.Branch8 or OperandKind.Branch32 => b.Operand == decoded[labels[a.Target]].Offset,
                _ => a.Operand == b.Operand,
            };
            if (!same) throw new InvalidDataException($"偏移 {b.Offset} 的 {a.Opcode} 操作数不同");
        }
    }

    private static readonly Dictionary<ushort, OpCode> runtimeOpcodes = typeof(OpCodes).GetFields(BindingFlags.Static | BindingFlags.Public)
        .Where(f => f.FieldType == typeof(OpCode)).Select(f => (OpCode)f.GetValue(null)!).ToDictionary(op => unchecked((ushort)op.Value));

    /// <summary>回读用 CLR 指令表的栈效果和副本内记号解析出的签名，按实际字节偏移传播。</summary>
    public static int Stack(ImmutableArray<Instruction> decoded, ITokenResolver tokens, IMetadataView metadata, MethodShape host, int header)
    {
        var code = decoded.ToDictionary(i => i.Offset);
        var heights = new Dictionary<int, int>();
        var pending = new Stack<(int Offset, int Depth)>();
        pending.Push((0, 0));
        int peak = 0;
        while (pending.TryPop(out var point))
        {
            var (offset, depth) = point;
            if (!heights.TryAdd(offset, depth))
            {
                if (heights[offset] != depth) throw new InvalidDataException($"IL_{offset:x4} 入边栈深不同");
                continue;
            }
            if (!code.TryGetValue(offset, out var i)) throw new InvalidDataException($"无效的后继 IL_{offset:x4}");
            var op = runtimeOpcodes[i.Opcode.Code];
            int pop, push;
            if (op == OpCodes.Call || op == OpCodes.Callvirt || op == OpCodes.Newobj)
            {
                var callee = metadata.Method(tokens.Method((int)i.Operand));
                pop = callee.Parameters.Length - (op == OpCodes.Newobj ? 1 : 0);
                push = op == OpCodes.Newobj || callee.Return != null ? 1 : 0;
            }
            else
            {
                pop = op == OpCodes.Ret ? (host.Return == null ? 0 : 1) : Count(op.StackBehaviourPop);
                push = Count(op.StackBehaviourPush);
            }
            if (depth < pop) throw new InvalidDataException($"IL_{offset:x4} 栈下溢");
            int after = depth - pop + push;
            peak = Math.Max(peak, after);
            if (op == OpCodes.Ret && after != 0) throw new InvalidDataException($"IL_{offset:x4} 返回时栈非空");
            if (op.FlowControl is FlowControl.Branch or FlowControl.Cond_Branch) pending.Push(((int)i.Operand, after));
            if (op.FlowControl is not (FlowControl.Branch or FlowControl.Return or FlowControl.Throw)) pending.Push((i.Next, after));
        }
        if (heights.Count != decoded.Length || peak != header)
            throw new InvalidDataException($"已核对 {heights.Count}/{decoded.Length} 条指令，栈深峰值 {peak}，头中为 {header}");
        return peak;
    }

    private static int Count(StackBehaviour effect) => effect switch
    {
        StackBehaviour.Pop0 or StackBehaviour.Push0 => 0,
        StackBehaviour.Pop1 or StackBehaviour.Popi or StackBehaviour.Popref or StackBehaviour.Push1 or StackBehaviour.Pushi
            or StackBehaviour.Pushi8 or StackBehaviour.Pushr4 or StackBehaviour.Pushr8 or StackBehaviour.Pushref => 1,
        StackBehaviour.Pop1_pop1 or StackBehaviour.Popi_pop1 or StackBehaviour.Popi_popi or StackBehaviour.Popi_popi8
            or StackBehaviour.Popi_popr4 or StackBehaviour.Popi_popr8 or StackBehaviour.Popref_pop1 or StackBehaviour.Popref_popi
            or StackBehaviour.Push1_push1 => 2,
        StackBehaviour.Popi_popi_popi or StackBehaviour.Popref_popi_pop1 or StackBehaviour.Popref_popi_popi or StackBehaviour.Popref_popi_popi8
            or StackBehaviour.Popref_popi_popr4 or StackBehaviour.Popref_popi_popr8 or StackBehaviour.Popref_popi_popref => 3,
        _ => throw new InvalidDataException($"不能核对栈效果 {effect}"),
    };
}
