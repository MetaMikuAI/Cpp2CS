using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.IL;

namespace Cpp2CS.Output;

internal static class StackDepth
{
    public static int Maximum(List<CilWriter.Item> code, Dictionary<int, int> labels, MethodShape host, IMetadataView metadata)
    {
        var entryDepth = new int?[code.Count];
        var pending = new Queue<int>();
        int peak = 0;
        void Enter(int index, int depth)
        {
            if ((uint)index >= code.Count) throw new InvalidDataException("控制流越过方法体的末尾");
            if (entryDepth[index] is { } known)
            {
                if (known != depth) throw new InvalidDataException($"指令 {index} 合流处的栈深不同：{known}、{depth}");
                return;
            }
            entryDepth[index] = depth;
            pending.Enqueue(index);
        }
        Enter(0, 0);
        while (pending.TryDequeue(out int index))
        {
            var (instruction, form) = code[index];
            var (pop, push) = Transition(instruction, host, metadata);
            int before = entryDepth[index]!.Value;
            if (before < pop) throw new InvalidDataException($"指令 {index} {instruction.Opcode} 栈下溢");
            int after = checked(before - pop + push);
            peak = Math.Max(peak, after);
            if (instruction.Opcode == "ret" && after != 0) throw new InvalidDataException($"指令 {index} 返回时栈非空");
            if (instruction.Target >= 0)
            {
                if (!labels.TryGetValue(instruction.Target, out int target)) throw new InvalidDataException($"缺少标号 {instruction.Target}");
                Enter(target, after);
            }
            if (form.Flow is FlowKind.Next or FlowKind.ConditionalBranch) Enter(index + 1, after);
        }
        if (entryDepth.Contains(null)) throw new InvalidDataException("方法体含没有入口栈深的指令");
        return peak;
    }

    private static (int Pop, int Push) Transition(ManagedInstruction instruction, MethodShape host, IMetadataView metadata)
    {
        var variants = OperationCatalog.ForInstruction(instruction.Opcode);
        if (instruction.Opcode == "ret")
            variants = variants.Where(v => v.Condition == (host.Return is null ? VariantCondition.ReturnsVoid : VariantCondition.ReturnsValue));
        (int Pop, int Push)? effect = null;
        MethodShape? method = null;
        foreach (var variant in variants)
        {
            (int, int) current = (variant.Operands.Length, variant.Result == null ? 0 : 1);
            if (variant.OperandsFromSignature)
            {
                method ??= metadata.Method(instruction.Entity ?? throw new InvalidDataException($"{instruction.Opcode} 缺少方法实体"));
                if (variant.Constructs && !method.HasThis) throw new InvalidDataException("构造函数缺少 this");
                current = (method.Parameters.Length - (variant.Constructs ? 1 : 0), variant.Constructs || method.Return != null ? 1 : 0);
            }
            if (effect.HasValue && effect != current) throw new InvalidDataException($"{instruction.Opcode} 的目录项栈效果不一致");
            effect = current;
        }
        return effect ?? throw new InvalidDataException($"目录缺少 {instruction.Opcode} 的栈效果");
    }
}
