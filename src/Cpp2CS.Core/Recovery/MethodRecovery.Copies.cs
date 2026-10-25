using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private readonly Dictionary<(ulong, TypeDef), MethodDef?> copies = new();
    private readonly Dictionary<ulong, string?> irShapes = new();

    /// <summary>
    /// 方法的本地副本：IL2CPP 为跨文件内联生成的副本（例如 AsyncUniTaskMethodBuilder.get_Task），clang 没有内联时留下的函数没有注册入口，
    /// 也没有 F8 的 MethodInfo 见证（非泛型方法不传 MethodInfo）。副本与原函数的差别只在各自的元数据初始化守卫和隐藏 MethodInfo 实参
    /// （原函数转传自己的，副本传 0）。在接收者类型的方法中找与它 L2 归一后形状相同（块序号代替地址、调用不计隐藏 MethodInfo 实参）的唯一方法。
    /// 这只决定 C# 里写哪个方法：执行对照两侧都透明执行（原生侧执行副本的机器码，CIL 侧执行该方法的方法体），身份选错会表现为不一致。
    /// </summary>
    private MethodDef? CopyOf(ulong target, TypeDef type)
    {
        if (copies.TryGetValue((target, type), out var known)) return known;
        MethodDef? result = null;
        if (facts.EntriesAt(target).Length == 0 && facts.Unregistered.At(target) is null && facts.Code.At(target) is { } function && function.Start == target
            && facts.Code.RegionOf(target) == CodeRegion.Managed && type.GenericParameters.Count == 0 && IrShape(target) is { } shape)
        {
            // 长度不要求相同（副本与原函数的守卫、MethodInfo 传递各占的指令数可能不同），只比较 L2 归一后的形状。
            var matches = type.Methods.Where(m => m.Address != 0 && m.GenericParameters.Count == 0 && facts.Code.RegionOf(m.Address) == CodeRegion.Managed
                && facts.EntriesAt(m.Address).Select(e => e.Method?.Method).Distinct().Count() == 1 && IrShape(m.Address) == shape).ToArray();
            if (matches is [var only]) result = only;
        }
        return copies[(target, type)] = result;
    }

    private string? IrShape(ulong entry)
    {
        if (irShapes.TryGetValue(entry, out var known)) return known;
        string? shape = null;
        var lifted = lifter.Lift(entry);
        if (lifted.Succeeded && rewriter.Run(lifted.Function) is { Errors.Count: 0 })
        {
            var index = lifted.Function.Blocks.Select((b, i) => (b.Start, i)).ToDictionary(p => p.Start, p => p.i);
            string Block(ulong address) => index.TryGetValue(address, out var i) ? $"B{i}" : $"0x{address:x}";
            var text = new System.Text.StringBuilder();
            foreach (var block in lifted.Function.Blocks)
            {
                text.Append('|');
                foreach (var statement in block.Statements)
                    text.Append(statement switch
                    {
                        Branch b => $"if {b.Condition} goto {Block(b.Target)} else {Block(b.Fallthrough)}",
                        Jump j => $"goto {Block(j.Target)}",
                        Call c => WithoutMethodInfo(c).ToString(),
                        _ => statement.ToString(),
                    }).Append(';');
            }
            // SSA 版本号按出现顺序重编（原函数多一个转传 MethodInfo 的定义，后续版本号会整体错开）。
            var renamed = new Dictionary<string, string>();
            var counters = new Dictionary<string, int>();
            shape = System.Text.RegularExpressions.Regex.Replace(text.ToString(), @"\b([a-z]+\d+)_(\d+)\b", m =>
            {
                if (renamed.TryGetValue(m.Value, out var known)) return known;
                var storage = m.Groups[1].Value;
                counters[storage] = counters.GetValueOrDefault(storage) + 1;
                return renamed[m.Value] = $"{storage}#{counters[storage]}";
            });
        }
        return irShapes[entry] = shape;
    }

    /// <summary>直接调用去掉隐藏 MethodInfo 实参（按被调者签名的寄存器）：原函数转传自己的 MethodInfo，副本传 0。</summary>
    private Call WithoutMethodInfo(Call call)
    {
        if (call is not { Op: null, Target: Const target } || lifter.Calls is not FactsCallModel model || model.Signature(target.Value)?.MethodInfo is not { } register) return call;
        var keep = Enumerable.Range(0, call.Sources.Length).Where(k => call.Sources[k] != register).ToArray();
        return call with { Arguments = keep.Select(k => call.Arguments[k]).ToArray(), Sources = keep.Select(k => call.Sources[k]).ToArray() };
    }
}
