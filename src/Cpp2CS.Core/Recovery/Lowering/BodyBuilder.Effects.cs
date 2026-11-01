using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>副作用次序上的证明：判空被随后的访问吸收、显式类构造被随后的访问触发。</summary>
internal sealed partial class BodyBuilder
{
    /// <summary>
    /// 直线路径上随后第一个有副作用的语句按 IL 语义触发 owner 的类初始化（ECMA-335 II.10.5.3）：访问 owner 的静态字段；
    /// 调用非 beforefieldinit 的 owner 的静态方法或构造函数。中间只允许无副作用的定义与不触发初始化的运行时操作。
    /// </summary>
    private bool Initializes(Block block, int index, TypeRef owner)
    {
        var precise = owner is DefinitionRef d && (d.Definition.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) == 0;
        bool Static(Sym address, int width) => oracle.Locate(address, width) is { Kind: LocationKind.Static, Owner: { } o } && o.Equals(owner);
        for (var steps = 0; steps < 64; steps++)
        {
            if (index >= block.Statements.Count)
            {
                if (block.Successors.Count != 1 || block.Successors[0].Predecessors.Count != 1 || block.Handler is not null) return false;
                block = block.Successors[0];
                index = 0;
                continue;
            }
            var statement = block.Statements[index++];
            if (statement is Nop or Phi or Ir.Jump) continue;
            var reads = Reads(statement).ToArray();
            if (reads.Length > 0) return Static(reads[0].Address, reads[0].Width);
            switch (statement)
            {
                case Define: continue;
                case Store store: return Static(values.Operands(store)[0], store.Value.Width);
                case Call { Op.Kind: OpKind.InitClass or OpKind.RunClassConstructor or OpKind.WriteBarrier or OpKind.InitMethodRgctx }: continue;
                case Call { Op.Kind: OpKind.NewObject }: continue;
                case Call { Op: null } call when oracle.Callee(call) is { } callee:
                    return precise && callee.DeclaringType.Equals(owner) && (callee.Method.IsStatic || callee.Method.Name == ".ctor");
                default: return false;
            }
        }
        return false;
    }

    /// <summary>
    /// 判空被吸收：直线路径上判空之后第一个有副作用的语句经该对象访问字段、元素或调用其实例方法——
    /// ldfld、ldelem 与 callvirt 对 null 抛出同一异常。
    /// </summary>
    private bool Absorbed(Block block, int index, Sym target)
    {
        for (var steps = 0; steps < 64; steps++)
        {
            if (index >= block.Statements.Count)
            {
                if (block.Successors.Count != 1 || block.Successors[0].Predecessors.Count != 1 || block.Handler is not null) return false;
                block = block.Successors[0];
                index = 0;
                continue;
            }
            var statement = block.Statements[index++];
            if (statement is Nop or Phi || statement is Ir.Jump) continue;
            var reads = Reads(statement).ToArray();
            if (reads.Length > 0) return reads.Any(r => ReferenceEquals(oracle.Decompose(r.Address).Root, target));
            switch (statement)
            {
                case Define: continue;
                case Store store: return ReferenceEquals(oracle.Decompose(values.Operands(store)[0]).Root, target);
                case Call { Op: null } call:
                    {
                        var operands = values.Operands(call);
                        return call.Arguments.Length > 0 && ReferenceEquals(SymTable.Resolve(operands[1]), target);
                    }
                case Call { Op.Kind: OpKind.NullCheck or OpKind.WriteBarrier }: continue;
                default: return false;
            }
        }
        return false;
    }
}
