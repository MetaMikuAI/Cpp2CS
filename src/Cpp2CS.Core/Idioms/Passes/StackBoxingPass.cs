using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Storage;
using Cpp2CS.Recovery.Calls;

namespace Cpp2CS.Idioms;

/// <summary>
/// IL2CPP 的栈上临时装箱：对值类型调用其基类（Object、ValueType、Enum）上的实例方法时，codegen 不在堆上分配，
/// 而在栈帧上写入类指针、monitor（-1，标记栈上临时对象）与值，以对象地址作为接收者调用，对象只在这次调用期间存在。
/// 三项写入在每条路径上都到达调用时，接收者换成对值的 box（ECMA-335 I.8.2.4）；值保留在原栈槽中，由内存模型处理。
/// </summary>
internal static class StackBoxingPass
{
    internal static bool StackBoxing(this IdiomState state) =>
        Run(state.function, state.owner.CallEffects, state.owner.Shapes.Of, state.owner.abi.Size, state.Fresh);

    internal static bool Run(MachineFunction function, IFrameCallEffects effects, Func<Call, CallShape> shapes, Func<TypeRef, int> size, Func<Variable> fresh)
    {
        FrameModel? model = null;
        var changed = false;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call || shapes(call) is not { Candidates: [{ Method.IsStatic: false } callee], Signature.This: { } self }
                    || !ManagedTypes.IsReferenceType(callee.DeclaringType)) continue;
                var receiver = call.ArgumentIndex(self.Pieces[0].Register);
                if (receiver < 0) continue;
                model ??= new FrameModel(function, effects);
                if (model.Slot(call.Arguments[receiver]) is not { } frame) continue;
                var values = model.Reach(block, i, frame + RuntimeLayout.ObjectKlass, 8);
                if (!values.Complete || values.Stores.Select(s => Bits(model, s, frame + RuntimeLayout.ObjectKlass, 64)).Distinct().ToArray()
                    is not [Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsValueType: true } type } header]
                    || !DerivesFrom(type, callee.DeclaringType)) continue;
                var bytes = size(type);
                if (bytes <= 0) continue;
                var monitors = model.Reach(block, i, frame + RuntimeLayout.ObjectMonitor, 8);
                if (!monitors.Complete || monitors.Stores.Any(s => Bits(model, s, frame + RuntimeLayout.ObjectMonitor, 64) is not Const { Value: ulong.MaxValue })
                    || !model.Reach(block, i, frame + RuntimeLayout.ObjectHeaderSize, bytes).Complete) continue;
                var result = fresh();
                block.Statements.Insert(i++, new Call(call.Address, CallKind.Direct, Expr.C(0, 64))
                {
                    Op = new(OpKind.Box, type), Arguments = [header, new FrameAddress(frame + RuntimeLayout.ObjectHeaderSize)],
                    Sources = [Storage.Gpr(0), Storage.Gpr(1)], Results = [result.Storage], Defines = [result],
                });
                var arguments = call.Arguments.ToArray();
                arguments[receiver] = new Use(result, 64);
                block.Statements[i] = call with { Arguments = arguments };
                changed = true;
                model = null;
            }
        return changed;
    }

    private static Expr? Bits(FrameModel model, Store store, long offset, int width) =>
        model.Slot(store.Target) is { } start ? Fold.Extract(store.Value, checked((int)(offset - start) * 8), width) : null;

    /// <summary>值类型的基类链上有被调方法的声明类型。</summary>
    private static bool DerivesFrom(DefinitionRef type, TypeRef declaring)
    {
        for (var current = type.Definition.BaseType?.Substitute(type.Arguments, []); current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []))
            if (d.Definition == (declaring as DefinitionRef)?.Definition) return true;
        return false;
    }
}
