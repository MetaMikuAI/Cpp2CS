using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class SignatureBinding
{
    internal static bool BindSignature(this RecoveryScope ctx, out AbiSignature signature, out Expr? returnValue)
    {
        signature = null!;
        returnValue = null;
        var definition = ctx.method.Method;
        // 依赖访问器可以沿用调用者的引用布局见证，保留其 T 身份；没有见证的开放参数仍拒绝。
        var closed = ctx.ClosedInstance && ctx.method.MethodArguments.Count == definition.GenericParameters.Count && ctx.method.TypeArguments.Count == definition.Owner.GenericParameters.Count && ctx.method.TypeArguments.Concat(ctx.method.MethodArguments).All(a => a is DefinitionRef or ArrayRef or GenericParameterRef { Binding: { Kind: NativeBindingKind.Reference, Entry: > 0 } });
        if (!closed && !ctx.SharedDefinition && (definition.GenericParameters.Count > 0 || definition.Owner.GenericParameters.Count > 0 || ctx.method.TypeArguments.Count > 0))
        {
            ctx.Hole(ctx.entry, "泛型 方法或类型带泛型参数", rule: "Prepare");
            return false;
        }

        if (ctx.owner.abi.Classify(ctx.method, out var problem) is not { } classified)
        {
            ctx.Hole(ctx.entry, $"签名 {problem}", rule: "Prepare");
            return false;
        }

        signature = classified;
        if (signature.This is { } self)
            ctx.State.Signature.arguments[self.Pieces[0].Register] = new(-1, self.Type, 64);
        var incomingStack = ctx.owner.abi.StackArguments(signature);
        for (var i = 0; i < signature.Parameters.Length; i++)
        {
            var parameter = signature.Parameters[i];
            if (RuleRegistry.Parameters.Any(rule => rule(ctx, parameter, i)))
                continue;
            if (incomingStack.Parameters.FirstOrDefault(p => p.Index == i) is { Indirect: false } stackParameter && (ctx.types.Kind(parameter.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Reference or TypeKind.Float or TypeKind.Double || ManagedTypes.IsNativePointer(parameter.Type)))
            {
                ctx.State.Signature.arguments[Storage.Slot(stackParameter.Offset)] = new(i, parameter.Type, stackParameter.Size * 8);
                continue;
            }

            if (parameter.Passing != Passing.Registers || parameter.Pieces.Length != 1 || ctx.types.Kind(parameter.Type) is TypeKind.Struct or null || ctx.types.Kind(parameter.Type) == TypeKind.Pointer && !ManagedTypes.IsNativePointer(parameter.Type) && (parameter.Type is not ByRefRef parameterReference || ctx.types.Kind(parameterReference.Element) is not (TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference) && !ManagedTypes.IsNativePointer(parameterReference.Element)))
            {
                var hole = ctx.Hole(ctx.entry, $"参数 {definition.Parameters[i].Name} 的类型 {parameter.Type} 尚未支持", rule: "Prepare");
                foreach (var piece in parameter.Pieces)
                    ctx.Poison(new Variable(piece.Register, 0), hole);
                continue;
            }

            ctx.State.Signature.arguments[parameter.Pieces[0].Register] = new(i, parameter.Type, parameter.Pieces[0].Width);
        }

        ctx.State.Signature.returnType = definition.ReturnType.Substitute(ctx.method.TypeArguments, ctx.method.MethodArguments);
        ctx.PrepareReturnBuffer(signature.Return);
        if (signature.Return is { } ret)
        {
            if (!ctx.RegisterStruct(ret) && !ctx.IndirectStruct(ret) && (ret.Passing != Passing.Registers || ret.Pieces.Length != 1 || ctx.types.Kind(ret.Type) is TypeKind.Struct or null || ctx.types.Kind(ret.Type) == TypeKind.Pointer && !ManagedTypes.IsNativePointer(ret.Type)))
            {
                ctx.State.Signature.returnHole = ctx.Hole(ctx.entry, $"返回值 类型 {ret.Type} 尚未支持", rule: "Prepare");
            }

            // 寄存器聚合返回保留全部片；间接返回只写入口缓冲区，返回时的 x8 内容不属于结果。
            if (!ctx.IndirectStruct(ret))
                returnValue = ret.Pieces.Length == 1 ? new Read(ret.Pieces[0].Register, ret.Pieces[0].Width) : new Intrinsic("diagnostic_return", ret.Pieces.Select(p => (Expr)new Read(p.Register, p.Width)).ToArray(), 64);
        }

        return true;
    }
}
