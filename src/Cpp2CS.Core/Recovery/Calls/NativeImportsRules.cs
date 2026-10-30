using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using System.Reflection;

namespace Cpp2CS.Recovery;

internal static class NativeImportsRules
{
    [Analysis("数学导入", 60)]
    internal static void AnalyzeNativeImports(this RecoveryScope ctx)
    {
        var libraries = ctx.facts.Model.Image.NeededLibraries.Where(n => n is "libm.so" or "libm.so.6").ToArray();
        if (libraries.Length != 1)
            return;
        foreach (var call in ctx.blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (call is { Kind: CallKind.Direct, Op: { Kind: OpKind.ImportOutPair, Operand: "sincosf" }, Arguments.Length: 1, Defines: [{ } sine, { } cosine] })
            {
                Register(call, "sincosf", new PrimitiveRef("void"), [new("value", ctx.types.Single, 0, null, false), new("sine", new ByRefRef(ctx.types.Single), ParameterAttributes.Out, null, false), new("cosine", new ByRefRef(ctx.types.Single), ParameterAttributes.Out, null, false)]);
                ctx.State.Types.known[sine] = ctx.types.Single;
                ctx.State.Types.known[cosine] = ctx.types.Single;
                continue;
            }

            if (call is not { Kind: CallKind.Direct or CallKind.Tail, Op: { Kind: OpKind.Import, Operand: string symbol } } || call.Kind == CallKind.Direct && (call.Results is not [var result] || result != Storage.Vec(0) || call.Defines.Length != 1))
                continue;
            string[]? parameters = symbol switch
            {
                "sinf" or "tanf" or "acos" => ["value"],
                "fmodf" => ["value", "divisor"],
                "powf" => ["value", "power"],
                "atan2" or "atan2f" => ["y", "x"],
                _ => null
            };
            if (parameters is null || call.Arguments.Length != parameters.Length)
                continue;
            var scalar = symbol is "acos" or "atan2" ? ctx.types.Double : ctx.types.Single;
            // 保留导入的精度及实参顺序，不替换成另一精度或近似表达式。
            Register(call, symbol, scalar, parameters.Select(name => new ParameterDef(name, scalar, 0, null, false)).ToArray());
            if (call.Defines is [{ } output])
                ctx.State.Types.known[output] = scalar;
        }

        void Register(Call call, string symbol, TypeRef returned, ParameterDef[] parameters)
        {
            var ownerType = new TypeDef
            {
                Index = -1,
                Assembly = ctx.method.Method.Owner.Assembly,
                Namespace = "Cpp2CS",
                Name = "NativeImports",
                Token = 0,
                Attributes = TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit,
                IsValueType = false,
                IsEnum = false
            };
            var imported = new MethodDef
            {
                Index = -1,
                Owner = ownerType,
                Name = symbol,
                Token = 0,
                Attributes = MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.PinvokeImpl,
                ImplAttributes = MethodImplAttributes.PreserveSig,
                Slot = -1,
                ReturnType = returned,
                Parameters = parameters,
                NativeImport = new(libraries[0], symbol)
            };
            ctx.State.Calls.nativeImports.Add(call, new(imported, [], []));
        }
    }

    [CallRule(20)]
    internal static RecoveryResult<bool> NativeImportCall(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (!ctx.State.Calls.nativeImports.TryGetValue(call, out var imported))
            return false;
        if (call.Kind == CallKind.Tail && !ctx.State.Signature.returnType.Equals(imported.Method.ReturnType))
            return false;
        var arguments = new List<ManagedValue>();
        foreach (var operand in call.Arguments)
        {
            var type = imported.Method.Parameters[arguments.Count].Type;
            if (!ctx.Values.RecoverAs(ScalarVectorNarrowing.Low(operand, ctx.types.Bits(type)), type, call.Address).TryGet(out var argument, out var failure))
                return failure;
            arguments.Add(argument);
        }

        LocalValue? result = null;
        if (call.Op?.Kind == OpKind.ImportOutPair)
        {
            foreach (var variable in call.Defines)
            {
                if (!ctx.Values.Local(variable).TryGet(out var local, out var failure))
                    return failure;
                arguments.Add(new AddressValue(local));
            }
        }
        else if (call.Kind != CallKind.Tail && !ctx.Values.Local(call.Defines[0]).TryGet(out result, out var resultFailure))
            return resultFailure;
        output.Add(new ManagedCall(call.Address, new(imported, null, arguments.ToArray(), false), result, call.Kind == CallKind.Tail));
        return true;
    }
}
