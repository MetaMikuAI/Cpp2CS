using Cpp2CS.Recovery.Analysis;
using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<Call, MethodRef> nativeImports = new();

        [Analysis("数学导入", 60)]
        private void AnalyzeNativeImports()
        {
            var libraries = facts.Model.Image.NeededLibraries.Where(n => n is "libm.so" or "libm.so.6").ToArray();
            if (libraries.Length != 1) return;
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                if (call is not { Kind: CallKind.Direct or CallKind.Tail, Op: { Kind: OpKind.Import, Operand: string symbol } }
                    || call.Kind == CallKind.Direct && (call.Results is not [var result] || result != Storage.Vec(0) || call.Defines.Length != 1)) continue;
                string[]? parameters = symbol switch { "sinf" => ["value"], "fmodf" => ["value", "divisor"], _ => null };
                if (parameters is null || call.Arguments.Length != parameters.Length) continue;
                // 保留 C 单精度导入及实参顺序，不替换成 double 运算或近似表达式。
                var ownerType = new TypeDef { Index = -1, Assembly = method.Method.Owner.Assembly, Namespace = "Cpp2CS", Name = "NativeImports",
                    Token = 0, Attributes = TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit,
                    IsValueType = false, IsEnum = false };
                var imported = new MethodDef { Index = -1, Owner = ownerType, Name = symbol, Token = 0,
                    Attributes = MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.PinvokeImpl,
                    ImplAttributes = MethodImplAttributes.PreserveSig, Slot = -1, ReturnType = types.Single,
                    Parameters = parameters.Select(name => new ParameterDef(name, types.Single, 0, null, false)).ToArray(), NativeImport = new(libraries[0], symbol) };
                nativeImports.Add(call, new(imported, [], []));
                if (call.Defines is [{ } output]) known[output] = types.Single;
            }
        }

        [CallRule(20)]
        private RecoveryResult<bool> NativeImportCall(Call call, List<ManagedStatement> output)
        {
            if (!nativeImports.TryGetValue(call, out var imported)) return false;
            if (call.Kind == CallKind.Tail && !returnType.Equals(imported.Method.ReturnType)) return false;
            var arguments = new List<ManagedValue>();
            foreach (var operand in call.Arguments)
            {
                if (!RecoverAs(ScalarVectorNarrowing.Low(operand, 32), types.Single, call.Address).TryGet(out var argument, out var failure)) return failure;
                arguments.Add(argument);
            }
            LocalValue? result = null;
            if (call.Kind != CallKind.Tail && !Local(call.Defines[0]).TryGet(out result, out var resultFailure)) return resultFailure;
            output.Add(new ManagedCall(call.Address, new(imported, null, arguments.ToArray(), false),
                result, call.Kind == CallKind.Tail));
            return true;
        }
    }
}
