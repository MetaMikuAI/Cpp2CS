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
                if (call is not { Kind: CallKind.Direct or CallKind.Tail, Op: { Kind: OpKind.Import, Operand: "sinf" },
                    Arguments: [_] }
                    || call.Kind == CallKind.Direct && (call.Results is not [var result] || result != Storage.Vec(0) || call.Defines.Length != 1)) continue;
                // C sinf 的参数与结果都是 float；保留导入，避免 double 运算后的二次舍入。
                // https://man7.org/linux/man-pages/man3/sin.3.html
                var ownerType = new TypeDef { Index = -1, Assembly = method.Method.Owner.Assembly, Namespace = "Cpp2CS", Name = "NativeImports",
                    Token = 0, Attributes = TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit,
                    IsValueType = false, IsEnum = false };
                var imported = new MethodDef { Index = -1, Owner = ownerType, Name = "sinf", Token = 0,
                    Attributes = MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.PinvokeImpl,
                    ImplAttributes = MethodImplAttributes.PreserveSig, Slot = -1, ReturnType = types.Single,
                    Parameters = [new("value", types.Single, 0, null, false)], NativeImport = new(libraries[0], "sinf") };
                nativeImports.Add(call, new(imported, [], []));
                if (call.Defines is [{ } output]) known[output] = types.Single;
            }
        }

        [CallRule(20)]
        private bool NativeImportCall(Call call, List<ManagedStatement> output)
        {
            if (!nativeImports.TryGetValue(call, out var imported)) return false;
            if (call.Kind == CallKind.Tail && !returnType.Equals(imported.Method.ReturnType)) return false;
            var argument = RecoverAs(ScalarVectorNarrowing.Low(call.Arguments[0], 32), types.Single, call.Address);
            output.Add(new ManagedCall(call.Address, new(imported, null, [argument], false),
                call.Kind == CallKind.Tail ? null : Local(call.Defines[0]), call.Kind == CallKind.Tail));
            return true;
        }
    }
}
