using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private void CompareExchangeReference(Call call, List<ManagedStatement> output)
        {
            if (call.Arguments is not [var address, var value, var comparand] || call.Defines.FirstOrDefault() is not { } result)
                throw Fail(call.Address, "原子交换 缺少位置、引用参数或返回值");
            var location = Location(address, 64);
            if (types.Kind(location.Type) != TypeKind.Reference) throw Fail(call.Address, "原子交换 位置不是托管引用");
            var definition = types.CorlibDefinition("System.Threading.Interlocked")?.Methods.FirstOrDefault(m => m.Name == "CompareExchange"
                && m.IsStatic && m.GenericParameters.Count == 1 && m.Parameters.Count == 3
                && m.Parameters[0].Type is ByRefRef { Element: GenericParameterRef { IsMethod: true, Position: 0 } }
                && m.Parameters.Skip(1).All(p => p.Type is GenericParameterRef { IsMethod: true, Position: 0 })
                && m.ReturnType is GenericParameterRef { IsMethod: true, Position: 0 });
            if (definition is null) throw Fail(call.Address, "原子交换 核心库缺少 Interlocked.CompareExchange<T>");
            var target = new MethodRef(definition, [], [location.Type]);
            output.Add(new ManagedCall(call.Address, new ManagedInvocation(target, null,
                [new AddressValue(location), RecoverAs(value, location.Type, call.Address), RecoverAs(comparand, location.Type, call.Address)], false), Local(result), false));
            if (call.Kind == CallKind.Tail) output.Add(new ManagedReturn(call.Address, Local(result)));
        }
    }
}
