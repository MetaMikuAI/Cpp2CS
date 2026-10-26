using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        // 保留数组协变检查及其抛出顺序；实际数组类型可能比字段声明的元素类型更窄。
        private void ArrayElementCheck(Call call, Variable created, List<ManagedStatement> output)
        {
            var array = Recover(call.Arguments[1], null);
            if (array.Type is not ArrayRef) throw Fail(call.Address, "数组元素检查缺少数组类型");
            var value = RecoverAs(call.Arguments[0], types.Object, call.Address);
            var getType = types.CorlibMethod("System.Object", "GetType");
            var elementType = types.CorlibMethod("System.Type", "GetElementType");
            var instanceOf = types.CorlibMethod("System.Type", "IsInstanceOfType", types.Object);
            if (getType is null || elementType is null || instanceOf is null) throw Fail(call.Address, "数组元素检查缺少类型反射方法");
            var runtimeType = StructLocal(types.Corlib("System.Type"), 64);
            var element = StructLocal(types.Corlib("System.Type"), 64);
            var matches = StructLocal(types.Boolean, 1);
            output.Add(new ManagedCall(call.Address, new ManagedInvocation(getType, array, [], false), runtimeType, false));
            output.Add(new ManagedCall(call.Address, new ManagedInvocation(elementType, runtimeType, [], true), element, false));
            output.Add(new ManagedCall(call.Address, new ManagedInvocation(instanceOf, element, [value], true), matches, false));
            output.Add(new ManagedAssignment(call.Address, Local(created),
                new ChoiceValue(matches, value, new ConstantValue(0, types.Object, 64), types.Object, 64)));
        }
    }
}
