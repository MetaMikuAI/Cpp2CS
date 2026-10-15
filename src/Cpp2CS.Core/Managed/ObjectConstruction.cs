using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>合并没有中间操作的分配和同类型构造；复杂初始化继续保留独立分配及调用。</summary>
public static class ObjectConstruction
{
    public static ManagedBody Recover(ManagedBody body)
    {
        bool Captured(ManagedValue value) => value.Type is not ByRefRef
            && value is ArgumentValue or LocalValue or ConstantValue or StringValue;
        return body with { Blocks = body.Blocks.Select(block =>
        {
            var statements = new List<ManagedStatement>();
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is ManagedAssignment { Value: ObjectAllocationValue allocation } assignment
                    && !allocation.ObjectType.Definition.Methods.Any(m => m.Name == ".cctor" && m.IsStatic)
                    && i + 1 < block.Statements.Count && block.Statements[i + 1] is ManagedCall { Result: null } call
                    && call.Invocation.Receiver == assignment.Target && call.Invocation.Method is { Method: { Name: ".ctor", IsStatic: false } } constructor
                    && constructor.DeclaringType == allocation.ObjectType && call.Invocation.Arguments.All(Captured))
                {
                    statements.Add(assignment with { Value = new NewObjectValue(constructor, call.Invocation.Arguments) });
                    if (call.Tail) statements.Add(new ManagedReturn(call.Address, null));
                    i++;
                }
                else statements.Add(block.Statements[i]);
            }
            return block with { Statements = statements };
        }).ToArray() };
    }
}
