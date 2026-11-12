using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private static bool Opaque(TypeRef type) => type is GenericParameterRef;
    private static bool GenericStruct(TypeRef type) => type switch
    {
        ByRefRef r => GenericStruct(r.Element), PointerRef p => GenericStruct(p.Element),
        DefinitionRef { Definition.IsValueType: true } => type.ContainsGenericParameter(), _ => false,
    };
    private bool Scalar(TypeRef type) => Opaque(type) || IntegerType(type) || IsFloat(type) || ReferenceType(type) || ManagedTypes.IsNativePointer(type);
    private int ValueWidth(TypeRef type) => Opaque(type) ? types.Size(type) * 8 : types.ValueWidth(type);
    private T? GenericFailure<T>(string reason, string message) where T : class =>
        Fail<T>(LoweringFailureKind.UnsupportedType, message, code: "lowering.Generic." + reason);

    private void CheckGenericBody(ManagedBody body)
    {
        if (!GenericWitness.IsGeneric(method.Method)) return;
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            position = statement.Address;
            if (statement is ManagedBranch branch && Opaque(branch.Condition.Type))
                GenericFailure<object>("NullTest", "类型参数值的判空尚未下降");
            foreach (var value in ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk))
            {
                if (GenericStruct(value.Type))
                    GenericFailure<object>("Struct", "含类型参数的值类型尚未下降");
                if (value is ConversionValue conversion && Opaque(conversion.Operand.Type))
                    GenericFailure<object>("Conversion", "类型参数值不能作为其他类型的位型");
                if (value is BinaryValue binary && (Opaque(binary.Left.Type) || Opaque(binary.Right.Type))
                    || value is UnaryValue unary && Opaque(unary.Operand.Type))
                    GenericFailure<object>("Arithmetic", "类型参数值参与运算");
                if (value is ComparisonValue comparison && (Opaque(comparison.Left.Type) || Opaque(comparison.Right.Type)))
                    GenericFailure<object>(comparison.Left is ConstantValue { Bits: 0 } || comparison.Right is ConstantValue { Bits: 0 }
                        ? "NullTest" : "Arithmetic", "类型参数值参与比较");
            }
        }
    }
}
