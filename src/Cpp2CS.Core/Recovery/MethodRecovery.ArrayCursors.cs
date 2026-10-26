using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<Variable, Expr> arrayCursors = new();

        private void PrepareArrayCursors()
        {
            foreach (var cursor in ArrayCursorRecognition.Read(function,
                expression => TypeOfAddressBase(expression) is ArrayRef { IsVector: true } array ? types.Size(array.Element) : null))
            {
                arrayCursors[cursor.Pointer] = cursor.Address;
                runtime.Add(cursor.Pointer);
                runtime.UnionWith(cursor.AddressCopies);
            }
            if (arrayCursors.Count > 0) InferTypes();
        }
    }
}
