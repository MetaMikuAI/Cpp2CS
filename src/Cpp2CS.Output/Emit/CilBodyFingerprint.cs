using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>CIL 的稳定语义编码：忽略写盘分配的 MVID、token 和字节偏移，保留完整签名、指令、局部变量和 EH。</summary>
public static class CilBodyFingerprint
{
    public static byte[] Describe(MethodDefinition method) => Describe(method, method.Body);

    public static byte[] Describe(MethodDefinition method, MethodBody body)
    {
        using var stream = new MemoryStream();
        using var writer = new BinaryWriter(stream, Encoding.UTF8, true);
        var positions = body.Instructions.Select((i, n) => (i, n)).ToDictionary(x => x.i, x => x.n);
        int Position(Instruction? instruction) => instruction is null ? -1 : positions[instruction];
        void Type(TypeReference type)
        {
            // MemberRef 写盘后不保存泛型形参名字（T 可能读成 !0）；身份是所属种类与位置。
            if (type is GenericParameter parameter)
            {
                writer.Write("parameter"); writer.Write((int)parameter.Type); writer.Write(parameter.Position);
                return;
            }
            if (type is TypeSpecification specification)
            {
                writer.Write(type.GetType().Name);
                Type(specification.ElementType);
                switch (type)
                {
                    case GenericInstanceType generic:
                        writer.Write(generic.GenericArguments.Count);
                        foreach (var argument in generic.GenericArguments) Type(argument);
                        break;
                    case ArrayType array:
                        writer.Write(array.IsVector); writer.Write(array.Rank);
                        foreach (var dimension in array.Dimensions)
                        {
                            writer.Write(dimension.LowerBound.HasValue);
                            if (dimension.LowerBound is { } lower) writer.Write(lower);
                            writer.Write(dimension.UpperBound.HasValue);
                            if (dimension.UpperBound is { } upper) writer.Write(upper);
                        }
                        break;
                    case IModifierType modifier: Type(modifier.ModifierType); break;
                    case ByReferenceType or PointerType or PinnedType or SentinelType: break;
                    default: throw new NotSupportedException($"CIL 一致性检查尚不支持类型 {type.GetType()}");
                }
                return;
            }
            writer.Write("type"); writer.Write(type.FullName);
            writer.Write(type.GetElementType().Scope switch
            {
                AssemblyNameReference assembly => assembly.FullName,
                ModuleDefinition module => module.Assembly.Name.FullName,
                var scope => scope.Name,
            });
        }
        void Method(MethodReference reference)
        {
            writer.Write(reference is GenericInstanceMethod);
            if (reference is GenericInstanceMethod generic)
            {
                Method(generic.ElementMethod);
                writer.Write(generic.GenericArguments.Count);
                foreach (var argument in generic.GenericArguments) Type(argument);
                return;
            }
            writer.Write(reference.Name);
            writer.Write(reference.HasThis);
            writer.Write(reference.ExplicitThis);
            // Generic 位由签名的形参数量确定，Cecil 在写盘时才补上它。
            writer.Write((int)reference.CallingConvention & ~(int)MethodCallingConvention.Generic);
            writer.Write(reference.GenericParameters.Count);
            Type(reference.DeclaringType);
            Type(reference.ReturnType);
            writer.Write(reference.Parameters.Count);
            foreach (var parameter in reference.Parameters) Type(parameter.ParameterType);
            // 同模块的合成导入使用 MethodDef token；库、入口和 ABI 也是调用身份的一部分。
            var import = (reference as MethodDefinition)?.PInvokeInfo;
            if (import is not null)
            {
                writer.Write("pinvoke"); writer.Write(import.Module.Name); writer.Write(import.EntryPoint); writer.Write((int)import.Attributes);
            }
        }
        Method(method);
        writer.Write(body.InitLocals);
        writer.Write(body.Variables.Count);
        foreach (var local in body.Variables) Type(local.VariableType);
        writer.Write(body.Instructions.Count);
        foreach (var instruction in body.Instructions)
        {
            writer.Write((int)instruction.OpCode.Code);
            writer.Write(instruction.Operand?.GetType().Name switch
            {
                // 定义与引用在写盘前后表示不同，按元数据实体的语义身份比较。
                _ when instruction.Operand is MethodReference => "method",
                _ when instruction.Operand is FieldReference => "field",
                _ when instruction.Operand is TypeReference => "type",
                var name => name ?? "null",
            });
            switch (instruction.Operand)
            {
                case null: break;
                case Instruction target: writer.Write(Position(target)); break;
                case Instruction[] targets:
                    writer.Write(targets.Length);
                    foreach (var target in targets) writer.Write(Position(target));
                    break;
                case VariableDefinition variable: writer.Write(variable.Index); break;
                case ParameterDefinition parameter: writer.Write(parameter.Index); break;
                case MethodReference reference: Method(reference); break;
                case FieldReference field: writer.Write(field.Name); Type(field.DeclaringType); Type(field.FieldType); break;
                case TypeReference type: Type(type); break;
                case string text: writer.Write(text); break;
                case sbyte number: writer.Write(number); break;
                case byte number: writer.Write(number); break;
                case int number: writer.Write(number); break;
                case long number: writer.Write(number); break;
                case float number: writer.Write(BitConverter.SingleToInt32Bits(number)); break;
                case double number: writer.Write(BitConverter.DoubleToInt64Bits(number)); break;
                default: throw new NotSupportedException($"CIL 一致性检查尚不支持 {instruction.Operand.GetType()}");
            }
        }
        writer.Write(body.ExceptionHandlers.Count);
        foreach (var handler in body.ExceptionHandlers)
        {
            writer.Write((int)handler.HandlerType);
            writer.Write(Position(handler.TryStart)); writer.Write(Position(handler.TryEnd));
            writer.Write(Position(handler.HandlerStart)); writer.Write(Position(handler.HandlerEnd));
            writer.Write(Position(handler.FilterStart));
            writer.Write(handler.CatchType is not null);
            if (handler.CatchType is { } type) Type(type);
        }
        // MaxStack、MVID、token 和指令字节偏移由写盘分配；控制流已按指令序号严格比较。
        writer.Flush();
        return stream.ToArray();
    }
}
