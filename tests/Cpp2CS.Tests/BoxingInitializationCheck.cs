using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using Mono.Cecil.Cil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

internal static class BoxingInitializationCheck
{
    public static void Add(ManagedTypes types, AssemblyDefinition assembly)
    {
        foreach (var name in new[] { "ValueInit", "NullableInit", "FailedInit" })
        {
            var nullable = name == "NullableInit";
            var failure = name == "FailedInit";
            var module = assembly.MainModule;
            TypeDef Owner(string suffix, bool value) => new() { Index = -1, Assembly = assembly.Name.Name + ".dll", Namespace = "Checks", Name = name + suffix,
                Token = 0, Attributes = SR.TypeAttributes.Public | (value ? SR.TypeAttributes.SequentialLayout : 0), IsValueType = value, IsEnum = false,
                Size = value ? 4 : 16, PackingSize = 0, ClassSizeIsDefault = true };
            var owner = Owner("", false); var valueOwner = Owner("Value", true); var valueType = new DefinitionRef(valueOwner, []);
            var value = new FieldDef { Index = -1, Owner = valueOwner, Name = "Value", Type = types.Int32, Offset = 0, Attributes = SR.FieldAttributes.Public };
            valueOwner.Fields = [value];
            MethodRef Method(TypeDef parent, string methodName, TypeRef result) => new(new MethodDef { Index = -1, Owner = parent, Name = methodName,
                Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static, ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result }, [], []);
            valueOwner.Methods = [Method(valueOwner, ".cctor", types.Void).Method];
            var dataType = nullable ? new DefinitionRef(types.CorlibDefinition("System.Nullable")!, [valueType]) : valueType;
            var data = new FieldDef { Index = -1, Owner = owner, Name = "Data", Type = dataType, Offset = 0, Attributes = SR.FieldAttributes.Public | SR.FieldAttributes.Static };
            owner.Fields = [data];
            var host = new TypeDefinition("Checks", name, TypeAttributes.Public, module.TypeSystem.Object); module.Types.Add(host);
            var actualValue = new TypeDefinition("Checks", name + "Value", TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
                module.ImportReference(typeof(ValueType))); module.Types.Add(actualValue);
            var member = new FieldDefinition("Value", FieldAttributes.Public, module.TypeSystem.Int32); actualValue.Fields.Add(member);
            var nullableDefinition = module.ImportReference(typeof(Nullable<>));
            var actualNullable = new GenericInstanceType(nullableDefinition); actualNullable.GenericArguments.Add(actualValue);
            TypeReference Reference(TypeRef type) => type == valueType ? actualValue : nullable && type == dataType ? actualNullable
                : type is ByRefRef reference ? new ByReferenceType(Reference(reference.Element))
                : type == types.Object ? module.TypeSystem.Object : type == types.RuntimeTypeHandle ? module.ImportReference(typeof(RuntimeTypeHandle))
                : module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
            var storage = new FieldDefinition("Data", FieldAttributes.Public | FieldAttributes.Static, Reference(dataType)); host.Fields.Add(storage);
            var count = new FieldDefinition("Count", FieldAttributes.Public | FieldAttributes.Static, module.TypeSystem.Int32); host.Fields.Add(count);
            var initializer = new MethodDefinition(".cctor", MethodAttributes.Private | MethodAttributes.Static | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName,
                module.TypeSystem.Void); actualValue.Methods.Add(initializer);
            var il = initializer.Body.GetILProcessor();
            il.Emit(OpCodes.Ldsfld, count); il.Emit(OpCodes.Ldc_I4_1); il.Emit(OpCodes.Add); il.Emit(OpCodes.Stsfld, count);
            if (failure)
            {
                il.Emit(OpCodes.Newobj, module.ImportReference(typeof(InvalidOperationException).GetConstructor(Type.EmptyTypes))); il.Emit(OpCodes.Throw);
            }
            else
            {
                il.Emit(OpCodes.Ldsflda, storage);
                if (nullable) il.Emit(OpCodes.Initobj, actualNullable);
                else { il.Emit(OpCodes.Ldc_I4, 91); il.Emit(OpCodes.Stfld, member); }
                il.Emit(OpCodes.Ret);
            }
            var fill = new MethodDefinition("Fill", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Void); host.Methods.Add(fill);
            il = fill.Body.GetILProcessor();
            var local = new VariableDefinition(actualValue); fill.Body.Variables.Add(local); fill.Body.InitLocals = true;
            il.Emit(OpCodes.Ldloca, local); il.Emit(OpCodes.Initobj, actualValue);
            il.Emit(OpCodes.Ldloca, local); il.Emit(OpCodes.Ldc_I4_7); il.Emit(OpCodes.Stfld, member); il.Emit(OpCodes.Ldloc, local);
            if (nullable)
            {
                var constructor = new MethodReference(".ctor", module.TypeSystem.Void, actualNullable) { HasThis = true };
                constructor.Parameters.Add(new ParameterDefinition(nullableDefinition.GenericParameters[0])); il.Emit(OpCodes.Newobj, constructor);
            }
            il.Emit(OpCodes.Stsfld, storage); il.Emit(OpCodes.Ret);
            MethodReference Called(MethodRef method) => method.Method.Name == "RunClassConstructor"
                ? module.ImportReference(typeof(System.Runtime.CompilerServices.RuntimeHelpers).GetMethod("RunClassConstructor", [typeof(RuntimeTypeHandle)]))
                : new MethodReference(method.Method.Name, method.Method.Name == "get_HasValue" ? module.TypeSystem.Boolean : nullableDefinition.GenericParameters[0], actualNullable) { HasThis = true };
            var emitter = new BodyEmitter(types, Reference, f => f.Field == data ? storage : throw new NotSupportedException(f.ToString()), Called);
            var operand = new StaticFieldValue(new(data, new DefinitionRef(owner, [])), dataType, types.Size(dataType) * 8);
            var initialization = Boxing.Initialization(types, dataType, out var problem); Require(problem is null && initialization is not null, problem ?? "需要初始化计划");
            var body = new ManagedBody(Method(owner, "Box", types.Object), [new(0x1000, [new ManagedReturn(0x1000, new BoxValue(operand, types.Object, initialization))])]);
            var actual = new MethodDefinition("Box", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Object); host.Methods.Add(actual);
            problem = emitter.Emit(body, actual); Require(problem is null, problem ?? name);
            var missing = body with { Blocks = [new(0x1000, [new ManagedReturn(0x1000, new BoxValue(operand, types.Object))])] };
            Require(emitter.Emit(missing, new MethodDefinition("Bad", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Object)) is not null,
                "不能省略值类型已有的静态构造函数");
        }
    }

    public static void Execute(SR.Assembly assembly)
    {
        foreach (var name in new[] { "ValueInit", "NullableInit", "FailedInit" })
        {
            var host = assembly.GetType("Checks." + name, true)!;
            var fill = host.GetMethod("Fill")!; var box = host.GetMethod("Box")!; var count = host.GetField("Count")!;
            int Count() => (int)count.GetValue(null)!;
            Require(Count() == 0, "访问宿主不应初始化其结构体字段类型");
            if (name == "NullableInit") Require(box.Invoke(null, []) is null && Count() == 0, "无值 nullable 不触发内部类型初始化");
            fill.Invoke(null, []); Require(Count() == 0, "直接字段写入与 nullable 构造没有提前运行内部类型初始化");
            if (name == "FailedInit")
            {
                for (var i = 0; i < 2; i++)
                {
                    var task = Task.Run(() => box.Invoke(null, [])); Task.WhenAny(task).GetAwaiter().GetResult();
                    Require(task.Exception?.InnerException is SR.TargetInvocationException { InnerException: TypeInitializationException { InnerException: InvalidOperationException } },
                        "装箱初始化失败必须传播");
                }
                Require(Count() == 1, "装箱初始化失败被缓存"); continue;
            }
            var result = box.Invoke(null, [])!;
            Require(Count() == 1 && (int)result.GetType().GetField("Value")!.GetValue(result)! == (name == "NullableInit" ? 0 : 91),
                "先初始化后读值；nullable 的有值判定不能在初始化后重做");
            fill.Invoke(null, []); result = box.Invoke(null, [])!;
            Require(Count() == 1 && (int)result.GetType().GetField("Value")!.GetValue(result)! == 7, "初始化只执行一次，之后复制当前值");
        }
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
