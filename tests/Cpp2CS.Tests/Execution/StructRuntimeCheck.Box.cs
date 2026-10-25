using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static partial class StructRuntimeCheck
{
    /// <summary>ECMA-335 III.4.1：装箱复制全部字段；随后修改局部值不能改变盒子。仅合成 IL，不读取原生方法。</summary>
    private static void CheckBoxing(World world, Skeleton skeleton, CilInterpreter interpreter, Assertions a)
    {
        var model = world.Index.Facts.Model;
        var method = model.Methods.First(m => m.ReturnType.Equals(world.Types.Object)
            && m.Owner.GenericParameters.Count == 0 && m.GenericParameters.Count == 0 && m.Parameters.Count == 0);
        var tested = new MethodRef(method, [], []);
        var definition = skeleton.Method(method);
        foreach (var name in new[] { "UnityEngine.Vector3", "UnityEngine.Matrix4x4" })
        {
            var type = new DefinitionRef(model.Types.Single(t => t.FullName == name), []);
            var reference = skeleton.Reference(definition.Module, type, definition.DeclaringType, definition);
            definition.Body = new MethodBody(definition) { InitLocals = true };
            var local = new VariableDefinition(reference);
            var boxed = new VariableDefinition(definition.Module.TypeSystem.Object);
            definition.Body.Variables.Add(local); definition.Body.Variables.Add(boxed);
            var il = definition.Body.GetILProcessor();
            var expected = new byte[world.StorageSize(type)];
            var fields = world.Index.Facts.Layouts.Of(type)!.Fields.OrderBy(f => f.Offset).ToArray();
            for (var i = 0; i < fields.Length; i++)
            {
                var field = fields[i];
                a.True(field.Type.Equals(world.Types.Single), $"{name} 合成用例叶子为 float");
                var value = i + 1.25f;
                il.Emit(OpCodes.Ldloca, local); il.Emit(OpCodes.Ldc_R4, value);
                il.Emit(OpCodes.Stfld, skeleton.Reference(definition.Module, new FieldRef(field.Field, type), definition.DeclaringType, definition));
                BitConverter.GetBytes(value).CopyTo(expected, field.Offset - RuntimeLayout.ObjectHeaderSize);
            }
            il.Emit(OpCodes.Ldloc, local); il.Emit(OpCodes.Box, reference); il.Emit(OpCodes.Stloc, boxed);
            il.Emit(OpCodes.Ldloca, local); il.Emit(OpCodes.Initobj, reference);
            il.Emit(OpCodes.Ldloc, boxed); il.Emit(OpCodes.Ret);
            var arguments = StructAbi.ArgumentTypes(tested).Select(p => interpreter.FromBytes(p, new byte[world.StorageSize(p)])).ToArray();
            var side = interpreter.Run(world, definition, tested, arguments);
            var actual = new byte[expected.Length]; side.Read(World.HeapBase + RuntimeLayout.ObjectHeaderSize, actual);
            a.True(actual.SequenceEqual(expected), $"{name} 的 box 完整复制且不与局部值共享存储");
            a.Equal($"return 0x{World.HeapBase:x}", side.Result, $"{name} 装箱结果为对象引用");
        }
    }
}
