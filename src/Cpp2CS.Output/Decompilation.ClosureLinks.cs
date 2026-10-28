using System.Buffers.Binary;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.IL.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>内层闭包的固定外层引用仍指向入口对象；展开前统一该引用的读取。</summary>
    private sealed class ClosureLinks : IILTransform
    {
        public void Run(ILFunction function, ILTransformContext context)
        {
            static bool Closure(IType type) => type.GetDefinition() is { IsReferenceType: true } definition
                && definition.Name.Contains("DisplayClass", StringComparison.Ordinal)
                && definition.GetAttributes().Any(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute");
            foreach (var store in function.Descendants.OfType<StObj>().ToArray())
            {
                if (store.Target is not LdFlda { Target: LdLoc owner } link || store.Value is not LdLoc original
                    || store.Parent is not Block block || function.Body is not BlockContainer body
                    || owner.Variable.Function != function || original.Variable.Function != function
                    || !owner.Variable.IsSingleDefinition || !original.Variable.IsSingleDefinition
                    || owner.Variable.UsesInitialValue || original.Variable.UsesInitialValue
                    || owner.Variable.AddressInstructions.Count != 0 || original.Variable.AddressInstructions.Count != 0
                    || !Closure(owner.Variable.Type) || !Closure(original.Variable.Type)
                    || !link.Field.ReturnType.Equals(original.Variable.Type)
                    || owner.Variable.StoreInstructions.OfType<StLoc>().ToArray() is not [StLoc { Value: NewObj creation } allocation]
                    || !EmptyConstructor(creation.Method)
                    || allocation.Parent != block || block.Instructions.IndexOf(allocation) + 1 != block.Instructions.IndexOf(store)
                    || original.Variable.StoreInstructions.OfType<StLoc>().ToArray() is not [StLoc { Value: NewObj, Parent: Block entry }]
                    || entry != body.EntryPoint
                    || owner.Variable.LoadInstructions.Any(read => read.Parent is not LdFlda)) continue;
                var accesses = owner.Variable.LoadInstructions.Select(read => (LdFlda)read.Parent!).Where(field => field.Field.Equals(link.Field)).ToArray();
                // 委托主体已展开，所有可达的字段地址只能用于读取或这一处初始化，闭包对象自身不能逃逸。
                if (accesses.Any(field => field.Parent is not LdObj { IsVolatile: false } && field.Parent != store)) continue;
                foreach (var read in accesses.Select(field => field.Parent).OfType<LdObj>().ToArray())
                {
                    var replacement = new LdLoc(original.Variable);
                    replacement.AddILRange(read);
                    read.ReplaceWith(replacement);
                }
            }
        }

        // 自定义构造函数可能发布 this；只接受编译器常规的 object 构造转调。
        private static bool EmptyConstructor(IMethod constructor)
        {
            if (constructor.MemberDefinition.MetadataToken.Kind != HandleKind.MethodDefinition
                || constructor.ParentModule is not MetadataModule module) return false;
            var definition = module.MetadataFile.Metadata.GetMethodDefinition((MethodDefinitionHandle)constructor.MemberDefinition.MetadataToken);
            if (definition.RelativeVirtualAddress == 0) return false;
            var body = module.MetadataFile.GetMethodBody(definition.RelativeVirtualAddress);
            var bytes = body.GetILBytes()!;
            var start = 0;
            while (start < bytes.Length && bytes[start] == (byte)ILOpCode.Nop) start++;
            if (body.ExceptionRegions.Length != 0 || bytes.Length - start != 7 || bytes[start] != (byte)ILOpCode.Ldarg_0
                || bytes[start + 1] != (byte)ILOpCode.Call || bytes[^1] != (byte)ILOpCode.Ret) return false;
            var target = module.ResolveMethod(MetadataTokens.EntityHandle(BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(start + 2, 4))), default);
            return target is { IsConstructor: true, IsStatic: false, Parameters.Count: 0, DeclaringType.FullName: "System.Object" };
        }
    }
}
