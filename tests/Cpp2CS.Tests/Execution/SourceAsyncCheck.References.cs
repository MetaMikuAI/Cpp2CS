using Microsoft.CodeAnalysis;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static partial class SourceAsyncCheck
{
    private const string BuilderContract = "https://github.com/Cysharp/UniTask/blob/a77a1b4a89824fb6df293099de3060daf2a432c1/src/UniTask/Assets/Plugins/UniTask/Runtime/CompilerServices/AsyncUniTaskMethodBuilder.cs";

    internal static MetadataReference[] CompilationReferences(string assemblies, string proof, bool includeVoidBuilder = false)
    {
        var reference = Path.Combine(proof, "refs", "UniTask.dll");
        Directory.CreateDirectory(Path.GetDirectoryName(reference)!);
        using var module = ModuleDefinition.ReadModule(Path.Combine(assemblies, "UniTask.dll"));
        foreach (var builder in new[] { module.GetType("Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder`1"),
                     module.GetType("Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder") })
        if (!builder.Methods.Any(m => m.Name == "AwaitOnCompleted"))
        {
            // IL2CPP 裁剪了未使用的公开声明；此补全只供 C# 编译引用，不参与原生恢复与执行。
            // 签名及约束来自 BuilderContract。生成的两个状态机还须证明没有调用此补全声明。
            var method = new MethodDefinition("AwaitOnCompleted", MethodAttributes.Public | MethodAttributes.HideBySig, module.TypeSystem.Void);
            foreach (var (name, constraint) in new[] { ("TAwaiter", "INotifyCompletion"), ("TStateMachine", "IAsyncStateMachine") })
            {
                var generic = new GenericParameter(name, method);
                generic.Constraints.Add(new GenericParameterConstraint(new TypeReference("System.Runtime.CompilerServices", constraint, module, module.TypeSystem.CoreLibrary)));
                method.GenericParameters.Add(generic);
                method.Parameters.Add(new ParameterDefinition(new ByReferenceType(generic)));
            }
            method.Body.Instructions.Add(Instruction.Create(OpCodes.Ldnull));
            method.Body.Instructions.Add(Instruction.Create(OpCodes.Throw));
            builder.Methods.Add(method);
            var attribute = new TypeReference("System.Runtime.CompilerServices", "ReferenceAssemblyAttribute", module, module.TypeSystem.CoreLibrary);
            module.Assembly.CustomAttributes.Add(new CustomAttribute(new MethodReference(".ctor", module.TypeSystem.Void, attribute) { HasThis = true }));
        }
        module.Write(reference);
        File.WriteAllText(Path.Combine(proof, "references.txt"), "UniTask.dll 是仅供编译的引用副本；补全裁剪的 AwaitOnCompleted 声明，无运行实现。其余引用来自匹配版本元数据。\n" + BuilderContract + "\n");
        var voidReference = Path.Combine(proof, "refs", "mscorlib.dll");
        if (includeVoidBuilder)
        {
            using var corlib = ModuleDefinition.ReadModule(Path.Combine(assemblies, "mscorlib.dll"));
            var builder = corlib.GetType("System.Runtime.CompilerServices.AsyncVoidMethodBuilder");
            if (!builder.Methods.Any(m => m.Name == "AwaitOnCompleted"))
            {
                // 无 await 也要求完整 builder 编译契约；声明来自 CLR 的公开 API，不参与恢复和执行。
                var contract = typeof(System.Runtime.CompilerServices.AsyncVoidMethodBuilder).GetMethod("AwaitOnCompleted")!;
                var method = new MethodDefinition(contract.Name, MethodAttributes.Public | MethodAttributes.HideBySig, corlib.TypeSystem.Void);
                foreach (var parameter in contract.GetGenericArguments())
                {
                    var generic = new GenericParameter(parameter.Name, method);
                    foreach (var constraint in parameter.GetGenericParameterConstraints())
                        generic.Constraints.Add(new GenericParameterConstraint(corlib.GetType(constraint.FullName!)));
                    method.GenericParameters.Add(generic);
                    method.Parameters.Add(new ParameterDefinition(new ByReferenceType(generic)));
                }
                method.Body.Instructions.Add(Instruction.Create(OpCodes.Ldnull));
                method.Body.Instructions.Add(Instruction.Create(OpCodes.Throw));
                builder.Methods.Add(method);
            }
            corlib.Write(voidReference);
            File.AppendAllText(Path.Combine(proof, "references.txt"), "mscorlib.dll 为仅供编译副本；AwaitOnCompleted 声明来自当前 CLR AsyncVoidMethodBuilder 公开 API。生成源码必须没有调用该补全声明。\n");
        }
        return Directory.GetFiles(assemblies, "*.dll").Select(p => MetadataReference.CreateFromFile(Path.GetFileName(p) switch
        {
            "UniTask.dll" => reference,
            "mscorlib.dll" when includeVoidBuilder => voidReference,
            _ => p,
        })).ToArray();
    }

    internal static void CheckCompiledAwait(string assembly, int expectedAwaits = 2)
    {
        using var module = ModuleDefinition.ReadModule(assembly);
        var methods = module.GetTypes().SelectMany(t => t.Methods).Where(m => m.HasBody).ToArray();
        var calls = methods.SelectMany(m => m.Body.Instructions).Select(i => i.Operand).OfType<MethodReference>().ToArray();
        if (calls.Any(m => m.Name == "AwaitOnCompleted") || calls.Count(m => m.Name == "AwaitUnsafeOnCompleted") != expectedAwaits)
            throw new InvalidDataException("实际编译必须调用元数据中已有的 AwaitUnsafeOnCompleted，不能执行补全声明");
    }
}
