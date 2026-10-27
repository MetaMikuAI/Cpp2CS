using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Mono.Cecil;

namespace Cpp2CS.Tests;

internal static class ScopeForwardingCheck
{
    [Command("scope-forwarding", "范围外声明转发至当前源码程序集的类型身份", Gate = Gate.Unit)]
    public static int Run()
    {
        using var module = ModuleDefinition.CreateModule("Scope.Dependency", ModuleKind.Dll);
        var restored = new TypeDefinition("Test", "Restored", Mono.Cecil.TypeAttributes.Public, module.ImportReference(typeof(object)));
        var nested = new TypeDefinition("", "Nested", Mono.Cecil.TypeAttributes.NestedPublic, module.ImportReference(typeof(object)));
        restored.NestedTypes.Add(nested);
        module.Types.Add(restored);
        var container = new TypeDefinition("Test", "Container`1", Mono.Cecil.TypeAttributes.Public, module.ImportReference(typeof(object)));
        container.GenericParameters.Add(new("T", container));
        module.Types.Add(container);
        var closed = new GenericInstanceType(container);
        closed.GenericArguments.Add(restored);
        var dependency = new TypeDefinition("Test", "Dependency", Mono.Cecil.TypeAttributes.Public, module.ImportReference(typeof(object)));
        module.Types.Add(dependency);
        foreach (var (name, access, parameter) in new[]
        {
            ("Accept", Mono.Cecil.MethodAttributes.Public, (TypeReference)restored),
            ("AcceptInternal", Mono.Cecil.MethodAttributes.Assembly, restored),
            ("AcceptPrivate", Mono.Cecil.MethodAttributes.Private, restored),
            ("AcceptProtected", Mono.Cecil.MethodAttributes.Family, restored),
            ("AcceptNested", Mono.Cecil.MethodAttributes.Public, nested),
            ("AcceptGeneric", Mono.Cecil.MethodAttributes.Public, closed),
        })
        {
            var accept = new MethodDefinition(name, access | Mono.Cecil.MethodAttributes.Static, module.ImportReference(typeof(void)));
            accept.Parameters.Add(new ParameterDefinition(parameter));
            accept.Body.Instructions.Add(Mono.Cecil.Cil.Instruction.Create(Mono.Cecil.Cil.OpCodes.Ret));
            dependency.Methods.Add(accept);
        }
        ScopeCompilationReferences.Rewrite(module, [restored, container], "Scope.Source");
        using var stream = new MemoryStream();
        module.Write(stream);
        CSharpCompilation Compile(string statements) => CSharpCompilation.Create("Scope.Source", [CSharpSyntaxTree.ParseText(
            "namespace Test { public class Container<T> {} public class Restored { public class Nested {} public void Call() { " + statements + " } } }")],
            [MetadataReference.CreateFromImage(stream.ToArray()), MetadataReference.CreateFromFile(typeof(object).Assembly.Location)],
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
        var a = new Assertions();
        foreach (var statements in new[] { "Dependency.Accept(this);", "Dependency.AcceptInternal(this);",
            "Dependency.AcceptNested(new Nested());", "Dependency.AcceptGeneric(new Container<Restored>());" })
        {
            var errors = Compile(statements).GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).ToArray();
            a.True(errors.Length == 0, "类型转发绑定源码声明：" + string.Join("; ", errors.Select(d => d.ToString())));
        }
        foreach (var name in new[] { "AcceptPrivate", "AcceptProtected" })
        {
            var errors = Compile($"Dependency.{name}(this);").GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).ToArray();
            a.True(errors.Length > 0 && errors.All(d => d.Id is "CS0122" or "CS0117"), name + " 仍不可访问");
        }
        return a.Finish("scope-forwarding");
    }
}
