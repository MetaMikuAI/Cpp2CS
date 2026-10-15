using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

/// <summary>真实分支方法和访问器依赖全部从二进制恢复；宿主仅提供字段与引用身份，不提供业务实现。</summary>
public static class PhiNativeCheck
{
    public sealed class Root { public Parent? Parent; }
    public sealed class Parent { public Leaf? Leaf; }
    public sealed class Leaf { public Payload? Value; public Payload[]? Values; }
    public sealed class Payload;

    internal static void Run(RecoverySession session)
    {
        foreach (var (address, expected, isArray) in new[]
        {
            (0x5843760UL, "Sekai.Mysekai.FixtureController.GetColors", true),
            (0x58dc720UL, "Sekai.Mysekai.HarvestPlayerModel.get_TargetHarvestUid", false),
        })
        {
            var method = session.Model.Code[address].Single().Method;
            Require(method.ToString() == expected, "真实 case 的元数据身份");
            var prepared = session.Analyze(method, address);
            var recovered = BodyRecovery.Recover(session, prepared);
            Require(recovered.Body is { Accessors.Count: 1 }, string.Join("; ", recovered.Problems));
            var body = recovered.Body!;
            var proof = body.Accessors[0].Proof;
            var rootField = method.Method.Owner.Fields.Single(f => f.Offset == 0x10 && !f.IsStatic);
            var parent = ((DefinitionRef)rootField.Type).Definition;
            var middleField = isArray ? proof.Field.Field : parent.Fields.Single(f => f.Name == "TargetHarvestBaseView");
            var leaf = ((DefinitionRef)middleField.Type).Definition;
            var tailField = isArray ? leaf.Fields.Single(f => f.Name == "Colors") : proof.Field.Field;
            var payload = (DefinitionRef)(isArray ? ((ArrayRef)tailField.Type).Element : tailField.Type);
            Require(proof.Method.Method.Owner == (isArray ? parent : leaf), "访问器属于对应字段宿主");

            using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativePhi" + address.ToString("x"), new Version(1, 0)), "NativePhi", ModuleKind.Dll);
            var module = assembly.MainModule;
            var harness = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object);
            module.Types.Add(harness);
            var mappedTypes = new Dictionary<TypeDef, Type>
            {
                [method.Method.Owner] = typeof(Root), [parent] = typeof(Parent), [leaf] = typeof(Leaf), [payload.Definition] = typeof(Payload),
            };
            TypeReference Reference(TypeRef type)
            {
                if (type is ArrayRef a) return new ArrayType(Reference(a.Element));
                if (type is DefinitionRef d && mappedTypes.TryGetValue(d.Definition, out var host)) return module.ImportReference(host);
                return module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
            }
            var fields = new Dictionary<FieldDef, FieldReference>
            {
                [rootField] = module.ImportReference(typeof(Root).GetField(nameof(Root.Parent))),
                [middleField] = module.ImportReference(typeof(Parent).GetField(nameof(Parent.Leaf))),
                [tailField] = module.ImportReference(typeof(Leaf).GetField(isArray ? nameof(Leaf.Values) : nameof(Leaf.Value))),
            };
            var methods = new Dictionary<MethodDef, MethodDefinition>();
            foreach (var native in new[] { method, proof.Method })
            {
                Require(!native.Method.IsStatic && native.Method.Parameters.Count == 0, "测试映射要求无显式参数的实例方法");
                // 将 this 显式放在第 0 参数。调用者和真实访问器都保留恢复的完整方法体。
                var actual = new MethodDefinition(native.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(native.Method.ReturnType));
                actual.Parameters.Add(new ParameterDefinition(Reference(native.DeclaringType)));
                harness.Methods.Add(actual); methods.Add(native.Method, actual);
            }
            var emitter = new BodyEmitter(session.Types, Reference, f => fields[f.Field], m => methods[m.Method]);
            foreach (var nativeBody in new[] { proof.Body, body })
                Require(emitter.Emit(nativeBody, methods[nativeBody.Method.Method]) is null, "真实方法及依赖的 CIL 输出");
            using var stream = new MemoryStream(); assembly.Write(stream);
            var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
            var run = (Func<Root?, object?>)runtime.GetMethod(method.Method.Name)!.CreateDelegate(typeof(Func<Root?, object?>));
            var root = new Root { Parent = new Parent() };
            Require(run(root) is null, "空中间对象返回 null");
            var terminal = new Leaf();
            root.Parent.Leaf = terminal;
            Require(run(root) is null, "非空对象的空字段返回 null");
            foreach (var count in new[] { 0, 1, 3 })
            {
                object value = isArray ? Enumerable.Range(0, count).Select(_ => new Payload()).ToArray() : new Payload();
                if (isArray) terminal.Values = (Payload[])value; else terminal.Value = (Payload)value;
                Require(ReferenceEquals(run(root), value), "返回原始引用或数组，不创建副本");
                root.Parent.Leaf = null;
                Require(run(root) is null, "重复调用按当前分支取值");
                root.Parent.Leaf = terminal;
            }
            bool NullFault(Root? input) => Task.Run(() => run(input)).ContinueWith(t => t.Exception?.InnerException is NullReferenceException).GetAwaiter().GetResult();
            Require(NullFault(null) && NullFault(new Root()), "必需宿主为空时仍抛空引用异常");
            Console.WriteLine($"真实 case 0x{address:x} {method} 及 getter 0x{proof.Address:x} 执行通过：空分支、引用身份、重复读取和空引用异常；替代宿主，未验证游戏运行时");
        }
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
