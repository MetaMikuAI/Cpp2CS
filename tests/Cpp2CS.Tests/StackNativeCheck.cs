using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

/// <summary>真实 OnRankUp 调用者；Int32.ToString 使用 CLR 实现，UI 调用使用记录参数的测试依赖。</summary>
public static class StackNativeCheck
{
    public sealed class TextSink
    {
        public string? Text;
        public bool Flag;
        public int Calls;
        public void SetText(string text, bool flag) { Text = text; Flag = flag; Calls++; }
    }

    internal static void Run(RecoverySession session)
    {
        const ulong address = 0x570a9a4;
        var method = session.Model.Code[address].Single().Method;
        Require(method.ToString() == "Sekai.Mysekai.UIPartsMysekaiRankGauge.OnRankUp", "真实方法身份");
        var prepared = session.Analyze(method, address);
        var recovered = BodyRecovery.Recover(session, prepared);
        Require(recovered.Body is { Accessors.Count: 0 }, string.Join("; ", recovered.Problems));
        var values = new ValueRecovery(session, prepared);
        Require(values.Stack.Objects is [{ Offset: -20, Type: var localType, Width: 32 }] && localType == session.Types.Int32,
            "栈区域由 Int32 实例调用的 this 引用约束为四字节整数");
        var calls = recovered.Body!.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().ToArray();
        Require(calls.Length == 2, "真实方法只包含整数转换和 UI 写入两个调用");
        var stringify = calls[0].Invocation.Method;
        var setText = calls[1].Invocation.Method;
        Require(stringify.DeclaringType == session.Types.Int32 && stringify.Method.Name == "ToString" && stringify.Method.Parameters.Count == 0,
            "整数转换签名");
        Require(setText.Method.ToString() == "Sekai.UI.CustomTextMesh.SetText" && setText.Method.Parameters.Select(p => p.Type)
            .SequenceEqual(new TypeRef[] { session.Types.String, session.Types.Boolean }), "UI 调用签名");
        var field = method.Method.Owner.Fields.Single(f => !f.IsStatic && f.Offset == 0x20);
        Require(field.Type == setText.DeclaringType, "UI 接收者字段类型");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeStackCheck", new Version(1, 0)), "NativeStackCheck", ModuleKind.Dll);
        var module = assembly.MainModule;
        var harness = new TypeDefinition("Checks", "RankGauge", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(harness);
        var textField = new FieldDefinition("Text", FieldAttributes.Public, module.ImportReference(typeof(TextSink)));
        harness.Fields.Add(textField);
        TypeReference Reference(TypeRef type)
        {
            if (type == method.DeclaringType) return harness;
            if (type == setText.DeclaringType) return module.ImportReference(typeof(TextSink));
            if (type is ByRefRef reference) return new ByReferenceType(Reference(reference.Element));
            return module.ImportReference(Type.GetType("System." + (type == session.Types.String ? "String" : ManagedTypes.PrimitiveName(type)), true)!);
        }
        var targets = new Dictionary<MethodDef, MethodReference>
        {
            [stringify.Method] = module.ImportReference(typeof(int).GetMethod(nameof(int.ToString), Type.EmptyTypes)),
            [setText.Method] = module.ImportReference(typeof(TextSink).GetMethod(nameof(TextSink.SetText))),
        };
        var actual = new MethodDefinition("OnRankUp", MethodAttributes.Public, module.TypeSystem.Void);
        actual.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32)); harness.Methods.Add(actual);
        var emitter = new BodyEmitter(session.Types, Reference, f => f.Field == field ? textField : throw new NotSupportedException(f.ToString()), m => targets[m.Method]);
        Require(emitter.Emit(recovered.Body, actual) is null, "真实调用者的 CIL 输出");
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.RankGauge", true)!;
        var instance = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(runtime);
        var sink = new TextSink();
        runtime.GetField("Text")!.SetValue(instance, sink);
        var invoke = runtime.GetMethod("OnRankUp")!;
        foreach (var input in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            var before = sink.Calls;
            invoke.Invoke(instance, [input]);
            Require(sink.Text == input.ToString() && !sink.Flag && sink.Calls == before + 1, "整数边界值经栈地址转换后传递到 UI 调用");
        }
        runtime.GetField("Text")!.SetValue(instance, null);
        Require(Task.Run(() => invoke.Invoke(instance, [7])).ContinueWith(t =>
            t.Exception?.InnerException is SR.TargetInvocationException { InnerException: NullReferenceException }).GetAwaiter().GetResult(), "空 UI 接收者仍失败");
        Console.WriteLine($"真实 case 0x{address:x} {method} 的恢复调用者执行通过：栈整数、边界输入、UI 实参与空接收者；ToString 使用 CLR，UI 为记录依赖，未验证原始 UI 或游戏运行时");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
