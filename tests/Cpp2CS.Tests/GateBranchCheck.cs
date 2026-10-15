using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

/// <summary>真实门模型初始化：原生判空边复用对象寄存器的零值，汇合后写入布尔字段。</summary>
public static class GateBranchCheck
{
    public sealed class GateHost
    {
        public GateData? User;
        public bool HasSetupOnce;
        public bool IsSettingArea;
        public int Sentinel = 12345;
    }
    public sealed class GateData { public bool IsSettingArea; }

    internal static void Run(RecoverySession session)
    {
        const ulong address = 0x58a40a4;
        var method = session.Model.Code[address].Single().Method;
        Require(method.ToString() == "Sekai.Mysekai.MysekaiGateModel.InitializeBasicProperties", "真实 case 身份");
        var prepared = session.Analyze(method, address);
        var recovered = BodyRecovery.Recover(session, prepared);
        Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
        var body = recovered.Body!;
        var owner = method.Method.Owner;
        var user = owner.Fields.Single(f => !f.IsStatic && f.Offset == 0x10);
        var data = ((DefinitionRef)user.Type).Definition;
        var isSetting = data.Fields.Single(f => !f.IsStatic && f.Offset == 0x28);
        var hasSetup = owner.Fields.Single(f => !f.IsStatic && f.Offset == 0x80);
        var setting = owner.Fields.Single(f => !f.IsStatic && f.Offset == 0x34);
        Require(isSetting.Type == session.Types.Boolean && hasSetup.Type == session.Types.Boolean && setting.Type == session.Types.Boolean,
            "原始读写均为元数据中的布尔字段");
        Require(hasSetup.Name.Contains("HasSetupOnce") && isSetting.Name.Contains("isSettingAtHomeSite"), "真实字段的元数据身份");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("GateBranchCheck", new Version(1, 0)), "GateBranchCheck", ModuleKind.Dll);
        var module = assembly.MainModule;
        var harness = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(harness);
        TypeReference Reference(TypeRef type)
        {
            if (type == method.DeclaringType) return module.ImportReference(typeof(GateHost));
            if (type == user.Type) return module.ImportReference(typeof(GateData));
            return module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        }
        var fields = new Dictionary<FieldDef, FieldReference>
        {
            [user] = module.ImportReference(typeof(GateHost).GetField(nameof(GateHost.User))),
            [hasSetup] = module.ImportReference(typeof(GateHost).GetField(nameof(GateHost.HasSetupOnce))),
            [setting] = module.ImportReference(typeof(GateHost).GetField(nameof(GateHost.IsSettingArea))),
            [isSetting] = module.ImportReference(typeof(GateData).GetField(nameof(GateData.IsSettingArea))),
        };
        var methods = new Dictionary<MethodDef, MethodDefinition>();
        var bodies = body.Accessors.Select(a => a.Proof.Body).Append(body).DistinctBy(b => b.Method).ToArray();
        foreach (var native in bodies.Select(b => b.Method))
        {
            Require(!native.Method.IsStatic && native.Method.Parameters.Count == 0, "测试映射要求无显式参数的实例方法");
            var actual = new MethodDefinition(native.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(native.Method.ReturnType));
            actual.Parameters.Add(new ParameterDefinition(Reference(native.DeclaringType)));
            harness.Methods.Add(actual); methods.Add(native.Method, actual);
        }
        var emitter = new BodyEmitter(session.Types, Reference, f => fields[f.Field], m => methods[m.Method]);
        foreach (var nativeBody in bodies)
            Require(emitter.Emit(nativeBody, methods[nativeBody.Method.Method]) is null, "真实方法及访问器依赖的 CIL 输出");
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
        var run = (Action<GateHost?>)runtime.GetMethod(method.Method.Name)!.CreateDelegate(typeof(Action<GateHost?>));
        var host = new GateHost();
        foreach (var state in new bool?[] { null, true, false, null, false, true })
        foreach (var old in new[] { false, true })
        {
            host.User = state.HasValue ? new GateData { IsSettingArea = state.Value } : null;
            host.HasSetupOnce = old; host.IsSettingArea = !old;
            run(host);
            Require(host.HasSetupOnce == state.HasValue && host.IsSettingArea == state.GetValueOrDefault() && host.Sentinel == 12345,
                "判空汇合和两次字段写入必须与当前数据一致");
        }
        Require(Task.Run(() => run(null)).ContinueWith(t => t.Exception?.InnerException is NullReferenceException).GetAwaiter().GetResult(),
            "空 this 仍抛空引用异常");
        Console.WriteLine($"真实 case 0x{address:x} {method} 执行通过：空数据、布尔双分支、旧字段覆盖、重复调用和空 this；恢复方法 {bodies.Length} 个，替代宿主，未验证游戏运行时");
        Console.WriteLine($"字段证据：{user}；{hasSetup}；{setting}；{isSetting}");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
