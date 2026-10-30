using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class EmissionBoundaryCheck
{
    [Command("emission-boundaries", "写出检查无副作用，策略与方法局部状态互不污染", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var original = facts.Model;
        var types = new ManagedTypes(original, facts.Layouts);
        TypeDef Type(int offset, string name) => new() { Index = original.Types.Count + offset, Assembly = "Emission.Tests.dll",
            Namespace = "Tests", Name = name, Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, BaseType = types.Object };
        var module = new TypeDef { Index = original.Types.Count, Assembly = "Emission.Tests.dll", Namespace = "", Name = "<Module>",
            Token = 0, Attributes = TypeAttributes.NotPublic, IsValueType = false, IsEnum = false };
        var caller = Type(1, "Caller");
        var target = Type(2, "Target");
        MethodDef Method(int offset, TypeDef owner, string name, MethodAttributes access) => new() {
            Index = original.Methods.Count + offset, Owner = owner, Name = name, Token = 0,
            Attributes = access | MethodAttributes.Static, ImplAttributes = MethodImplAttributes.IL, Slot = -1 };
        var first = Method(0, caller, "First", MethodAttributes.Public);
        var second = Method(1, caller, "Second", MethodAttributes.Public);
        var hidden = Method(2, target, "Hidden", MethodAttributes.Private);
        first.ReturnType = second.ReturnType = types.Int32;
        caller.Methods = [first, second];
        target.Methods = [hidden];
        var assembly = new AssemblyDef { Name = caller.Assembly, AssemblyName = "Emission.Tests", Version = new(1, 0),
            Culture = "", PublicKey = [], Types = [module, caller, target] };
        var model = new ProgramModel { Image = original.Image, MetadataVersion = original.MetadataVersion,
            Assemblies = [.. original.Assemblies, assembly], Types = [.. original.Types, module, caller, target],
            Methods = [.. original.Methods, first, second, hidden], Fields = original.Fields, RuntimeTypes = original.RuntimeTypes,
            MethodSpecs = original.MethodSpecs, FieldRefs = original.FieldRefs, StringLiterals = original.StringLiterals, Code = original.Code };
        var skeleton = new Skeleton(model);
        var emitter = new FullBodyEmitter(skeleton, types);
        var local = new LocalValue(new Variable(Storage.Gpr(0), 1), types.Int32, 32);
        ManagedBody Body(MethodDef method, ulong value) => new(MethodRef.Open(method), [new(0x100,
            [new ManagedAssignment(0x100, local, new ConstantValue(value, types.Int32, 32)), new ManagedReturn(0x104, local)])]);
        var firstBody = Body(first, 7);
        var secondBody = Body(second, 11);
        var forbidden = firstBody with { Blocks = [new(0x100, [new ManagedCall(0x100, new(MethodRef.Open(hidden), null, [], false), null, false),
            new ManagedReturn(0x104, new ConstantValue(7, types.Int32, 32))])] };
        var stub = skeleton.Method(first).Body;
        var a = new Assertions();
        var problem = emitter.Check([forbidden])[forbidden];
        a.Equal(EmissionProblemKind.AccessDenied, problem.Kind, "访问失败使用稳定类别");
        a.Equal((ulong?)0x100, problem.Address, "失败保留语句地址");
        a.Equal(MethodRef.Open(first), problem.Method, "失败保留方法身份");
        a.True(problem.CanRecoverAccess, "依赖恢复不匹配可读说明");
        a.True(ReferenceEquals(stub, skeleton.Method(first).Body), "检查不替换骨架方法体");
        a.True(emitter.ExplicitInitializations.Count == 0 && emitter.AccessorCalls.Count == 0 && emitter.InlineCalls.Count == 0, "检查不写入证据");
        a.Equal(0, emitter.Check([forbidden], EmissionPolicy.Source).Count, "源码策略可检查原权限调用");
        a.Equal(1, emitter.Check([forbidden]).Count, "后续检查仍使用完整策略");
        var floating = new ConstantValue(0x3fc00000, types.Single, 32);
        var implicitScalar = firstBody with { Blocks = [new(0x100,
            [new ManagedAssignment(0x100, local, floating), new ManagedReturn(0x104, local)])] };
        a.Equal(1, emitter.Check([implicitScalar]).Count, "浮点栈值不能直接写入整数局部");
        a.Equal(1, emitter.Check([implicitScalar], EmissionPolicy.Source).Count, "源码策略也不能放过错误标量复制");
        var scalarEdge = firstBody with { Blocks = [new(0x100, [new ManagedJump(0x100, new(0x200, [new(local, floating)]))]),
            new(0x200, [new ManagedReturn(0x200, local)])] };
        a.Equal(1, emitter.Check([scalarEdge]).Count, "合流边上的复制同样核对栈类别");
        var explicitScalar = firstBody with { Blocks = [new(0x100,
            [new ManagedAssignment(0x100, local, new ConversionValue(ConvKind.Bitcast, floating, types.Int32, 32)), new ManagedReturn(0x104, local)])] };
        a.Equal(0, emitter.Check([explicitScalar]).Count, "显式同宽位重解释允许写入");
        a.Equal(0, emitter.Emit([firstBody, secondBody]).Count, "同批方法可写出");
        a.True(!ReferenceEquals(skeleton.Method(first).Body.Variables[0], skeleton.Method(second).Body.Variables[0]), "相同 IR 局部身份按方法分配");
        a.Equal(1, emitter.Emit([forbidden]).Count, "失败写出不覆盖已有方法体");
        using var stream = new MemoryStream();
        skeleton.Assembly(assembly.Name).Write(stream);
        var loaded = Assembly.Load(stream.ToArray()).GetType("Tests.Caller")!;
        a.Equal(7, loaded.GetMethod("First")!.CreateDelegate<Func<int>>()(), "失败重写后保留首方法的执行结果");
        a.Equal(11, loaded.GetMethod("Second")!.CreateDelegate<Func<int>>()(), "第二方法的局部与结果独立");
        return a.Finish("emission-boundaries");
    }
}
