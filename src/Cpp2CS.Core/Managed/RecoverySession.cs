using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Model;
using Cpp2CS.Runtime;
using Cpp2CS.Ssa;

namespace Cpp2CS.Managed;

/// <summary>单个方法的机器表示与托管恢复准备结果；Problems 非空时不能作为已恢复方法使用。</summary>
public sealed record PreparedMethod(MethodRef Method, AbiValue? Return, MachineFunction Function,
    Prepare.Result? Preparation, IReadOnlyList<string> Problems);

/// <summary>同一程序共享边界表、调用识别与类型布局；每次分析生成独立的 CFG 和 SSA。</summary>
public sealed class RecoverySession
{
    public ProgramModel Model { get; }
    public FunctionTable Functions { get; }
    public IMachine Machine { get; }
    public CfgBuilder Builder { get; }
    public CallResolver Resolver { get; }
    public ManagedTypes Types { get; }
    public IManagedAbi Abi { get; }
    public ManagedCallModel Calls { get; }
    public Accessors Accessors { get; }
    public ConstructorDelegations Constructors { get; }

    public RecoverySession(ProgramModel model)
    {
        Model = model;
        Machine = model.Image.Architecture switch
        {
            Architecture.Arm64 => new Arm64Machine(model.Image),
            _ => throw new NotSupportedException($"{model.Image.Architecture} 尚无托管恢复管线"),
        };
        Functions = FunctionTable.Build(model.Image);
        Builder = new CfgBuilder(Machine, Functions);
        Resolver = new CallResolver(model, new RuntimeHelpers(Builder, RuntimeClassLayout.For(model)?.ConstructorFinished), new ManagedCopies(Machine, Functions, model));
        Types = new ManagedTypes(model, 16);
        Abi = new Arm64ManagedAbi(Types);
        Calls = new ManagedCallModel(Resolver.Resolve, Abi, Machine.Convention);
        Accessors = new Accessors(this);
        Constructors = new ConstructorDelegations(this);
    }

    /// <summary>按具体方法实参建立返回数据流、寄存器 SSA，再整理运行时样板；不生成占位方法体。</summary>
    public PreparedMethod Analyze(MethodRef method, ulong address, FunctionRange? range = null)
    {
        var function = range is null ? Builder.Build(address) : Builder.Build(address, range);
        var returnType = method.Method.ReturnType.Substitute(method.TypeArguments, method.MethodArguments);
        var returns = Abi.ClassifyReturn(returnType, out var problem);
        if (problem is not null) return new(method, null, function, null, [$"返回值 ABI: {problem}"]);
        ManagedReturns.Bind(function, returns);
        var errors = Lowering.Registers(function, Machine.Convention, Calls, null);
        if (errors.Count > 0) return new(method, returns, function, null, errors);
        var prepared = new Prepare(Resolver, Calls, Machine.Convention).Run(function);
        return new(method, returns, function, prepared, SsaCheck.Verify(function, Dominators.Compute(function)));
    }
}
