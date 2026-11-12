using Cpp2CS.Model;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal enum CilComparisonStatus { Match, Mismatch, Inconclusive }
internal sealed record CilComparisonResult(CilComparisonStatus Status, int CompletedCases, int? Seed, string? Reason)
{
    public ComparisonReason ReasonKind { get; init; }
    public int NaNSkippedCases { get; init; }
    public CoverageResult? Coverage { get; init; }
    public CoverageResult? AttemptedCoverage { get; init; }
    public IReadOnlyDictionary<string, CilComparisonInstance>? Instances { get; init; }
}
internal sealed record CilComparisonInstance(bool Applicable, CilComparisonResult Result);

/// <summary>有限合成输入上的 IL 对照；泛型入口按适用实例分别执行并归并。</summary>
internal static partial class CilComparison
{
    public static CilComparisonResult Compare(MethodDefinition left, MethodDefinition right, int cases = 32, int firstSeed = 0, int stepLimit = 1_000_000, Func<CecilModel>? modelFactory = null)
        => IsGenericEntry(left) || IsGenericEntry(right)
            ? CompareGeneric(left, right, cases, firstSeed, stepLimit, modelFactory)
            : CompareInstance(left, right, cases, firstSeed, stepLimit, modelFactory);

    private static CilComparisonResult CompareInstance(MethodDefinition left, MethodDefinition right, int cases, int firstSeed, int stepLimit, Func<CecilModel>? modelFactory, bool? valueInstance = null)
    {
        if (cases <= 0 || stepLimit <= 0) return new(CilComparisonStatus.Inconclusive, 0, null, "用例数和步数必须为正") { ReasonKind = ComparisonReason.InvalidRequest };
        var completed = 0;
        var skipped = 0;
        var coverage = new ExecutionCoverage(left);
        var attempted = new ExecutionCoverage(left);
        CilComparisonResult Result(CilComparisonStatus status, int? at, string? reason, ComparisonReason kind = ComparisonReason.None) =>
            new(status, completed, at, reason) { ReasonKind = kind, NaNSkippedCases = skipped, Coverage = coverage.Result(), AttemptedCoverage = attempted.Result() };
        int? seed = null;
        try
        {
            if (valueInstance is null && (!left.HasBody || !right.HasBody || left.Body.Instructions.Count == 0 || right.Body.Instructions.Count == 0))
                throw new Unsupported("方法没有 CIL 方法体", ComparisonReason.MissingBody);
            var model = modelFactory is null ? new CecilModel(left.Module, right.Module) : modelFactory();
            var l = model.Method(left); var r = model.Method(right);
            if (valueInstance is { } value)
            {
                if (!Applicable(left, value) || !Applicable(right, value))
                    throw new Unsupported("入口泛型约束不允许本轮的类型实参", ComparisonReason.GenericDefinition);
                var argument = model.Type(value ? left.Module.TypeSystem.Int32 : left.Module.TypeSystem.Object);
                l = Close(l, argument); r = Close(r, argument);
                if (!left.HasBody || !right.HasBody || left.Body.Instructions.Count == 0 || right.Body.Instructions.Count == 0)
                    throw new Unsupported("方法没有 CIL 方法体", ComparisonReason.MissingBody);
            }
            if (!ManagedValues.ArgumentTypes(l).SequenceEqual(ManagedValues.ArgumentTypes(r)) || !l.Concrete(l.Method.ReturnType).Equals(r.Concrete(r.Method.ReturnType)))
                throw new Unsupported("两侧方法签名不对应");
            var index = new WorldIndex(model.Program, new ManagedTypes(model.Program, new ManagedStorage(model.Prepare), 8));
            var li = new CilInterpreter(model, index) { BodyModule = left.Module, StepLimit = stepLimit };
            // 逐方法对照：被测的只是 right 这一个方法体，它调用的方法两侧都执行参考程序集里的方法体。
            // 被调方法自己的恢复结果由它自己的那次对照负责；输出程序集里没恢复的方法只有占位体，不能拿来执行。
            var ri = new CilInterpreter(model, index) { BodyModule = left.Module, StepLimit = stepLimit };
            var lh = HintsOf(left, model, l); var rh = HintsOf(right, model, r);
            var hints = new Hints(lh.Constants.Concat(rh.Constants).Distinct().Order().ToArray(), lh.Types.Concat(rh.Types).Distinct().ToArray());
            for (var n = 0; n < cases; n++)
            {
                seed = checked(firstSeed + n);
                try
                {
                    li.CaseBudget = ri.CaseBudget = new ExecutionBudget(stepLimit);
                    li.Coverage = null;
                    var plan = ThrowPlanFor(left, l, li, index, hints, seed.Value);
                    var world = new World(index, seed.Value, hints, l.DeclaringType) { ThrowPlan = plan };
                    StackValue[] arguments;
                    try { arguments = Arguments(world, li, l); }
                    catch (Unsupported e) when (e.Kind is not (ComparisonReason.NaN or ComparisonReason.TypeMismatch))
                    { throw new Unsupported(e.Message, ComparisonReason.InputSynthesis); }
                    var currentCoverage = new ExecutionCoverage(left, attempted);
                    li.Coverage = currentCoverage;
                    // 同一个世界提供稳定的输入身份；各侧执行写入隔离在覆盖层。
                    var ls = li.Run(world, left, l, arguments);
                    var rs = ri.Run(world, right, r, arguments);
                    if (ls.Result is null || rs.Result is null) throw new Unsupported("执行没有结局");
                    coverage.Merge(currentCoverage);
                    completed++;
                    if (Trace.Difference(world, ls, rs) is { } difference)
                        return Result(CilComparisonStatus.Mismatch, seed, difference);
                }
                catch (Unsupported e) when (e.Kind == ComparisonReason.NaN) { skipped++; }
            }
            return completed == 0
                ? Result(CilComparisonStatus.Inconclusive, null, "所有用例均因 NaN 跳过", ComparisonReason.NaN)
                : Result(CilComparisonStatus.Match, null, null);
        }
        catch (AssemblyResolutionException e) { return Result(CilComparisonStatus.Inconclusive, seed, $"缺少引用程序集：{e.AssemblyReference}", ComparisonReason.MissingReference); }
        catch (Unsupported e) { return Result(CilComparisonStatus.Inconclusive, seed, e.Message, e.Kind); }
    }
    public static CilComparisonResult Compare(string leftAssembly, string rightAssembly, string type, string method, int cases = 32)
    {
        using var resolver = new DefaultAssemblyResolver();
        resolver.AddSearchDirectory(Path.GetDirectoryName(typeof(object).Assembly.Location)!);
        resolver.AddSearchDirectory(Path.GetDirectoryName(Path.GetFullPath(leftAssembly))!);
        resolver.AddSearchDirectory(Path.GetDirectoryName(Path.GetFullPath(rightAssembly))!);
        using var left = ModuleDefinition.ReadModule(leftAssembly, new ReaderParameters { AssemblyResolver = resolver });
        using var right = ModuleDefinition.ReadModule(rightAssembly, new ReaderParameters { AssemblyResolver = resolver });
        var l = left.GetTypes().Where(t => t.FullName == type).SelectMany(t => t.Methods).Where(m => m.Name == method).ToArray();
        var r = right.GetTypes().Where(t => t.FullName == type).SelectMany(t => t.Methods).Where(m => m.Name == method).ToArray();
        if (l.Length != 1 || r.Length != 1) return new(CilComparisonStatus.Inconclusive, 0, null, "方法不存在或名称有重载；请用 MethodDefinition 入口指定签名");
        return Compare(l[0], r[0], cases);
    }
    internal static StackValue[] Arguments(World world, CilInterpreter interpreter, MethodRef method)
    {
        return ManagedValues.ArgumentTypes(method).Select((type, position) =>
        {
            var bytes = position == 0 && !method.Method.IsStatic
                ? ManagedValues.Bytes(type is ByRefRef b ? world.ValueStorage(b.Element, "this") : world.Object(type, "this", 0), 8)
                : world.ValueBytes(type, $"arg{position}");
            if (position == 0 && !method.Method.IsStatic && ManagedValues.Bits(bytes) == 0) throw new Unsupported("无法合成非空 this");
            return interpreter.FromBytes(type, bytes);
        }).ToArray();
    }
    private static Hints HintsOf(MethodDefinition method, CecilModel model, MethodRef instance)
    {
        var constants = new SortedSet<ulong>(); var types = new List<TypeRef>();
        foreach (var instruction in method.Body.Instructions)
        {
            long? constant = instruction.OpCode.Code switch { Code.Ldc_I4_S => (sbyte)instruction.Operand, Code.Ldc_I4 => (int)instruction.Operand,
                Code.Ldc_I8 => (long)instruction.Operand, >= Code.Ldc_I4_M1 and <= Code.Ldc_I4_8 => instruction.OpCode.Code - Code.Ldc_I4_0, _ => null };
            if (constant is { } c) foreach (var value in new[] { unchecked(c - 1), c, unchecked(c + 1), unchecked(-c - 1), unchecked(-c), unchecked(-c + 1) }) constants.Add(unchecked((ulong)value));
            TypeRef? type = instruction.Operand switch
            {
                TypeReference t when instruction.OpCode.Code is Code.Isinst or Code.Castclass or Code.Box or Code.Ldtoken => instance.Concrete(model.Type(t)),
                TypeReference t when instruction.OpCode.Code == Code.Newarr => new ArrayRef(instance.Concrete(model.Type(t)), 1),
                MethodReference m when instruction.OpCode.Code == Code.Newobj => instance.Concrete(model.Type(m.DeclaringType)), _ => null
            };
            if (type is not null && !types.Contains(type)) types.Add(type);
        }
        return new(constants.ToArray(), types);
    }
}
