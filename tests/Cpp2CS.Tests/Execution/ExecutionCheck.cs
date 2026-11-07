using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// 执行对照（方法级差分）：恢复清单中的方法并写出 CIL，按若干种子合成输入与环境，在同一份合成内存上分别解释 CIL、
/// 在 Unicorn 中执行原机器码，比较事件序列（分配、调用及实参、抛出、返回值）与事件发生时两侧写过的内存。
/// verified：全部请求用例一致；partial：部分用例一致，其余不支持；mismatch：任一用例不一致。
/// 没有可比较用例或方法未写出均为验证不完整；对照器内部异常直接暴露。
/// </summary>
internal static partial class ExecutionCheck
{
    private const int Cases = 32;

    public static int Run(string binary, string metadata, string list, string[] options)
    {
        var caseCount = options.SkipWhile(o => o != "--cases").Skip(1).FirstOrDefault() is { } requested ? int.Parse(requested) : Cases;
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(caseCount);
        var runOptions = new RecoveryOptions();
        if (options.SkipWhile(o => o != "--fact-cache-file").Skip(1).FirstOrDefault() is { } cache)
            runOptions = runOptions with { FactCacheFile = Path.GetFullPath(cache) };
        var verbose = options.Contains("--verbose");
        // 每个方法的墙钟上限（秒）；超时的用例记为不可检查，不计入一致。
        TimeSpan? timeLimit = options.SkipWhile(o => o != "--time-limit").Skip(1).FirstOrDefault() is { } seconds
            ? TimeSpan.FromSeconds(double.Parse(seconds, System.Globalization.CultureInfo.InvariantCulture)) : null;
        var facts = FactsBuilder.Build(binary, metadata, options: runOptions);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var targets = ReadList(facts, list, 0, 1);
        var decompiler = new MethodDecompiler(facts, types);
        var results = targets.Select(t => t.Recover(decompiler)).ToArray();
        // 依赖闭包与 recover 相同：透明构造（内联证明）的被调构造函数一并写出，对照时透明执行。
        var dependencies = new List<MethodRecoveryResult>();
        DependencyClosure.Complete(results, dependencies, results.GroupBy(r => r.Method.Method).ToDictionary(g => g.Key, g => g.First()), new Summaries(decompiler));
        var all = results.Concat(dependencies).ToArray();
        var skeleton = new Skeleton(facts.Model);
        skeleton.ApplyDeclarations(all);
        var emitter = new BodyEmitter(skeleton, types, diagnostics: runOptions.Diagnostics);
        var bodies = all.Where(r => r.Body is not null).Select(r => r.Body!).ToArray();
        var problems = emitter.Check(bodies, EmissionPolicy.Recovered);
        DependencyClosure.Validate(all, problems);
        new BodyPublication(emitter).Publish(bodies.Where(b => !problems.ContainsKey(b)), EmissionPolicy.Recovered);
        var index = new WorldIndex(facts, types);
        var cecil = new CecilModel(facts.Model, skeleton);
        var interpreter = new CilInterpreter(cecil, index);
        // 解释导出工程编译出的 C#，而不是恢复的 CIL；比较模型不变。
        if (options.SkipWhile(o => o != "--csharp").Skip(1).FirstOrDefault() is { } compiled)
        {
            cecil.UseCompiled(compiled, Option(options, "--csharp-assembly"), Option(options, "--csharp-references"));
            interpreter.SetAccessors(method => cecil.Compiled!.AutoAccessor(skeleton.Method(method)));
        }
        var written = all.GroupBy(r => r.Method.Method).ToDictionary(g => g.Key, g => g.First());
        // 内联目标的实参可能提到调用方的类型参数，而 CIL 的 VAR/MVAR 只引用所在类型和方法自己的参数（ECMA-335 II.7.1）：按原生见证闭合后才能写成实例体。
        interpreter.SetInline(emitter, skeleton, method => decompiler.Summary(WithWitnesses(method)) is { Body: { } own, Entry: var entry }
            && written.GetValueOrDefault(method.Method)?.Entry != entry ? emitter.BuildInstance(own) : null);
        using var machine = new NativeMachine(facts);
        var verdicts = new Dictionary<ExecutionVerdict, int>();
        var output = options.SkipWhile(o => o != "--output").Skip(1).FirstOrDefault();
        using var table = output is null ? null : new StreamWriter(output) { AutoFlush = true };
        for (var i = 0; i < results.Length; i++)
        {
            var result = results[i];
            var name = $"0x{result.Entry:x} {result.Method}";
            var outcome = result.Body is null
                ? new Outcome(ExecutionVerdict.NotWritten, 0, 0, $"；{result.Holes.FirstOrDefault()?.Reason ?? "没有方法体"}")
                : problems.TryGetValue(result.Body, out var problem)
                    ? new Outcome(ExecutionVerdict.NotWritten, 0, 0, $"；{problem}")
                    : Guarded(targets[i].Instance, skeleton, cecil, interpreter, machine, index, verbose, caseCount, result.Entry, timeLimit);
            verdicts[outcome.Verdict] = verdicts.GetValueOrDefault(outcome.Verdict) + 1;
            table?.WriteLine($"0x{result.Entry:x}\t{result.Method}\t{outcome.Verdict.Label()}\t{outcome.Matches}/{caseCount}\t{outcome.Coverage:F2}\t{outcome.Detail.TrimStart('；')}");
            if (outcome.Verdict != ExecutionVerdict.Verified) Console.WriteLine($"  {outcome.Verdict.Label()} {name}{outcome.Detail}");
        }
        Console.WriteLine($"执行对照：写出 {results.Count(r => r.Body is not null && !problems.ContainsKey(r.Body))}/{results.Length}，"
            + string.Join("，", verdicts.OrderBy(p => p.Key).Select(p => $"{p.Key.Label()} {p.Value}")));
        return ExecutionVerdicts.ExitCode(verdicts.Keys);
    }


    private static string Option(string[] options, string name) =>
        options.SkipWhile(o => o != name).Skip(1).FirstOrDefault() ?? throw new ArgumentException($"缺少 {name}");

    private sealed class Summaries(MethodDecompiler decompiler) : IMethodResults
    {
        public MethodRecoveryResult Recover(MethodRef method, ulong entry) => decompiler.Recover(method, entry);
        public MethodRecoveryResult RecoverInstance(MethodRef method, ulong entry) => decompiler.RecoverInstance(method, entry);
        public MethodRecoveryResult RecoverDefinition(MethodDef method) => decompiler.RecoverDefinition(method);
    }

    /// <summary>Reason：不可检查时的主要原因（用例最多的一类，去掉具体类型与方法名以便汇总）。</summary>
    private sealed record Outcome(ExecutionVerdict Verdict, int Matches, double Coverage, string Detail, string Reason = "", int ThrowCases = 0);

    /// <summary>对照器自身出错时这个方法没有结论，记为 checker-failed 并继续；一个方法不能让整轮对照中断。</summary>
    private static Outcome Guarded(MethodRef tested, Skeleton skeleton, CecilModel cecil, CilInterpreter interpreter, NativeMachine machine, WorldIndex index, bool verbose, int caseCount = Cases, ulong? nativeEntry = null, TimeSpan? timeLimit = null)
    {
        try { return Check(tested, skeleton, cecil, interpreter, machine, index, verbose, caseCount, nativeEntry, timeLimit); }
        catch (Exception e) when (e is not OutOfMemoryException)
        {
            return new Outcome(ExecutionVerdict.CheckerFailed, 0, 0, $"；{e.GetType().Name}：{e.Message}（{e.StackTrace?.Split('\n').FirstOrDefault()?.Trim()}）");
        }
    }

    private static Outcome Check(MethodRef tested, Skeleton skeleton, CecilModel cecil, CilInterpreter interpreter, NativeMachine machine, WorldIndex index, bool verbose, int caseCount = Cases, ulong? nativeEntry = null, TimeSpan? timeLimit = null)
    {
        var deadline = timeLimit is { } limit ? DateTime.UtcNow + limit : (DateTime?)null;
        cecil.Context = tested;
        var definition = skeleton.Method(tested.Method);
        var entry = nativeEntry ?? tested.Method.Address;
        var function = index.Facts.Code.At(entry)!;
        Aapcs64Classifier.Signature signature;
        try { signature = index.StructAbi.Signature(tested); }
        catch (Unsupported e) { return new Outcome(ExecutionVerdict.NotCheckable, 0, 0, $"；{e.Message}", e.Message); }
        // 世界按恢复体的提示生成，和 CIL 的对照用同一批输入。
        var hints = HintsOf(definition, cecil);
        var executed = definition;
        if (cecil.Compiled is { } compiled)
        {
            if (compiled.Body(definition) is not { } body) return new Outcome(ExecutionVerdict.NotCheckable, 0, 0, "；C# 编译结果里没有对应方法", "C# 编译结果里没有对应方法");
            executed = body;
            interpreter.UseCompiled(body, definition, tested);
        }
        FieldRef[] statics;
        ThrowPlan?[] throwPlans;
        machine.Covered.Clear();
        try
        {
            statics = interpreter.StaticFields(executed, tested).Distinct().ToArray();
            throwPlans = ThrowPlans(tested, executed, cecil, interpreter, index, caseCount: caseCount);
        }
        catch (Unsupported e) when (cecil.Compiled is not null)
        {
            return new Outcome(ExecutionVerdict.NotCheckable, 0, 0, $"；{e.Message}", e.Message);
        }
        var throwCases = 0;
        var matches = 0;
        var mismatches = new List<string>();
        var unsupported = new Dictionary<string, int>();
        HashSet<Instruction>? arrayAccesses = Environment.GetEnvironmentVariable("EXECUTION_ARRAY_COVERAGE") == "1" ? [] : null;
        HashSet<Instruction> arrayInstructions = arrayAccesses is null ? [] : definition.Body.Instructions.Where(i => i.OpCode.Code is Code.Ldelem_Any or Code.Stelem_Any).ToHashSet();
        var arrayCases = 0;
        var returns = 0;
        for (var seed = 0; seed < caseCount; seed++)
        {
            if (deadline is { } end && DateTime.UtcNow > end)
            {
                unsupported[World.TimeLimitReason] = unsupported.GetValueOrDefault(World.TimeLimitReason) + caseCount - seed;
                break;
            }
            var world = new World(index, seed, hints, InitializedOwner(tested)) { ThrowPlan = throwPlans[seed], Deadline = deadline };
            try
            {
                foreach (var field in statics) world.PrepareStatic(field);
                var (bits, values) = Arguments(world, interpreter, tested, signature);
                var cil = interpreter.Run(world, executed, tested, values);
                var native = machine.Run(world, tested, signature, bits, cil.Callees, entry);
                if (arrayAccesses is not null)
                {
                    var completed = cil.ArrayAccesses!.Where(arrayInstructions.Contains).ToArray();
                    arrayAccesses.UnionWith(completed);
                    if (completed.Length > 0) arrayCases++;
                    if (cil.Result?.StartsWith("return ", StringComparison.Ordinal) == true) returns++;
                }
                if (native.PlannedThrowReached && cil.PlannedThrowReached) throwCases++;
                if (Environment.GetEnvironmentVariable("EXECUTION_TRACE") == $"0x{tested.Method.Address:x}")
                    Console.WriteLine($"    种子 {seed}：{string.Join(" | ", cil.Events.Select(e => e.Text))}");
                if (Trace.Difference(world, native, cil) is { } difference)
                {
                    mismatches.Add($"种子 {seed}：{difference}");
                    if (verbose)
                    {
                        Console.WriteLine($"    种子 {seed} 原生：{string.Join(" | ", native.Events.Select(e => e.Text))}");
                        Console.WriteLine($"    种子 {seed} CIL ：{string.Join(" | ", cil.Events.Select(e => e.Text))}");
                    }
                }
                else matches++;
            }
            catch (Unsupported e)
            {
                unsupported[e.Message] = unsupported.GetValueOrDefault(e.Message) + 1;
            }
        }
        var covered = machine.Covered.Sum(b => (long)b.Size);
        if (arrayAccesses is not null)
            Console.WriteLine($"ARRAY_COVERAGE\t0x{tested.Method.Address:x}\t{tested}\t{arrayAccesses.Count(i => i.OpCode.Code == Code.Ldelem_Any)}\t{arrayInstructions.Count(i => i.OpCode.Code == Code.Ldelem_Any)}\t{arrayAccesses.Count(i => i.OpCode.Code == Code.Stelem_Any)}\t{arrayInstructions.Count(i => i.OpCode.Code == Code.Stelem_Any)}\t{arrayCases}\t{returns}\t{caseCount}");
        var coverage = (double)Math.Min(covered, (long)function.Size) / function.Size;
        var detail = (mismatches.Count > 0 ? $"；不一致 {mismatches.Count}，首例 {mismatches[0]}" : "")
            + (unsupported.Count > 0 ? $"；不可检查 {unsupported.Values.Sum()}（{string.Join("；", unsupported.OrderByDescending(u => u.Value).Take(3).Select(u => $"{u.Value}× {u.Key}"))}）" : "");
        var verdict = ExecutionVerdicts.Classify(caseCount, matches, mismatches.Count);
        var reason = unsupported.Count > 0 ? Category(unsupported.MaxBy(u => u.Value).Key) : "";
        return new Outcome(verdict, matches, coverage, detail, reason, throwCases);
    }

    /// <summary>不可检查原因的类别：去掉其中的类型、方法、地址等具体部分。</summary>
    private static string Category(string reason)
    {
        var text = System.Text.RegularExpressions.Regex.Replace(reason, @"0x[0-9a-f]+", "#");
        // 原因的格式多为"描述 具体对象"或"描述 具体对象：细节"：类型名、方法名中含有 '.'、'<'，按词去掉
        var words = text.Split(' ').Select(w => w.Contains('.') || w.Contains('<') || w.Contains('`') ? "…" : w);
        return string.Join(' ', words);
    }

    /// <summary>
    /// 被测方法执行时必定已初始化的类型（按解释器采用的触发点，见 CilInterpreter.Invoke）：自身的静态构造正在运行；
    /// 静态方法、构造函数（经 newobj 时分配函数已初始化，经 base(...) 时调用前已初始化）与值类型的方法在进入前初始化；
    /// 精确初始化的类型有实例即已初始化。beforefieldinit 引用类型的实例方法保留尚未初始化的情形（this 可能是子类的实例）。
    /// </summary>
    private static TypeRef? InitializedOwner(MethodRef tested) =>
        tested.Method.IsStatic || tested.Method.Name == ".ctor" || World.Precise(tested.DeclaringType)
            || tested.DeclaringType is DefinitionRef { Definition.IsValueType: true } ? tested.DeclaringType : null;

    /// <summary>方法 IL 中的整数常量（及其 ±1、相反数 ±1）与类型操作数（isinst、newobj、box、newarr、ldtoken）。</summary>
    private static Hints HintsOf(Mono.Cecil.MethodDefinition method, CecilModel cecil)
    {
        var constants = new SortedSet<ulong>();
        var types = new List<TypeRef>();
        foreach (var instruction in method.Body.Instructions)
        {
            long? constant = instruction.OpCode.Code switch
            {
                Code.Ldc_I4_S => (sbyte)instruction.Operand, Code.Ldc_I4 => (int)instruction.Operand, Code.Ldc_I8 => (long)instruction.Operand,
                >= Code.Ldc_I4_M1 and <= Code.Ldc_I4_8 => instruction.OpCode.Code - Code.Ldc_I4_0,
                _ => null,
            };
            // 相反数也取：x == -3 常被写成 x + 3 == 0
            if (constant is { } c)
                foreach (var v in new[] { c - 1, c, c + 1, -c - 1, -c, -c + 1 }) constants.Add(unchecked((ulong)v));
            try
            {
                TypeRef? type = instruction.Operand switch
                {
                    Mono.Cecil.TypeReference t when instruction.OpCode.Code is Code.Isinst or Code.Castclass or Code.Box or Code.Ldtoken => cecil.Type(t),
                    Mono.Cecil.TypeReference t when instruction.OpCode.Code == Code.Newarr => new ArrayRef(cecil.Type(t), 1),
                    Mono.Cecil.MethodReference m when instruction.OpCode.Code == Code.Newobj => cecil.Method(m).DeclaringType,
                    _ => null,
                };
                if (type is not null && !types.Contains(type)) types.Add(type);
            }
            catch (Unsupported) { }
        }
        return new Hints(constants.ToArray(), types);
    }

    /// <summary>按 ABI 合成实参：this 为声明类型（或其具体子类）的对象，值类型的 this 为指向数据的指针；其余参数按类型取值。</summary>
    private static (List<byte[]> Bits, List<StackValue> Values) Arguments(World world, CilInterpreter interpreter, MethodRef method, Aapcs64Classifier.Signature signature)
    {
        var bits = new List<byte[]>();
        var values = new List<StackValue>();
        var types = StructAbi.ArgumentTypes(method);
        for (var position = 0; position < types.Length; position++)
        {
            var type = types[position];
            byte[] bytes;
            if (position == 0 && signature.This is not null)
            {
                var value = type is ByRefRef b ? world.ValueStorage(b.Element, "this") : world.Object(type, "this", 0);
                if (value == 0 && type is DefinitionRef { Definition: { IsInterface: false, IsValueType: false } } declared)
                    value = world.Instance(declared, "this", 0);
                if (value == 0) throw new Unsupported($"没有可作为 this 的 {type} 对象");
                bytes = StructAbi.Bytes(value, 8);
            }
            else bytes = world.ValueBytes(type, $"arg{position}");
            bits.Add(bytes);
            values.Add(interpreter.FromBytes(type, bytes));
        }
        return (bits, values);
    }

    /// <summary>类型参数代入入口的原生见证；没有见证的参数保持原样。</summary>
    private static MethodRef WithWitnesses(MethodRef method)
    {
        TypeRef Close(TypeRef type) => type switch
        {
            GenericParameterRef { Binding.Layout: { } layout } => layout,
            DefinitionRef { Arguments.Count: > 0 } d => d with { Arguments = d.Arguments.Select(Close).ToArray() },
            ArrayRef a => a with { Element = Close(a.Element) },
            PointerRef p => p with { Element = Close(p.Element) },
            ByRefRef r => r with { Element = Close(r.Element) },
            _ => type,
        };
        return method with { TypeArguments = method.TypeArguments.Select(Close).ToArray(), MethodArguments = method.MethodArguments.Select(Close).ToArray() };
    }

    /// <summary>方法清单（制表符分隔，第 addressColumn 列为十六进制入口、第 nameColumn 列为方法名，两者都要对得上）。</summary>
    private static RecoveryTarget[] ReadList(ProgramFacts facts, string path, int addressColumn, int nameColumn)
    {
        return File.ReadLines(path).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t')).Select(f =>
        {
            var address = Convert.ToUInt64(f[addressColumn], 16);
            return RecoveryTarget.Find(facts, address, f[nameColumn]);
        }).ToArray();
    }
}
