using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>F9 的一层定向依赖：只从范围内已确认的访问权限失败出发，不递归扩张普通调用。</summary>
public sealed class AccessorRecovery
{
    public sealed record Access(ManagedBody Body, ulong Address, ManagedValue Value, bool Write, FieldAccessor[] Candidates);
    public MethodRecoveryResult[] Targets { get; }
    public List<MethodRecoveryResult> Dependencies { get; } = [];
    public List<Access> Accesses { get; } = [];
    public Dictionary<ManagedBody, string> Problems { get; private set; }
    public Dictionary<MethodDef, FieldAccessor> Candidates { get; } = [];
    public int PropertyCount { get; }
    public Dictionary<MethodDef, string> Inspected { get; } = [];
    public Dictionary<MethodDef, MethodRecoveryResult?> Synthesized { get; } = [];
    public Dictionary<MethodDef, FieldAccessor> LanguageAccessors { get; } = [];
    /// <summary>
    /// 泛型类型封闭实例上的访问器（List&lt;T&gt;.Enumerator.get_Current、Nullable&lt;T&gt;.get_HasValue……）：按实例的原生代码恢复并认出严格单字段形态。
    /// 不写出方法体（泛型定义的 CIL 不能用某个实例的类型表达），不经证据库；执行对照独立核对实例原生代码的形状后按字段访问执行。
    /// </summary>
    public HashSet<FieldAccessor> GenericAccessors { get; } = [];
    /// <summary>内联认回的候选（<see cref="InlineRecognition"/>）：越权字段所在类型上的小方法，各自恢复、写出并独立验证。</summary>
    public Dictionary<MethodDef, MethodRecoveryResult> InlineCandidates { get; } = [];
    private readonly Dictionary<ManagedBody, MethodDef[]> inlineOptions = new(ReferenceEqualityComparer.Instance);
    /// <summary>按普查建模的泛型内联被调方法（GenericInline）：方法体由同一定义的另一实例代换类型得到，不写出、不需要执行证据。</summary>
    private readonly Dictionary<ManagedBody, InlineRecognition.Callee[]> genericInline = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<ManagedBody, string> dependencyProblems = new(ReferenceEqualityComparer.Instance);
    private readonly ProgramFacts facts;

    public AccessorRecovery(ProgramFacts facts, ManagedTypes types, MethodRecovery recovery, BodyEmitter emitter, MethodRecoveryResult[] targets, IReadOnlySet<string>? rejected = null, bool useLanguage = true)
    {
        this.facts = facts;
        Targets = targets;
        Problems = emitter.Emit(targets.Where(r => r.Body is not null).Select(r => r.Body!));
        var recovered = targets.ToDictionary(r => r.Method.Method);
        var scope = recovered.Keys.ToHashSet();
        var properties = facts.Model.Types.SelectMany(t => t.Properties.SelectMany(p => new[] { (Method: p.Getter, Write: false), (Method: p.Setter, Write: true) }))
            .Where(p => p.Method is not null).Select(p => (Method: p.Method!, p.Write)).Distinct().ToArray();
        PropertyCount = properties.Length;
        var byOwner = properties.ToLookup(p => p.Method.Owner);
        var language = useLanguage ? AutoPropertyAccessor.Candidates(types) : [];
        var shapes = new Dictionary<MethodDef, FieldAccessor?>();
        FieldAccessor? Inspect(MethodDef method, bool write)
        {
            if (shapes.TryGetValue(method, out var shape)) return shape;
            if (!recovered.TryGetValue(method, out var result) && method.Address != 0 && method.GenericParameters.Count == 0
                && method.Owner.GenericParameters.Count == 0 && facts.Code.RegionOf(method.Address) == CodeRegion.Managed)
                recovered[method] = result = recovery.Recover(new MethodRef(method, [], []), method.Address);
            shape = result?.Body is { } body ? FieldAccessor.Recognize(body, write, types) : null;
            Inspected[method] = result?.Body is null ? "访问器有洞或无代码" : shape is null ? "不满足严格形态" : "严格形态";
            if ((shape is null || method.Address == 0) && language.TryGetValue(method, out var automatic)
                && (rejected is null || !rejected.Contains(automatic.Method.ToString()))
                && (method.Address == 0 || facts.Code.RegionOf(method.Address) == CodeRegion.Managed))
            {
                shape = automatic;
                LanguageAccessors[method] = automatic;
                // 已有普通恢复体优先，包括严格形态未认出的转换；它仍须独立执行验证。
                if (result?.Body is null)
                {
                    Synthesized[method] = result;
                    recovered[method] = new(automatic.Method, method.Address, AutoPropertyAccessor.Synthesize(automatic), []);
                }
                Inspected[method] = result?.Body is null ? "语言定义合成" : "语言定义，保留普通恢复体";
            }
            return shapes[method] = shape;
        }
        Dictionary<MethodRef, ulong>? instances = null;
        var genericShapes = new Dictionary<MethodRef, FieldAccessor?>();
        FieldAccessor? InspectInstance(MethodDef method, DefinitionRef owner, bool write)
        {
            var instance = new MethodRef(method, owner.Arguments, []);
            if (genericShapes.TryGetValue(instance, out var known)) return known;
            // 先只认 getter：执行对照核对的是“单条读取 + 返回”的原生形状。
            if (write) return genericShapes[instance] = null;
            instances ??= InstanceAddresses(facts);
            // 引用类型实参共享代码，注册表登记为 object 实例；按具体实例恢复（单字段读取与 T 无关），代码取共享实例的。
            var shared = new MethodRef(method, owner.Arguments.Select(a => ManagedTypes.IsReferenceType(a) ? (TypeRef)types.Object : a).ToArray(), []);
            var found = instances.TryGetValue(instance, out var entry) || instances.TryGetValue(shared, out entry);
            var recoveredInstance = found ? recovery.RecoverInstance(instance, entry) : null;
            var shape = recoveredInstance?.Body is { } body ? FieldAccessor.Recognize(body, write, types) : null;
            if (shape is not null) GenericAccessors.Add(shape);
            return genericShapes[instance] = shape;
        }
        // EmptyArray<T>.Value 只经 Array.Empty<T>() 公开（原生代码内联了它；empty-census 核对全部实例都只返回该字段）。
        var arrayEmpty = facts.Model.Types.FirstOrDefault(t => t.FullName == "System.Array")?.Methods
            .FirstOrDefault(m => m is { Name: "Empty", IsStatic: true, GenericParameters.Count: 1, Parameters.Count: 0 });
        foreach (var result in targets.Where(r => r.Body is not null && Problems.GetValueOrDefault(r.Body)?.StartsWith("访问权限 ", StringComparison.Ordinal) == true))
            foreach (var (address, value, write) in Fields(result.Body!))
            {
                var field = FieldAccessor.FieldOf(value)!;
                if (ManagedAccess.Field(types, result.Method.Method.Owner, field, FieldAccessor.ReceiverType(value))) continue;
                var owners = new List<DefinitionRef>();
                for (TypeRef? t = field.DeclaringType; t is DefinitionRef d; t = d.Definition.BaseType?.Substitute(d.Arguments, [])) owners.Add(d);
                var candidates = owners.SelectMany(o => byOwner[o.Definition].Where(p => p.Write == write)
                        .Select(p => o.Arguments.Count == 0 ? Inspect(p.Method, write) : InspectInstance(p.Method, o, write)))
                    .OfType<FieldAccessor>().Where(a => a.Matches(types, result.Method.Method.Owner, value, write)).OrderBy(a => a.Method.Method.Index).ToArray();
                if (!write && arrayEmpty is not null && value is StaticFieldValue { Field.DeclaringType: DefinitionRef { Definition.FullName: "System.EmptyArray", Arguments: [var element] } } empty
                    && empty.Field.Field.Name == "Value")
                {
                    var accessor = new FieldAccessor(new MethodRef(arrayEmpty, [], [element]), field, value.Type, value.Width, false);
                    if (accessor.Matches(types, result.Method.Method.Owner, value, write))
                    {
                        candidates = [accessor];
                        GenericAccessors.Add(accessor);
                    }
                }
                Accesses.Add(new(result.Body!, address, value, write, candidates));
                // 泛型方法实例（Array.Empty<T>）不写出方法体，由执行对照按普查建模。
                foreach (var candidate in candidates.Where(c => c.Method.TypeArguments.Count == 0 && c.Method.MethodArguments.Count == 0)) Candidates[candidate.Method.Method] = candidate;
            }
        var inlineShapes = new Dictionary<MethodDef, MethodRecoveryResult?>();
        MethodRecoveryResult? InlineShape(MethodDef method)
        {
            if (inlineShapes.TryGetValue(method, out var known)) return known;
            if (!recovered.TryGetValue(method, out var result))
                recovered[method] = result = recovery.Recover(new MethodRef(method, [], []), method.Address);
            return inlineShapes[method] = result.Body is { Regions.Count: 0 } body && body.Blocks.Sum(b => b.Statements.Count) <= 40 ? result : null;
        }
        foreach (var result in targets.Where(r => r.Body is not null && Problems.GetValueOrDefault(r.Body)?.Split(' ')[0] is "访问权限" or "只读实例字段"))
        {
            var owner = result.Method.Method.Owner;
            var methods = new List<MethodDef>();
            foreach (var type in InaccessibleOwners(types, owner, result.Body!).Distinct())
                foreach (var method in type.Methods.Where(m => m.Address != 0 && m.GenericParameters.Count == 0 && m.Name != ".cctor" && (m.Name != ".ctor" || type.IsValueType)
                    && rejected?.Contains(new MethodRef(m, [], []).ToString()) != true
                    && m.Parameters.Count <= 3 && facts.Code.RegionOf(m.Address) == CodeRegion.Managed && ManagedAccess.Method(types, owner, new MethodRef(m, [], []), null)))
                    if (InlineShape(method) is { } shape)
                    {
                        methods.Add(method);
                        InlineCandidates[method] = shape;
                    }
            if (methods.Count > 0) inlineOptions[result.Body!] = methods.ToArray();
            if (GenericCallees(types, owner, recovery, result.Body!).ToArray() is { Length: > 0 } generic) genericInline[result.Body!] = generic;
        }
        // 试跑认回（假定候选都已验证），只留下真正被某个目标用到的被调方法：其余候选不写出、不验证。
        var used = new HashSet<MethodDef>();
        foreach (var (body, options) in inlineOptions.ToArray())
        {
            var owner = body.Method.Method.Owner;
            var trial = RecognizeInline(types, owner, body, options.Select(m => Callee(InlineCandidates[m])).Concat(genericInline.GetValueOrDefault(body) ?? []).ToArray());
            var calls = trial.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Where(c => c.Inlined).Select(c => c.Invocation.Method.Method).ToHashSet();
            if (calls.Count == 0) inlineOptions.Remove(body);
            else { inlineOptions[body] = options.Where(calls.Contains).ToArray(); used.UnionWith(calls); }
        }
        foreach (var method in InlineCandidates.Keys.Where(m => !used.Contains(m)).ToArray()) InlineCandidates.Remove(method);
        // 有洞的目标访问器也只有在被确切依赖时才替换；未匹配的普查候选不扩大写出范围。
        for (var i = 0; i < Targets.Length; i++)
            if (Candidates.ContainsKey(Targets[i].Method.Method) && Synthesized.ContainsKey(Targets[i].Method.Method))
                Targets[i] = recovered[Targets[i].Method.Method];
        foreach (var method in LanguageAccessors.Keys.Where(m => !Candidates.ContainsKey(m)).ToArray())
        {
            LanguageAccessors.Remove(method);
            Synthesized.Remove(method);
        }
        // 只写出确切匹配过越权字段的候选，而不是为找候选检查过的所有属性。
        Dependencies.AddRange(Candidates.Keys.Where(m => !scope.Contains(m)).OrderBy(m => m.Index).Select(m => recovered[m]));
        Dependencies.AddRange(InlineCandidates.Keys.Where(m => !scope.Contains(m) && !Candidates.ContainsKey(m)).OrderBy(m => m.Index).Select(m => InlineCandidates[m]));
        // 候选扫描缓存不代表已写出。透明调用的依赖必须加入实际输出集合，并继续补齐其透明依赖。
        var scheduled = All.Select(r => r.Method.Method).ToHashSet();
        var pending = new Queue<MethodRecoveryResult>(All);
        while (pending.TryDequeue(out var current))
        {
            if (current.Body is not { } body) continue;
            foreach (var method in TransparentConstructors(body).Distinct().OrderBy(m => m.Index))
            {
                if (!scheduled.Add(method)) continue;
                if (!recovered.TryGetValue(method, out var dependency))
                    recovered[method] = dependency = recovery.Recover(new MethodRef(method, [], []), method.Address);
                Dependencies.Add(dependency);
                pending.Enqueue(dependency);
            }
        }
        // 全程序 37,092 类型中有 9 个无属性关联的显式接口访问器（accessor-owner-census）。
        // 不修补范围外骨架；依赖所在源文件已知会触发 CS0683 时保留失败，不把仅 CIL/执行通过当成可用。
        foreach (var result in Dependencies.Where(r => r.Body is not null))
            if (emitter.AccessorDependencyProblem(result.Method.Method) is { } problem) dependencyProblems[result.Body!] = problem;
        foreach (var pair in emitter.Emit(Dependencies.Where(r => r.Body is not null && !dependencyProblems.ContainsKey(r.Body)).Select(r => r.Body!))) Problems[pair.Key] = pair.Value;
        foreach (var pair in dependencyProblems) Problems[pair.Key] = pair.Value;
        CheckTransparent();
        foreach (var method in Candidates.Keys.ToArray())
            if (Problems.ContainsKey(recovered[method].Body!)) Candidates.Remove(method);
        foreach (var method in InlineCandidates.Keys.ToArray())
            if (Problems.ContainsKey(InlineCandidates[method].Body!)) InlineCandidates.Remove(method);
        // 合成目标尚未经过批量写出，必须在允许认回之前接受相同的 L4 检查。
        foreach (var pair in emitter.Emit(Targets.Where(r => Synthesized.ContainsKey(r.Method.Method)).Select(r => r.Body!)))
        {
            Problems[pair.Key] = pair.Value;
            Candidates.Remove(pair.Key.Method.Method);
        }
    }

    public IEnumerable<MethodRecoveryResult> All => Targets.Concat(Dependencies);

    public void Rewrite(ManagedTypes types, BodyEmitter emitter, Func<FieldAccessor, bool> verified, Func<MethodDef, bool>? verifiedInline = null)
    {
        var allowed = Candidates.Values.Where(c => c.LanguageDefined && c.Method.Method.Address == 0 || verified(c)).ToHashSet();
        allowed.UnionWith(GenericAccessors);
        for (var i = 0; i < Targets.Length; i++)
        {
            if (Targets[i].Body is not { } original || verifiedInline is null) continue;
            var options = inlineOptions.GetValueOrDefault(original) ?? [];
            var callees = options.Where(m => InlineCandidates.ContainsKey(m) && verifiedInline(m)).Distinct().Select(m => Callee(InlineCandidates[m]))
                .Concat(genericInline.GetValueOrDefault(original) ?? []).ToArray();
            if (callees.Length == 0) continue;
            var rewritten = RecognizeInline(types, Targets[i].Method.Method.Owner, original, callees);
            if (ReferenceEquals(rewritten, original)) continue;
            Targets[i] = Targets[i] with { Body = rewritten };
            // F9 的越权访问按值记录；认回内联之后同一组值仍指向改写后的方法体。
            foreach (var access in Accesses.Where(a => ReferenceEquals(a.Body, original)).ToArray())
                Accesses[Accesses.IndexOf(access)] = access with { Body = rewritten };
        }
        for (var i = 0; i < Targets.Length; i++)
        {
            var result = Targets[i];
            if (result.Body is not { } body || !Accesses.Any(a => ReferenceEquals(a.Body, body))) continue;
            var choices = Accesses.Where(a => ReferenceEquals(a.Body, body)).ToArray();
            FieldAccessor? Select(ManagedValue value, bool write) => choices.Where(a => a.Write == write && a.Value.Equals(value))
                .SelectMany(a => a.Candidates).FirstOrDefault(a => allowed.Contains(a) && a.Matches(types, result.Method.Method.Owner, value, write));
            Targets[i] = result with { Body = AccessorRewriter.Rewrite(body, Select) };
        }
        // 认回访问器之后仍越权的访问按原样写出（用户决定：语义等价即计入）。
        emitter.IgnoreAccess = true;
        try { Problems = emitter.Emit(All.Where(r => r.Body is not null && !dependencyProblems.ContainsKey(r.Body)).Select(r => r.Body!)); }
        finally { emitter.IgnoreAccess = false; }
        foreach (var pair in dependencyProblems) Problems[pair.Key] = pair.Value;
        CheckTransparent();
    }

    private static IEnumerable<MethodDef> TransparentConstructors(ManagedBody body) => body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of)
        .SelectMany(ManagedValues.Walk).OfType<NewObjectValue>().Where(n => n.Transparent).Select(n => n.Constructor.Method)
        // 泛型方法实例（内联的 Start<T>）由执行对照按普查建模，不需要写出方法体。
        // 泛型类型的封闭实例（内联的 UniTask<T>.GetAwaiter）同样按普查建模。
        .Concat(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Where(c => c.Inlined && c.Invocation.Method.MethodArguments.Count == 0
            && c.Invocation.Method.TypeArguments.Count == 0).Select(c => c.Invocation.Method.Method));

    /// <summary>透明执行的构造函数没有写出时（有洞或写出失败），用到它的方法也不写出：骨架里的占位方法体不能代替它执行。</summary>
    private void CheckTransparent()
    {
        var written = All.Where(r => r.Body is not null && !Problems.ContainsKey(r.Body)).ToDictionary(r => r.Method.Method);
        bool changed;
        do
        {
            changed = false;
            foreach (var result in written.Values.ToArray())
                foreach (var dependency in TransparentConstructors(result.Body!))
                    if (!written.ContainsKey(dependency))
                    {
                        Problems[result.Body!] = $"构造函数 内联的 {dependency} 没有写出";
                        written.Remove(result.Method.Method);
                        changed = true;
                        break;
                    }
        } while (changed);
    }

    /// <summary>泛型方法实例（GenericMethod 注册入口）的代码地址。</summary>
    private static Dictionary<MethodRef, ulong> InstanceAddresses(ProgramFacts facts)
    {
        var map = new Dictionary<MethodRef, ulong>();
        foreach (var function in facts.Code.Functions)
            foreach (var entry in facts.EntriesAt(function.Start))
                if (entry is { Kind: EntryKind.GenericMethod, Method: { } method } && method.TypeArguments.Count > 0) map.TryAdd(method, function.Start);
        return map;
    }

    private Dictionary<MethodDef, (MethodRef Instance, ulong Address)[]>? genericInstances;
    private readonly Dictionary<MethodRef, InlineRecognition.Callee?> genericCallees = [];

    /// <summary>
    /// 方法体中越权字段所在的泛型封闭类型（如 UniTask&lt;bool&gt;、UniTask.Awaiter&lt;bool&gt;）上按普查建模的方法：取同一定义的一个实例
    /// （类型实参是非基元的具体类型，代换时不会误换其他类型）的恢复体，把它的类型实参换成所需的。
    /// </summary>
    private IEnumerable<InlineRecognition.Callee> GenericCallees(ManagedTypes types, TypeDef caller, MethodRecovery recovery, ManagedBody body)
    {
        var closed = new HashSet<DefinitionRef>();
        foreach (var (_, value, _) in Fields(body))
            for (ManagedValue? current = value; current is FieldValue f; current = f.Receiver is AddressValue a ? a.Target : f.Receiver)
                if (f.Field.DeclaringType is DefinitionRef { Arguments.Count: > 0 } d) closed.Add(d);
        if (closed.Count == 0) yield break;
        genericInstances ??= facts.Code.Functions.SelectMany(fn => facts.EntriesAt(fn.Start).Where(e => e is { Kind: EntryKind.GenericMethod, Method: { } m }
                // 类型实参取非 System 命名空间的无参值类型或 Nullable<…>：方法体里不会因别的原因出现它（例如 bool 返回值），代换只换实例本身。
                && m.MethodArguments.Count == 0 && m.TypeArguments is [DefinitionRef { Arguments.Count: 0, Definition: { IsValueType: true, Namespace: not "System" } } or DefinitionRef { Definition.FullName: "System.Nullable" }]
                && GenericInline.IsModeled(m.Method)).Select(e => (Instance: e.Method!, Address: fn.Start)))
            .GroupBy(p => p.Instance.Method).ToDictionary(g => g.Key, g => g.ToArray());
        foreach (var owner in closed)
            foreach (var method in owner.Definition.Methods.Where(GenericInline.IsModeled))
            {
                if (method.Name == "GetResult" && (owner.Arguments[0] is var argument && !ManagedTypes.IsReferenceType(argument) && types.Size(argument) > GenericInline.ResultLimit)) continue;
                var wanted = new MethodRef(method, owner.Arguments, []);
                if (!genericCallees.TryGetValue(wanted, out var callee))
                {
                    callee = null;
                    // 优先取与所需类型实参同类别（基元/结构体）、同大小的实例，代换后值的形态（整体读取、片）相同。
                    var target = owner.Arguments[0];
                    var all = genericInstances.GetValueOrDefault(method) ?? [];
                    // 所需实例本身在二进制中、但读不出时不建模（awaiter-census 只核对了读得出的实例）。
                    var own = facts.Code.Functions.SelectMany(fn => facts.EntriesAt(fn.Start).Where(e => e.Kind == EntryKind.GenericMethod && wanted.Equals(e.Method)).Select(_ => fn.Start)).FirstOrDefault();
                    if (own != 0)
                    {
                        // 所需实例本身在二进制中：直接用它的恢复体（不代换）；读不出时不建模。
                        if (recovery.RecoverInstance(wanted, own).Body is { } exact)
                            callee = new(wanted, exact, method.ReturnType.Substitute(owner.Arguments, []) is DefinitionRef { Definition.FullName: "System.Boolean" });
                        all = [];
                    }
                    foreach (var (instance, address) in all
                        .OrderBy(p => types.Kind(p.Instance.TypeArguments[0]) == types.Kind(target) ? 0 : 1).ThenBy(p => Math.Abs(types.Size(p.Instance.TypeArguments[0]) - types.Size(target))))
                    {
                        if (recovery.RecoverInstance(instance, address).Body is not { } source) continue;
                        var from = instance.TypeArguments[0];
                        var mapped = ManagedTypeMap.Map(source, t => ManagedTypeMap.Replace(t, from, target),
                            t => types.Kind(t) switch { TypeKind.Struct => 0, TypeKind.Bool => 8, TypeKind.Reference => 64, _ => types.Bits(t) });
                        callee = new(wanted, mapped, method.ReturnType.Substitute(owner.Arguments, []) is DefinitionRef { Definition.FullName: "System.Boolean" });
                        break;
                    }
                    genericCallees[wanted] = callee;
                }
                if (callee is not null && ManagedAccess.Method(types, caller, wanted, null)) yield return callee;
            }
    }

    private static InlineRecognition.Callee Callee(MethodRecoveryResult result) =>
        new(result.Method, result.Body!, result.Method.Method.ReturnType is DefinitionRef { Definition.FullName: "System.Boolean" });

    /// <summary>单字段包装的构造与内联方法的认回（大的被调方法先试）。</summary>
    private ManagedBody RecognizeInline(ManagedTypes types, TypeDef owner, ManagedBody body, InlineRecognition.Callee[] callees)
    {
        callees = callees.OrderByDescending(c => c.Body.Blocks.Sum(b => b.Statements.Count)).ToArray();
        var rewritten = InlineRecognition.RewriteWrappers(body, callees,
            f => !ManagedAccess.Field(types, owner, f, null) || (f.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0,
            t => t is DefinitionRef d && facts.Layouts.Of(d) is { } layout ? layout.Fields.Count : 0);
        return InlineRecognition.Rewrite(rewritten, callees, types.Boolean, v => v is FieldValue f && !ManagedAccess.Field(types, owner, f.Field, f.Receiver.Type));
    }

    /// <summary>方法体中越权字段的声明类型，以及经结构体字段链读到它们时外层字段的声明类型（如 UniTask.Awaiter.task 之于 UniTask.source）。</summary>
    private static IEnumerable<TypeDef> InaccessibleOwners(ManagedTypes types, TypeDef caller, ManagedBody body)
    {
        foreach (var (_, value, _) in Fields(body))
        {
            if (value is not FieldValue field || ManagedAccess.Field(types, caller, field.Field, field.Receiver.Type)) continue;
            for (ManagedValue? current = field; current is not null; )
            {
                if (current is FieldValue f)
                {
                    if (f.Field.DeclaringType is DefinitionRef { Definition: { GenericParameters.Count: 0 } d }) yield return d;
                    current = f.Receiver;
                }
                else current = current is AddressValue a ? a.Target : null;
            }
        }
    }

    public static IEnumerable<(ulong Address, ManagedValue Value, bool Write)> Fields(ManagedBody body)
    {
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            var roots = ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement));
            foreach (var root in roots)
                foreach (var value in ManagedValues.Walk(root))
                    if (value is FieldValue or StaticFieldValue)
                        yield return (statement.Address, value, statement is ManagedStore s && ReferenceEquals(s.Target, value));
        }
    }
}
