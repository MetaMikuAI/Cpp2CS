using System.Text.RegularExpressions;
using Cpp2CS.Model;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// 导出工程编译出的程序集：定义按全名对应到骨架，让解释器执行 C# 的编译结果，和原生走同一套事件比较。
/// C# 标识符里的 _00XX 是反编译器对非法字符的转义，还原后就是骨架的名字。名字里直接含尖括号的是 Roslyn 生成的：
/// 闭包和 lambda 按序号换算成骨架的名字；状态机和匿名类型两边不对应，执行到时按不可检查处理。
/// </summary>
internal sealed class CompiledSource
{
    private const string BackingField = "k__BackingField";
    /// <summary>生成名字里的方法序号：序号是方法在类型里的位置，导出的 C# 成员顺序不同，序号也不同；下划线后的次序两边相同。</summary>
    private static readonly Regex Ordinal = new(@"(?<=<>c__DisplayClass|<>c__|>b__|<>9__|>g__[^|/]*\|)\d+", RegexOptions.Compiled);
    private static readonly Regex Lambda = new(@"^<(?<method>[^>]+)>(b__|g__[^|]*\|)(?<ordinal>\d+)_\d+$", RegexOptions.Compiled);
    private static readonly Regex Closure = new(@"^<>c__DisplayClass(?<ordinal>\d+)_\d+", RegexOptions.Compiled);
    private static readonly Regex LambdaOwner = new(@"^<(?<method>[^>]+)>(b__|g__)", RegexOptions.Compiled);
    private readonly string assembly;
    private readonly Dictionary<string, TypeDef> types = [];
    private readonly Dictionary<string, MethodDef> methods = [];
    private readonly Dictionary<string, FieldDef> fields = [];
    private readonly Dictionary<string, MethodDefinition> bodies = [];
    private readonly HashSet<MethodDefinition> normalized = [];
    private readonly Dictionary<(string Outer, string Ordinal), string> ordinals = [];
    private readonly Dictionary<(string Outer, string Method), List<MethodDefinition>> lambdaBodies = [];
    private readonly Dictionary<string, string> aliases = [];

    public ModuleDefinition Module { get; }

    public CompiledSource(string path, string assembly, string references,
        IReadOnlyDictionary<TypeDefinition, TypeDef> skeletonTypes,
        IReadOnlyDictionary<MethodDefinition, MethodDef> skeletonMethods,
        IReadOnlyDictionary<FieldDefinition, FieldDef> skeletonFields)
    {
        this.assembly = assembly;
        var resolver = new DefaultAssemblyResolver();
        resolver.AddSearchDirectory(references);
        Module = ModuleDefinition.ReadModule(path, new ReaderParameters { InMemory = true, AssemblyResolver = resolver });
        PairOrdinals(skeletonTypes.Keys);
        foreach (var (type, definition) in skeletonTypes) types.TryAdd(TypeKey(type)!, definition);
        foreach (var (method, definition) in skeletonMethods) methods.TryAdd(MethodKey(method)!, definition);
        foreach (var (field, definition) in skeletonFields) fields.TryAdd(FieldKey(field, field.Name)!, definition);
        foreach (var type in Module.GetTypes())
            foreach (var method in type.Methods.Where(m => m.HasBody))
            {
                if (LambdaOwner.Match(method.Name) is { Success: true } lambda)
                {
                    var key = (Outer(type.FullName), lambda.Groups["method"].Value);
                    if (!lambdaBodies.TryGetValue(key, out var list)) lambdaBodies[key] = list = [];
                    list.Add(method);
                }
                else if (MethodKey(method) is { } name) bodies.TryAdd(name, method);
            }
    }

    /// <summary>同一个方法名的序号从小到大一一配对；个数不同时不配对，用到这些名字的方法按不可检查处理。</summary>
    private void PairOrdinals(IEnumerable<TypeDefinition> skeleton)
    {
        var theirs = Lambdas(skeleton.Where(t => !t.Name.Contains('<')));
        var ours = Lambdas(Module.GetTypes().Where(t => !t.Name.Contains('<')));
        foreach (var (key, compiled) in ours)
            if (theirs.TryGetValue(key, out var original) && compiled.Count == original.Count)
                foreach (var (from, to) in compiled.Zip(original)) ordinals[(key.Outer, from.ToString())] = to.ToString();
    }

    private static Dictionary<(string Outer, string Method), SortedSet<int>> Lambdas(IEnumerable<TypeDefinition> outers)
    {
        var result = new Dictionary<(string, string), SortedSet<int>>();
        foreach (var outer in outers)
            foreach (var method in outer.Methods.Concat(outer.NestedTypes.Where(n => n.Name.StartsWith("<>c", StringComparison.Ordinal)).SelectMany(n => n.Methods)))
            {
                string? ordinal = null;
                if (Lambda.Match(method.Name) is { Success: true } match) ordinal = match.Groups["ordinal"].Value;
                else if (Closure.Match(method.DeclaringType.Name) is { Success: true } closure) ordinal = closure.Groups["ordinal"].Value;
                if (ordinal is null || LambdaOwner.Match(method.Name) is not { Success: true } owner) continue;
                var key = (Plain(outer.FullName), owner.Groups["method"].Value);
                if (!result.TryGetValue(key, out var set)) result[key] = set = [];
                set.Add(int.Parse(ordinal, System.Globalization.CultureInfo.InvariantCulture));
            }
        return result;
    }

    /// <summary>骨架方法对应的编译体；C# 里没有写出时为 null。</summary>
    public MethodDefinition? Body(MethodDefinition skeleton)
    {
        var method = LambdaOwner.IsMatch(skeleton.Name) ? ClosestLambda(skeleton) : MethodKey(skeleton) is { } key ? bodies.GetValueOrDefault(key) : null;
        if (method is null) return null;
        if (normalized.Add(method)) TypeHandles(method.Body);
        return method;
    }

    /// <summary>
    /// lambda 的次序按 Roslyn 降级时的顺序和闭包结构编号，反编译出的写法可能不同，序号相同不一定是同一个。
    /// 在同一方法的 lambda 里按签名和方法体里的调用、字段、常量选最接近恢复体的；对应上之后，闭包类也按这一对换算。
    /// </summary>
    private MethodDefinition? ClosestLambda(MethodDefinition skeleton)
    {
        var owner = skeleton.DeclaringType;
        var key = (Outer(owner.FullName), LambdaOwner.Match(skeleton.Name).Groups["method"].Value);
        if (!lambdaBodies.TryGetValue(key, out var candidates)) return null;
        var signature = Signature(skeleton);
        var closure = Closure.IsMatch(owner.Name);
        var wanted = Tokens(skeleton);
        MethodDefinition? best = null;
        var score = int.MinValue;
        foreach (var candidate in candidates.Where(c => Closure.IsMatch(c.DeclaringType.Name) == closure && c.IsStatic == skeleton.IsStatic && Signature(c) == signature))
        {
            var tokens = Tokens(candidate);
            // 重合的越多、多出来的越少越接近；恢复体为空时选最短的。
            var value = Overlap(tokens, wanted) * 2 - tokens.Values.Sum();
            if (value > score)
            {
                best = candidate;
                score = value;
            }
        }
        if (best is not null && closure) aliases[best.DeclaringType.FullName] = Plain(owner.FullName);
        return best;
    }

    private string Signature(MethodDefinition method) => $"{Name(method.ReturnType)}({string.Join(",", method.Parameters.Select(p => Name(p.ParameterType)))})";

    private static Dictionary<string, int> Tokens(MethodDefinition method)
    {
        var tokens = new Dictionary<string, int>();
        if (!method.HasBody) return tokens;
        foreach (var instruction in method.Body.Instructions)
        {
            var token = instruction.Operand switch
            {
                MethodReference target => Regex.Replace(target.Name, "^[gs]et_", ""),
                FieldReference field => Regex.Replace(field.Name, "^<|>k__BackingField$", ""),
                TypeReference type => Plain(type.Name),
                string text => text,
                int number => number.ToString(System.Globalization.CultureInfo.InvariantCulture),
                sbyte number => number.ToString(System.Globalization.CultureInfo.InvariantCulture),
                _ => instruction.OpCode.Code is >= Code.Ldc_I4_M1 and <= Code.Ldc_I4_8 ? (instruction.OpCode.Code - Code.Ldc_I4_0).ToString(System.Globalization.CultureInfo.InvariantCulture) : null,
            };
            if (token is not null) tokens[token] = tokens.GetValueOrDefault(token) + 1;
        }
        return tokens;
    }

    private static int Overlap(Dictionary<string, int> left, Dictionary<string, int> right) =>
        left.Sum(p => Math.Min(p.Value, right.GetValueOrDefault(p.Key)));

    /// <summary>
    /// C# 取 RuntimeTypeHandle 只能写 typeof(T).TypeHandle，编译成 ldtoken 后再经 Type 对象绕一圈；两次调用是这种写法带来的，
    /// 不是被恢复方法的行为。还原成一条 ldtoken（结果相同，见 Type.GetTypeFromHandle 和 Type.TypeHandle 的定义）。
    /// </summary>
    private static void TypeHandles(Mono.Cecil.Cil.MethodBody body)
    {
        foreach (var instruction in body.Instructions)
            if (instruction is { OpCode.Code: Code.Ldtoken, Next: { Operand: MethodReference { Name: "GetTypeFromHandle" } } from }
                && from.Next is { Operand: MethodReference { Name: "get_TypeHandle" } } handle)
            {
                from.OpCode = OpCodes.Nop;
                from.Operand = null;
                handle.OpCode = OpCodes.Nop;
                handle.Operand = null;
            }
    }

    public TypeDef? Type(TypeReference type) => TypeKey(type) is { } key ? types.GetValueOrDefault(key) : null;

    public MethodDef? Method(MethodReference method) => MethodKey(method) is { } key ? methods.GetValueOrDefault(key) : null;

    public FieldDef? Field(FieldReference field) =>
        FieldKey(field, field.Name) is { } key && fields.TryGetValue(key, out var found) ? found
            // 反编译器把取不回自动属性的后备字段写成 _名字。
            : field.Name.StartsWith('_') && FieldKey(field, $"<{field.Name[1..]}>{BackingField}") is { } backing ? fields.GetValueOrDefault(backing)
            : null;

    /// <summary>Roslyn 为自动属性生成的访问器：方法体只读写后备字段。</summary>
    public MethodDefinition? AutoAccessor(MethodDefinition skeleton) =>
        Body(skeleton) is { } body && body.Body.Instructions.Any(i => i.Operand is FieldReference { Name: var name } && name.EndsWith(BackingField, StringComparison.Ordinal))
            && body.Body.Instructions.All(i => i.OpCode.Code is Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldfld or Code.Stfld or Code.Ldsfld or Code.Stsfld or Code.Ret or Code.Nop) ? body : null;

    private string? TypeKey(TypeReference type)
    {
        var element = type.GetElementType();
        // 引用的 Module 是引用方，所在程序集要看 Scope。
        var scope = element.Scope switch
        {
            AssemblyNameReference name => name.Name,
            ModuleDefinition module when module == Module => assembly,
            _ => element.Module.Assembly.Name.Name,
        };
        return Name(element) is { } text ? $"{scope}|{text}" : null;
    }

    private string? MethodKey(MethodReference method)
    {
        if (TypeKey(method.DeclaringType) is not { } owner || Member(method.DeclaringType, method.Name) is not { } name
            || Name(method.ReturnType) is not { } result) return null;
        var parameters = method.Parameters.Select(p => Name(p.ParameterType)).ToArray();
        return parameters.Contains(null) ? null : $"{result} {owner}::{name}({string.Join(",", parameters)})`{method.GenericParameters.Count}";
    }

    private string? FieldKey(FieldReference field, string name) =>
        TypeKey(field.DeclaringType) is { } owner && Member(field.DeclaringType, name) is { } member ? $"{owner}::{member}" : null;

    /// <summary>签名里的类型名：泛型参数按位置，定义和引用写法一致；修饰符不参与比较。</summary>
    private string? Name(TypeReference type)
    {
        switch (type)
        {
            case GenericParameter p: return (p.Type == GenericParameterType.Method ? "!!" : "!") + p.Position;
            case GenericInstanceType g:
                var arguments = g.GenericArguments.Select(Name).ToArray();
                return !arguments.Contains(null) && Name(g.ElementType) is { } element ? $"{element}<{string.Join(",", arguments)}>" : null;
            case ArrayType a: return Name(a.ElementType) is { } item ? $"{item}[{a.Rank}]" : null;
            case PointerType p: return Name(p.ElementType) + "*";
            case ByReferenceType r: return Name(r.ElementType) + "&";
            case PinnedType p: return Name(p.ElementType);
            case IModifierType m: return Name(m.ElementType);
        }
        var name = type.FullName;
        if (type.Module != Module || !name.Contains('<')) return Plain(name);
        if (aliases.TryGetValue(name, out var alias)) return alias;
        if (name.Contains("<PrivateImplementationDetails>", StringComparison.Ordinal)) return name;
        var last = name[(name.LastIndexOf('/') + 1)..];
        if (!last.StartsWith("<>c", StringComparison.Ordinal)) return null;
        return Translate(name, Outer(name));
    }

    /// <summary>成员名：编译结果里 Roslyn 生成的名字换算成骨架的序号。</summary>
    private string? Member(TypeReference owner, string name)
    {
        var element = owner.GetElementType();
        if (element.Module != Module || !name.Contains('<')) return Plain(name);
        return Translate(name, Outer(element.FullName));
    }

    private static string Outer(string fullName)
    {
        var at = fullName.IndexOf("/<", StringComparison.Ordinal);
        return Plain(at < 0 ? fullName : fullName[..at]);
    }

    private string? Translate(string name, string outer)
    {
        var known = true;
        var text = Ordinal.Replace(name, match =>
        {
            if (ordinals.TryGetValue((outer, match.Value), out var to)) return to;
            known = false;
            return match.Value;
        });
        return known ? text : null;
    }

    private static string Plain(string name) => Regex.Replace(name, "_00([0-9A-Fa-f]{2})", m => ((char)Convert.ToInt32(m.Groups[1].Value, 16)).ToString());
}
