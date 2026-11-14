using Cpp2CS.Model;
using Mono.Cecil;
using R = System.Reflection;

namespace Cpp2CS.Tests.Execution;

/// <summary>测试侧 CIL 元数据视图；同全名的定义共享身份，方法体仍由各自模块提供。</summary>
internal sealed partial class CecilModel
{
    private readonly Dictionary<string, TypeDef> types = [];
    private readonly Dictionary<string, MethodDef> methods = [];
    private readonly Dictionary<string, FieldDef> fields = [];
    private readonly Dictionary<TypeDef, TypeDefinition> definitions = [];
    private readonly Dictionary<MethodDef, MethodDefinition> methodDefinitions = [];
    private readonly HashSet<TypeDef> filled = [];
    private readonly List<ModuleDefinition> modules;
    public MethodRef? Context { get; private set; }
    public ProgramModel Program { get; private set; } = null!;
    public CecilModel(params ModuleDefinition[] modules)
    {
        this.modules = modules.Distinct().ToList();
        // 类型服务按传统 corlib 名称索引；别名只针对真正的核心库定义。
        var core = modules[0].TypeSystem.Object.Resolve().Module;
        foreach (var module in this.modules.Append(core).Distinct())
            foreach (var type in module.GetTypes()) Definition(type);
        foreach (var type in definitions.Keys.ToArray()) Fill(type);
        // 填充成员时引用到的外部枚举也要具备底层字段，不能只留下身份。
        foreach (var type in definitions.Keys.Where(t => t.IsEnum).ToArray()) Fill(type);
        Program = new ProgramModel { MetadataVersion = 0, Assemblies = [], Types = types.Values.ToArray(), Methods = methods.Values.ToArray(),
            Fields = fields.Values.ToArray(), RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [] };
        checking = true;
    }
    private CecilModel(CecilModel source)
    {
        types = new(source.types); methods = new(source.methods); fields = new(source.fields);
        definitions = new(source.definitions); methodDefinitions = new(source.methodDefinitions); filled = new(source.filled);
        modules = source.modules; Program = source.Program; checking = source.checking;
    }
    internal bool HasCompleteDefinitions => filled.Count == definitions.Count;
    /// <summary>只复用完整填充的元数据；懒加载映射与对应性检查缓存逐方法隔离。</summary>
    public static Func<CecilModel> Factory(params ModuleDefinition[] modules)
    {
        CecilModel? template = null;
        return () =>
        {
            var model = template ?? new CecilModel(modules);
            if (!model.HasCompleteDefinitions) return model;
            template = model;
            return new(model);
        };
    }
    private CecilModel(CecilModel source, MethodRef context)
    {
        types = source.types; methods = source.methods; fields = source.fields; definitions = source.definitions;
        methodDefinitions = source.methodDefinitions; filled = source.filled; checking = source.checking; checkedTypes = source.checkedTypes; modules = source.modules; Program = source.Program; Context = context;
    }
    public CecilModel InContext(MethodRef context) => new(this, context);
    private string Key(TypeDefinition t) => (t.Module == t.Module.TypeSystem.Object.Resolve().Module ? "mscorlib.dll" : modules.Contains(t.Module) ? "input" : t.Module.Assembly.Name.Name + ".dll") + "|" + t.FullName;
    private TypeDef Definition(TypeReference reference)
    {
        var t = reference.Resolve() ?? throw new Unsupported($"无法解析类型 {reference}");
        var key = Key(t);
        if (types.TryGetValue(key, out var found))
        {
            if (Program is not null && found.IsEnum) Fill(found);
            if (Context is not null) CheckType(found);
            return found;
        }
        var result = new TypeDef { Index = types.Count, Assembly = key.Split('|')[0], Namespace = t.Namespace, Name = t.Name,
            Token = t.MetadataToken.ToUInt32(), Attributes = (R.TypeAttributes)t.Attributes, IsValueType = t.IsValueType,
            IsEnum = t.IsEnum, PackingSize = t.PackingSize, ClassSizeIsDefault = !t.HasLayoutInfo };
        types.Add(key, result); definitions.Add(result, t);
        result.DeclaringType = t.DeclaringType is null ? null : Definition(t.DeclaringType);
        result.GenericParameters = t.GenericParameters.Select(Generic).ToArray();
        // 枚举的底层类型来自 value__ 字段，类型查询后即可被存储与值类别查询使用。
        if (Program is not null && result.IsEnum) Fill(result);
        return result;
    }
    private static GenericParameterDef Generic(GenericParameter p) => new() { Name = p.Name, Position = p.Position, Attributes = (R.GenericParameterAttributes)p.Attributes };
    public void Prepare(TypeDef type) { CheckType(type, layout: true); Fill(type); }
    private void Fill(TypeDef type)
    {
        if (!filled.Add(type)) return;
        var enabled = checking;
        checking = false;
        try
        {
            var t = definitions[type];
            type.BaseType = t.BaseType is null ? null : Type(t.BaseType);
            type.NestedTypes = t.NestedTypes.Select(Definition).ToArray();
            type.Interfaces = t.Interfaces.Select(i => Type(i.InterfaceType)).ToArray();
            type.Fields = t.Fields.Select(f => Field(f).Field).ToArray();
            type.Methods = t.Methods.Select(m => Method(m).Method).ToArray();
        }
        finally { checking = enabled; }
    }
    public TypeRef Type(TypeReference type) => type switch
    {
        GenericParameter p => new GenericParameterRef(p.Name, p.Type == GenericParameterType.Method, p.Position)
            .Substitute(Context?.TypeArguments ?? [], Context?.MethodArguments ?? []),
        GenericInstanceType g => new DefinitionRef(Definition(g.ElementType), g.GenericArguments.Select(Type).ToArray()),
        ArrayType a => new ArrayRef(Type(a.ElementType), a.Rank) { IsVector = a.IsVector },
        ByReferenceType b => new ByRefRef(Type(b.ElementType)), PointerType p => new PointerRef(Type(p.ElementType)),
        PinnedType p => Type(p.ElementType), IModifierType m => Type(m.ElementType),
        FunctionPointerType => new PrimitiveRef("nint"),
        _ => new DefinitionRef(Definition(type), [])
    };
    public MethodRef Method(MethodReference reference)
    {
        var source = reference.Resolve() ?? throw new Unsupported($"无法解析方法 {reference}");
        CheckMethod(source);
        var owner = Definition(source.DeclaringType);
        var key = Key(source.DeclaringType) + "|" + Signature(source);
        if (!methods.TryGetValue(key, out var method))
        {
            method = new MethodDef { Index = methods.Count, Owner = owner, Name = source.Name, Token = source.MetadataToken.ToUInt32(),
                Attributes = (R.MethodAttributes)source.Attributes, ImplAttributes = (R.MethodImplAttributes)source.ImplAttributes, Slot = -1 };
            methods.Add(key, method); methodDefinitions.Add(method, source);
            method.ReturnType = Type(source.ReturnType);
            method.Parameters = source.Parameters.Select(p => new ParameterDef(p.Name, Type(p.ParameterType), (R.ParameterAttributes)p.Attributes, p.HasConstant ? p.Constant : null, p.HasConstant)).ToArray();
            method.GenericParameters = source.GenericParameters.Select(Generic).ToArray();
        }
        return new(method, reference.DeclaringType is GenericInstanceType g ? g.GenericArguments.Select(Type).ToArray() : [],
            reference is GenericInstanceMethod m ? m.GenericArguments.Select(Type).ToArray() : []);
    }
    public FieldRef Field(FieldReference reference)
    {
        var f = reference.Resolve() ?? throw new Unsupported($"无法解析字段 {reference}");
        CheckType(Definition(f.DeclaringType), layout: true);
        var key = Key(f.DeclaringType) + "|" + f.Name;
        if (!fields.TryGetValue(key, out var field))
        {
            field = new FieldDef { Index = fields.Count, Owner = Definition(f.DeclaringType), Name = f.Name, Type = Type(f.FieldType),
                Attributes = (R.FieldAttributes)f.Attributes, Offset = f.HasLayoutInfo ? f.Offset : -1, Token = f.MetadataToken.ToUInt32(), Constant = f.HasConstant ? f.Constant : null,
                InitialValue = f.InitialValue.Length == 0 ? null : f.InitialValue };
            fields.Add(key, field);
        }
        return new(field, Type(reference.DeclaringType));
    }
    public MethodDefinition? Body(MethodRef method, ModuleDefinition module)
    {
        var source = methodDefinitions[method.Method];
        if (modules.Contains(source.Module))
            return module.GetTypes().FirstOrDefault(t => t.FullName == source.DeclaringType.FullName)?.Methods.FirstOrDefault(m => Signature(m) == Signature(source) && m.HasBody);
        // 匹配核心库中的空构造与单次字段 getter 由参考 IL 证明；其他外部调用保持不透明。
        var core = module.TypeSystem.Object.Resolve().Module;
        if (source.Module.Assembly.Name.FullName != core.Assembly.Name.FullName) return null;
        var candidate = core.GetTypes().FirstOrDefault(t => t.FullName == source.DeclaringType.FullName)?.Methods.FirstOrDefault(m => Signature(m) == Signature(source) && m.HasBody);
        return candidate is not null && (EmptyConstructor(candidate, []) || FieldGetter(candidate)) ? candidate : null;
    }
    private static bool FieldGetter(MethodDefinition method)
    {
        if (!method.HasBody || method.Parameters.Count != 0 || method.Body.ExceptionHandlers.Count != 0
            || (method.ImplAttributes & MethodImplAttributes.Synchronized) != 0) return false;
        var instructions = method.Body.Instructions.Where(i => i.OpCode.Code != Mono.Cecil.Cil.Code.Nop).ToArray();
        var field = instructions switch
        {
            [{ OpCode.Code: Mono.Cecil.Cil.Code.Ldarg_0 }, { OpCode.Code: Mono.Cecil.Cil.Code.Ldfld, Operand: FieldReference f }, { OpCode.Code: Mono.Cecil.Cil.Code.Ret }]
                when !method.IsStatic => f,
            [{ OpCode.Code: Mono.Cecil.Cil.Code.Ldsfld, Operand: FieldReference f }, { OpCode.Code: Mono.Cecil.Cil.Code.Ret }]
                when method.IsStatic => f,
            _ => null,
        };
        return field is not null && field.FieldType.FullName == method.ReturnType.FullName;
    }
    private static bool EmptyConstructor(MethodDefinition method, HashSet<MethodDefinition> active)
    {
        if (method.IsStatic || method.Name != ".ctor" || method.Parameters.Count != 0 || !method.HasBody
            || method.Body.ExceptionHandlers.Count != 0 || !active.Add(method)) return false;
        var instructions = method.Body.Instructions.Where(i => i.OpCode.Code != Mono.Cecil.Cil.Code.Nop).ToArray();
        bool empty = instructions is [{ OpCode.Code: Mono.Cecil.Cil.Code.Ret }]
            || instructions is [{ OpCode.Code: Mono.Cecil.Cil.Code.Ldarg_0 }, { OpCode.Code: Mono.Cecil.Cil.Code.Call, Operand: MethodReference called }, { OpCode.Code: Mono.Cecil.Cil.Code.Ret }]
                && called.DeclaringType.FullName == method.DeclaringType.BaseType?.FullName && called.Resolve() is { } parent && EmptyConstructor(parent, active);
        active.Remove(method);
        return empty;
    }

}
