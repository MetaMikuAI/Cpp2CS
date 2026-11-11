using System.Reflection;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class ModelChecks
{
    public const string Command = "model";

    public static int Run()
    {
        var checks = new Assertions();
        foreach (var (pointerSize, headerSize) in new[] { (4, 8), (8, 16), (8, 24) })
            CheckModel(checks, pointerSize, headerSize);
        return checks.Finish("Model");
    }

    private static void CheckModel(Assertions checks, int pointerSize, int headerSize)
    {
        string[] names = ["Object", "String", "Boolean", "Char", "SByte", "Byte", "Int16", "UInt16",
            "Int32", "UInt32", "Int64", "UInt64", "Single", "Double", "IntPtr",
            "RuntimeTypeHandle", "RuntimeFieldHandle", "RuntimeMethodHandle", "Void"];
        var definitions = names.Select((name, index) => Definition(name, index,
            name is not ("Object" or "String"))).ToArray();
        var model = new ProgramModel
        {
            MetadataVersion = 31, Assemblies = [], Types = definitions, Methods = [], Fields = [],
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
        };
        var layouts = new Layouts(pointerSize);
        var types = new ManagedTypes(model, layouts, pointerSize);
        var parameter = new GenericParameterRef("T", false, 0);
        var methodParameter = new GenericParameterRef("U", true, 0);
        var container = Definition("Container", 100, true);
        TypeRef compound = new ByRefRef(new ArrayRef(new DefinitionRef(container,
            [new PointerRef(parameter), methodParameter]), 2));
        checks.True(compound.ContainsGenericParameter(), "复合类型检测泛型参数");
        checks.True(compound.Substitute([types.Int32], [types.String]).Equals(
            new ByRefRef(new ArrayRef(new DefinitionRef(container,
                [new PointerRef(types.Int32), types.String]), 2))), "递归代入类与方法参数");
        checks.True(parameter.Substitute([], []) == parameter, "缺少实参时保留形参");
        checks.True(new DefinitionRef(container, [types.Int32]).GetHashCode()
            == new DefinitionRef(container, [types.Int32]).GetHashCode(), "结构相等类型的哈希一致");
        checks.True(new ArrayRef(types.Int32, 1) != new ArrayRef(types.Int32, 1) { IsVector = false },
            "向量与一维多维数组身份不同");
        checks.True(types.IsAssignable(new ArrayRef(types.String, 1), new ArrayRef(types.Object, 1)),
            "引用数组允许协变");
        checks.True(!types.IsAssignable(new ArrayRef(types.Int32, 1), new ArrayRef(types.Object, 1)),
            "值类型数组不能通过装箱协变");
        checks.True(!types.IsAssignable(new ArrayRef(types.String, 1),
            new ArrayRef(types.Object, 1) { IsVector = false }), "数组种类不同不可协变");
        var constrained = parameter with
        {
            Parameter = new GenericParameterDef
            {
                Name = "T", Position = 0, Attributes = GenericParameterAttributes.ReferenceTypeConstraint,
            },
        };
        checks.True(constrained.Equals(parameter) && constrained.IsReference && !parameter.IsReference,
            "泛型约束影响类型类别而不改变身份");
        checks.True(types.Kind(parameter) is null && types.Kind(constrained) == TypeKind.Reference,
            "无约束形参不猜测原生布局");
        checks.True(types.ValueWidth(types.Object) == pointerSize * 8
            && types.StorageBits(new ByRefRef(types.Int32)) == pointerSize * 8
            && types.StorageBits(new PointerRef(types.Int32)) == pointerSize * 8, "指针宽度来自调用方");

        var enumeration = Definition("Enumeration", 101, true, true);
        enumeration.Fields = [Field(enumeration, "value__", types.Int32, 0)];
        checks.True(ManagedTypes.Underlying(new DefinitionRef(enumeration, [])) == types.Int32,
            "枚举按实例字段取得底层类型");

        var inner = Definition("Inner", 102, true);
        var innerRef = new DefinitionRef(inner, []);
        var number = Field(inner, "Number", types.Int32, 0);
        inner.Fields = [number];
        layouts.Add(innerRef, headerSize, 4, [new(number, types.Int32, headerSize)]);
        var outer = Definition("Outer", 103, true);
        var outerRef = new DefinitionRef(outer, []);
        var nested = Field(outer, "Nested", innerRef, 0);
        var tail = Field(outer, "Tail", types.Int32, 4);
        outer.Fields = [nested, tail];
        layouts.Add(outerRef, headerSize, 8,
            [new(nested, innerRef, headerSize), new(tail, types.Int32, headerSize + 4)]);
        checks.True(layouts.Of(outerRef)!.ValueSize == 8, "值大小扣除调用方对象头");
        var projection = types.Project(outerRef, 0, 32);
        checks.True(projection is { Bit: 0, Width: 32, Path.Count: 1 }, "精确投影优先直接字段");
        var path = new FieldRef[] { new(nested, outerRef), new(number, innerRef) };
        checks.True(types.Project(outerRef, path) is { Bit: 0, Width: 32, Path.Count: 2 },
            "路径投影展开嵌套字段");
        checks.True(types.Projections(outerRef).Select(p => p.Bit).SequenceEqual([0, 32]),
            "标量叶子偏移不含对象头");
        checks.True(types.IntegerPieces(outerRef) is { Count: 2 }, "整数叶子完整覆盖可打包");
        checks.True(types.Project(outerRef, 16, 32) is null && types.Project(outerRef, 64, 1) is null,
            "跨字段与越界投影拒绝");
        checks.True(types.InstanceField(new ByRefRef(outerRef), 4, 4)?.Field.Field == tail
            && types.InstanceField(new ByRefRef(outerRef), 4, 2) is null, "值类型字段定位要求精确宽度");
        layouts.Add(outerRef, headerSize, 12,
            [new(nested, innerRef, headerSize), new(tail, types.Int32, headerSize + 8)]);
        checks.True(types.IntegerPieces(outerRef) is null, "含填充的结构不可作为完整整数打包");
        checks.True(!new ValueProjection([], types.Int32, int.MaxValue, 32).Contains(int.MaxValue, int.MaxValue),
            "投影边界检查不发生整数溢出");

        var method = new MethodDef
        {
            Index = 0, Owner = container, Name = "Apply", Token = 0, Attributes = MethodAttributes.Public,
            ImplAttributes = 0, Slot = -1, ReturnType = methodParameter,
            GenericParameters = [new() { Name = "U", Position = 0, Attributes = 0 }],
        };
        container.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        checks.True(MethodRef.Open(method).ContainsParameters(), "开放方法引用保留两类泛型槽位");
        checks.True(new MethodRef(method, [types.Int32], [types.String]).Concrete(method.ReturnType) == types.String,
            "方法引用具体化返回类型");
    }

    private static bool ContainsParameters(this MethodRef method) =>
        method.TypeArguments is [GenericParameterRef { IsMethod: false, Position: 0 }]
        && method.MethodArguments is [GenericParameterRef { IsMethod: true, Position: 0 }];

    private static TypeDef Definition(string name, int index, bool value, bool enumeration = false) => new()
    {
        Index = index, Assembly = "mscorlib.dll", Namespace = "System", Name = name, Token = 0,
        Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = enumeration,
    };

    private static FieldDef Field(TypeDef owner, string name, TypeRef type, int offset) => new()
    {
        Index = 0, Owner = owner, Name = name, Type = type, Attributes = FieldAttributes.Public, Offset = offset,
    };

    // 合成布局只为检查消费端；不推断运行时布局。
    private sealed class Layouts(int pointerSize) : ITypeLayouts
    {
        private readonly Dictionary<DefinitionRef, TypeLayout> layouts = new();

        public void Add(DefinitionRef type, int headerSize, int valueSize, IReadOnlyList<FieldSlot> fields) =>
            layouts[type] = new TypeLayout
            {
                Type = type, ObjectHeaderSize = headerSize, InstanceSize = headerSize + valueSize,
                ActualSize = headerSize + valueSize, MinimumAlignment = 4, HasReferences = false,
                Fields = fields, Statics = [], StaticSize = 0, ThreadStatics = [], FromMetadata = false,
            };

        public TypeLayout? Of(DefinitionRef type) => layouts.GetValueOrDefault(type);
        public (int Size, int Alignment) SizeAndAlignment(TypeRef type) =>
            TrySizeAndAlignment(type) ?? throw new InvalidOperationException("没有合成布局");

        public (int Size, int Alignment)? TrySizeAndAlignment(TypeRef type) => type switch
        {
            DefinitionRef d when layouts.TryGetValue(d, out var layout) => (layout.ValueSize, layout.MinimumAlignment),
            _ when ManagedTypes.PrimitiveName(type) == "Int32" => (4, 4),
            _ when ManagedTypes.IsReferenceType(type) || type is PointerRef or ByRefRef => (pointerSize, pointerSize),
            _ => null,
        };
    }
}
