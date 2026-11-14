using System.Buffers.Binary;
using System.Reflection;
using System.Text;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>对照无法判定的原因，包括合成环境不足与已登记的实现差异。</summary>
public enum ComparisonReason { None, MissingReference, GenericDefinition, InputSynthesis, UnsupportedConstruct, NaN, StepBudget, CallDepthBudget, MissingBody, InvalidRequest, TypeMismatch, ImplementationDifference }
internal sealed class Unsupported(string reason, ComparisonReason kind = ComparisonReason.UnsupportedConstruct) : Exception(reason)
{
    public ComparisonReason Kind { get; } = kind;
}

/// <summary>
/// 跨用例共用的方法身份与具体类型候选；方法身份是解释器的逻辑编号。
/// </summary>
internal sealed class WorldIndex
{
    private readonly Dictionary<MethodRef, ulong> fake = new();
    private readonly Dictionary<ulong, MethodRef> fakeMethods = new();
    private readonly Dictionary<TypeRef, DefinitionRef[]> concrete = new();
    private readonly Dictionary<TypeRef, DefinitionRef[]> candidates = new();
    private readonly Dictionary<(TypeRef, TypeRef), TypeRef[]> hintCandidates = new();

    public WorldIndex(ProgramModel model, ManagedTypes types)
    {
        Model = model;
        Types = types;
        ManagedValues = new ManagedValues(this);
    }
    public ProgramModel Model { get; }
    public ManagedTypes Types { get; }
    public ITypeLayouts Layouts => Types.Layouts;
    public ManagedValues ManagedValues { get; }
    public ulong CodeAddress(MethodRef method)
    {
        if (fake.TryGetValue(method, out var address)) return address;
        address = World.CodeBase + 0x100 + (ulong)fake.Count * 8;
        fake.Add(method, address);
        fakeMethods.Add(address, method);
        return address;
    }

    /// <summary>作为 type 类型输入对象的候选：Concrete 中去掉字符串与 mscorlib 的类（System.Object 除外）。</summary>
    public DefinitionRef[] Candidates(TypeRef type)
    {
        if (candidates.TryGetValue(type, out var found)) return found;
        found = Concrete(type).Where(c => !c.Equals(Types.String) && c.Definition.Assembly != "mscorlib.dll" || c.Equals(Types.Object)).ToArray();
        candidates.Add(type, found);
        return found;
    }

    /// <summary>
    /// 方法 IL 中出现的类型 hint 用作 declared 类型输入时的候选：hint 是可赋给 declared 的具体类时为它自身；
    /// 是接口或抽象类时为 declared 的候选中可赋给 hint 的（使 isinst 接口的分支也能走到）。
    /// </summary>
    public TypeRef[] HintCandidates(TypeRef declared, TypeRef hint)
    {
        if (hintCandidates.TryGetValue((declared, hint), out var found)) return found;
        found = hint is DefinitionRef { Definition: var h } && (h.IsInterface || (h.Attributes & TypeAttributes.Abstract) != 0)
            ? Candidates(declared).Where(c => Types.IsAssignable(c, hint)).ToArray<TypeRef>()
            : hint is DefinitionRef && Types.IsAssignable(hint, declared) ? [hint] : [];
        hintCandidates.Add((declared, hint), found);
        return found;
    }

    private static bool Closed(TypeRef type) => type switch
    {
        GenericParameterRef => false,
        DefinitionRef d => d.Arguments.All(Closed),
        ArrayRef a => Closed(a.Element),
        PointerRef p => Closed(p.Element),
        ByRefRef r => Closed(r.Element),
        _ => true,
    };

    /// <summary>可赋给 type 的具体类：非抽象、非泛型定义的类（按类型序号），以及程序中实际存在的封闭泛型实例（按运行时类型表的顺序）。</summary>
    public DefinitionRef[] Concrete(TypeRef type)
    {
        if (concrete.TryGetValue(type, out var found)) return found;
        static bool IsClass(TypeDef t) => !t.IsInterface && (t.Attributes & TypeAttributes.Abstract) == 0 && !t.IsValueType;
        found = Model.Types
            .Where(t => IsClass(t) && t.GenericParameters.Count == 0)
            .Select(t => new DefinitionRef(t, []))
            .Concat(Model.RuntimeTypes.OfType<DefinitionRef>().Where(d => d.Arguments.Count > 0 && IsClass(d.Definition) && Closed(d)).Distinct())
            .Where(t => Types.IsAssignable(t, type)).ToArray();
        concrete.Add(type, found);
        return found;
    }
}

/// <summary>SplitMix64 随机数（构造廉价：输入合成每个值都新建一个）。</summary>
internal struct SplitMix(ulong state)
{
    public ulong NextUInt64()
    {
        var z = state += 0x9E3779B97F4A7C15UL;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
        return z ^ (z >> 31);
    }

    /// <summary>[0, n) 中的整数（n 很小，取模的偏差可以忽略）。</summary>
    public int Next(int n) => (int)(NextUInt64() % (ulong)n);
    public int Next(int min, int max) => min + Next(max - min);
    public long NextInt64() => (long)NextUInt64();
    public double NextDouble() => (NextUInt64() >> 11) * (1.0 / (1UL << 53));
}

/// <summary>被测方法 IL 中出现的整数常量（含 ±1 与相反数）与类型，用于引导取值。</summary>
internal sealed record Hints(IReadOnlyList<ulong> Constants, IReadOnlyList<TypeRef> Types);

/// <summary>
/// 两侧共用的合成输入世界：初始对象、数组、字符串与反射句柄按键共享。
/// 执行写入由 Side 隔离；私有存储编码不描述目标运行时布局。
/// </summary>
internal sealed partial class World
{
    public const ulong RuntimeBase = 0x7000_0000_0000, RuntimeSize = 0x100_0000;
    public const ulong HeapBase = 0x7100_0000_0000, HeapSize = 0x100_0000;
    /// <summary>异常对象的身份与类型通过抛出事件比较。</summary>
    public const ulong ExceptionBase = 0x7180_0000_0000, ExceptionSize = 0x10_0000;
    public const ulong StackBase = 0x7200_0000_0000, StackSize = 0x10_0000;
    /// <summary>逻辑方法编号的独立区间；不包含机器代码。</summary>
    public const ulong CodeBase = 0x7300_0000_0000, CodeSize = 0x10_0000;
    public const ulong Sentinel = CodeBase;
    public const int MaxDepth = 3;

    /// <summary>Runtime 区已合成部分的字节（按需增长，上限 RuntimeSize）。</summary>
    private byte[] runtime = new byte[0x4_0000];
    private ulong top = RuntimeBase + 0x100;
    private readonly Dictionary<TypeRef, ulong> klasses = new();
    private readonly Dictionary<ulong, TypeRef> klassTypes = new();
    private readonly Dictionary<MethodRef, ulong> methodInfos = new();
    private readonly Dictionary<ulong, MethodRef> methodInfoOwners = new();
    private readonly Dictionary<FieldRef, ulong> fieldInfos = new();
    private readonly Dictionary<string, ulong> strings = new();
    private readonly Dictionary<(int, TypeRef), ulong> returns = new();
    private readonly HashSet<FieldRef> preparedStatics = new();
    private readonly int seed;
    private readonly HashSet<TypeRef> uninitialized = new();

    private readonly TypeRef? initializedOwner;

    /// <summary>
    /// hints：被测方法用到的常量与类型（取值时优先尝试，使比较、类型检查的各分支都有机会走到）。
    /// initializedOwner：按 CLR 的保证在被测方法执行时已经（或正在）初始化的类型，不会被选为未初始化。
    /// </summary>
    public World(WorldIndex index, int seed, Hints hints, TypeRef? initializedOwner)
    {
        Index = index;
        this.seed = seed;
        Hints = hints;
        this.initializedOwner = initializedOwner;
    }

    public Hints Hints { get; }

    public WorldIndex Index { get; }
    public ManagedTypes Types => Index.Types;
    private ITypeLayouts Layouts => Index.Layouts;
    /// <summary>当前执行侧：合成的字节同时写入它的内存。</summary>
    public Side? Active { get; set; }
    public ulong RuntimeTop => top;
    public ReadOnlySpan<byte> RuntimeBytes => runtime.AsSpan(0, (int)(top - RuntimeBase));

    public static bool Compared(ulong address) =>
        address - RuntimeBase < RuntimeSize || address - HeapBase < HeapSize;

    /// <summary>比较时的初始值：Runtime 区取合成内容，Heap 区为 0。</summary>
    public byte Initial(ulong address) => address - RuntimeBase < (ulong)runtime.Length ? runtime[address - RuntimeBase] : (byte)0;

    /// <summary>由（种子, 键）决定的随机数源：FNV-1a 64 位散列作为 SplitMix64 的初始状态（终混避免相近的键得到相关的序列）。</summary>
    public SplitMix Rng(string key)
    {
        var hash = 14695981039346656037UL;
        foreach (var c in seed.ToString(System.Globalization.CultureInfo.InvariantCulture)) hash = (hash ^ c) * 1099511628211UL;
        hash = (hash ^ ':') * 1099511628211UL;
        foreach (var c in key) hash = (hash ^ c) * 1099511628211UL;
        return new SplitMix(hash);
    }

    // —— Runtime 区的分配与写入 ——

    private ulong Reserve(int size, int alignment = 16)
    {
        top = (top + (ulong)alignment - 1) & ~((ulong)alignment - 1);
        var address = top;
        top += (ulong)Math.Max(size, 1);
        if (top - RuntimeBase > RuntimeSize) throw new Unsupported("合成运行时区已满");
        if (top - RuntimeBase > (ulong)runtime.Length) System.Array.Resize(ref runtime, (int)Math.Min(RuntimeSize, Math.Max(top - RuntimeBase, (ulong)runtime.Length * 2)));
        return address;
    }

    private void Put(ulong address, ReadOnlySpan<byte> bytes)
    {
        bytes.CopyTo(runtime.AsSpan((int)(address - RuntimeBase)));
        Active?.Synthesized(address, bytes);
    }

    public void Put64(ulong address, ulong value) { Span<byte> b = stackalloc byte[8]; BinaryPrimitives.WriteUInt64LittleEndian(b, value); Put(address, b); }
    private void Put32(ulong address, uint value) { Span<byte> b = stackalloc byte[4]; BinaryPrimitives.WriteUInt32LittleEndian(b, value); Put(address, b); }
    private void Put16(ulong address, ushort value) { Span<byte> b = stackalloc byte[2]; BinaryPrimitives.WriteUInt16LittleEndian(b, value); Put(address, b); }
    private void Put8(ulong address, byte value) => Put(address, [value]);

    private void PutValue(ulong address, ulong bits, int bytes)
    {
        Span<byte> b = stackalloc byte[8];
        BinaryPrimitives.WriteUInt64LittleEndian(b, bits);
        Put(address, b[..bytes]);
    }

    private ulong CString(string text)
    {
        var bytes = Encoding.UTF8.GetBytes(text + "\0");
        var address = Reserve(bytes.Length, 8);
        Put(address, bytes);
        return address;
    }

    // —— 运行时结构 ——

    /// <summary>klass 对应的托管类型；不是合成的 klass 时为 null。</summary>
    public TypeRef? TypeOfKlass(ulong klass) => klassTypes.GetValueOrDefault(klass);

    /// <summary>精确初始化的类型（没有 beforefieldinit）：首次调用其静态方法或构造函数之前就要运行静态构造（ECMA-335 II.10.5.3.1）。</summary>
    public static bool Precise(TypeRef type) =>
        type is DefinitionRef d && (d.Definition.Attributes & TypeAttributes.BeforeFieldInit) == 0;

    /// <summary>类在用例开始时是否尚未运行静态构造（只对有静态构造的类成立）。</summary>
    public bool Uninitialized(TypeRef type)
    {
        Klass(type);
        return uninitialized.Contains(type);
    }

    public ulong TypePointer(TypeRef type) => Klass(type);
    public TypeRef TypeOfHandle(ulong handle) => TypeOfKlass(handle) ?? throw new Unsupported("未知类型句柄");
    private readonly Dictionary<TypeRef, ulong> staticBlocks = [];
    public ulong Klass(TypeRef type)
    {
        if (klasses.TryGetValue(type, out var value)) return value;
        value = Reserve(8);
        klasses.Add(type, value);
        klassTypes.Add(value, type);
        if (type is DefinitionRef d && d.Definition.Methods.Any(m => m.Name == ".cctor") && !type.Equals(initializedOwner))
            uninitialized.Add(type);
        return value;
    }
    public ulong MethodInfo(MethodRef method)
    {
        if (methodInfos.TryGetValue(method, out var value)) return value;
        value = Reserve(8);
        methodInfos.Add(method, value);
        methodInfoOwners.Add(value, method);
        return value;
    }
    public MethodRef? MethodOfInfo(ulong info) => methodInfoOwners.GetValueOrDefault(info);
    public ulong FieldInfo(FieldRef field)
    {
        if (fieldInfos.TryGetValue(field, out var value)) return value;
        value = Reserve(8);
        fieldInfos.Add(field, value);
        return value;
    }

    // —— 字段与取值 ——

    /// <summary>字段相对对象起始（引用类型含对象头）或静态字段块的偏移。</summary>
    public int FieldOffset(FieldRef field)
    {
        if (field.DeclaringType is not DefinitionRef owner || Layouts.Of(owner)?.Field(field.Field) is not { } slot)
            throw new Unsupported($"字段 {field} 没有布局");
        return slot.Offset;
    }

    public TypeRef FieldType(FieldRef field) => field.Field.Type.Substitute(field.DeclaringType is DefinitionRef d ? d.Arguments : [], []);

    /// <summary>值在内存中占的字节数（引用为 8）。</summary>
    public int StorageSize(TypeRef type) => ManagedTypes.IsReferenceType(type) || type is PointerRef or ByRefRef ? 8 : Types.Size(type) is var size and > 0 ? size : throw new Unsupported($"类型 {type} 的大小");

    public ulong StaticAddress(FieldRef field)
    {
        if (!staticBlocks.TryGetValue(field.DeclaringType, out var block))
        {
            var layout = Layouts.Of((DefinitionRef)field.DeclaringType) ?? throw new Unsupported("静态字段缺少布局");
            staticBlocks.Add(field.DeclaringType, block = Reserve(Math.Max(layout.StaticSize, 1)));
        }
        return block + (ulong)FieldOffset(field);
    }

    /// <summary>给方法会读写的静态字段填入初值（其余静态字段保持 0，避免合成整个类型闭包）。</summary>
    public void PrepareStatic(FieldRef field)
    {
        if (!preparedStatics.Add(field)) return;
        var address = StaticAddress(field);
        // 核心库原生整数的 Zero 是只读零常量；不能作为可变静态状态合成非零值。
        if (field.Field.Name == "Zero" && (field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && ManagedTypes.PrimitiveName(field.DeclaringType) is "IntPtr" or "UIntPtr"
            && FieldType(field).Equals(field.DeclaringType))
        {
            PutValue(address, 0, StorageSize(FieldType(field)));
            return;
        }
        Fill(address, FieldType(field), $"static:{field}", 0);
    }

    private void Fill(ulong address, TypeRef type, string key, int depth)
    {
        if (Types.Kind(type) == TypeKind.Struct)
        {
            RegisterValue(address, type);
            if (type is not DefinitionRef d || Layouts.Of(d) is not { } layout) throw new Unsupported($"结构 {type} 的布局");
            foreach (var slot in layout.Fields)
                Fill(address + (ulong)(slot.Offset - StorageLayout.ObjectHeaderSize), slot.Type.Substitute(d.Arguments, []), $"{key}.{slot.Field.Name}", depth);
            return;
        }
        PutValue(address, Value(type, key, depth), StorageSize(type));
    }

    /// <summary>type 类型的一个输入值（整数、浮点的位型，或对象地址）。key 决定取值。</summary>
    public ulong Value(TypeRef type, string key, int depth)
    {
        var rng = Rng(key);
        switch (Types.Kind(type))
        {
            case TypeKind.Bool: return (ulong)rng.Next(2);
            case TypeKind.Int:
            {
                var bits = Types.Bits(type);
                var mask = bits == 64 ? ulong.MaxValue : (1UL << bits) - 1;
                // 方法中的常量（含 ±1）优先：比较的两个分支、枚举的特定成员都靠它走到；调用的返回值常与常量比较（如 Count() == 1），更多地取常量
                if (Hints.Constants.Count > 0 && rng.Next(key.StartsWith("return", StringComparison.Ordinal) ? 2 : 3) == 0)
                    return Hints.Constants[rng.Next(Hints.Constants.Count)] & mask;
                if (ManagedTypes.Underlying(type) != type && type is DefinitionRef { Definition: var e } && rng.Next(3) != 0
                    && e.Fields.Where(f => f.IsStatic && f.Constant is not null).ToArray() is { Length: > 0 } constants)
                    return constants[rng.Next(constants.Length)].Constant switch
                    {
                        ulong u => u, uint u => u, ushort u => u, byte u => u, char u => u,
                        var c => unchecked((ulong)Convert.ToInt64(c)),
                    } & mask;
                ulong[] edges = [0, 1, 2, ulong.MaxValue, 7, 100, 1UL << (bits - 1), (1UL << (bits - 1)) - 1];
                // 同一用例内共用的几个值：让不同来源的整数（参数、字段、返回值）有机会相等
                if (rng.Next(4) == 0) return SharedInteger(rng.Next(3)) & mask;
                return (rng.Next(3) == 0 ? (ulong)rng.NextInt64() : edges[rng.Next(edges.Length)]) & mask;
            }
            case TypeKind.Float:
            {
                float[] values = [0, 1, -1, 0.5f, 2.5f, 100, -3.25f, float.NaN, 1e-3f];
                return BitConverter.SingleToUInt32Bits(rng.Next(4) == 0 ? (float)(rng.NextDouble() * 200 - 100) : values[rng.Next(values.Length)]);
            }
            case TypeKind.Double:
            {
                double[] values = [0, 1, -1, 0.5, 2.5, 100, -3.25, double.NaN, 1e-3];
                return BitConverter.DoubleToUInt64Bits(rng.Next(4) == 0 ? rng.NextDouble() * 200 - 100 : values[rng.Next(values.Length)]);
            }
            case TypeKind.Pointer:
                if (type is ByRefRef b) return ValueStorage(b.Element, key);
                if (type is PointerRef) return 0;
                // 原生整数是可复制的位型；非零、高位和负值可区分结构体中的不同指针字段。
                ulong[] pointers = [0, 1, uint.MaxValue, 1UL << 32, 1UL << 63, ulong.MaxValue];
                return pointers[rng.Next(pointers.Length)];
            case TypeKind.Reference:
                if (depth >= MaxDepth || rng.Next(5) == 0) return 0;
                return Object(type, key, depth + 1);
            default:
                throw new Unsupported($"类型 {type} 的输入值");
        }
    }

    private ulong SharedInteger(int which)
    {
        var rng = Rng($"shared{which}");
        return Hints.Constants.Count > 0 && rng.Next(2) == 0 ? Hints.Constants[rng.Next(Hints.Constants.Count)] : (ulong)rng.Next(-2, 16);
    }

    /// <summary>declared 类型（或其具体子类）的输入对象；字符串、数组按内容合成。</summary>
    public ulong Object(TypeRef declared, string key, int depth)
    {
        var rng = Rng(key + "#type");
        if (declared.Equals(Types.String)) return String(RandomText(rng));
        if (declared is ArrayRef { IsVector: true } array) return Array(array, key, depth, rng.Next(4));
        var type = declared;
        // 提示类型可作为 declared 的值时直接取用；是接口或抽象类时，取 declared 的具体子类中同时满足它的
        var hinted = Hints.Types.Select(t => Index.HintCandidates(declared, t)).Where(c => c.Length > 0).ToArray();
        if (hinted.Length > 0 && rng.Next(2) == 0)
        {
            var group = hinted[rng.Next(hinted.Length)];
            type = group[rng.Next(group.Length)];
        }
        else if (declared is not DefinitionRef { Definition: { IsInterface: false } d } || (d.Attributes & TypeAttributes.Abstract) != 0 || declared.Equals(Types.Object))
        {
            var candidates = Index.Candidates(declared);
            if (candidates.Length == 0) return 0;
            type = candidates[rng.Next(candidates.Length)];
        }
        return type is DefinitionRef concrete ? Instance(concrete, key, depth) : throw new Unsupported($"对象 {type} 的布局");
    }

    /// <summary>恰为 type 类型的输入对象（字段按键取值）。</summary>
    public ulong Instance(DefinitionRef type, string key, int depth)
    {
        if (DelegateModel.Invoke(type) is { } invoke) return DelegateInstance(type, invoke, key, depth);
        if (Layouts.Of(type) is not { } layout) throw new Unsupported($"对象 {type} 的布局");
        var address = Reserve(layout.InstanceSize, 8);
        Put64(address + StorageLayout.ObjectKlass, Klass(type));
        for (TypeRef? current = type; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, []))
            foreach (var slot in Layouts.Of(c)!.Fields)
                Fill(address + (ulong)slot.Offset, slot.Type.Substitute(c.Arguments, []), $"{key}.{slot.Field.Name}", depth);
        return address;
    }

    private ulong Array(ArrayRef type, string key, int depth, int length)
    {
        var size = StorageSize(type.Element);
        var address = Reserve(StorageLayout.ArrayData + length * size, 8);
        Put64(address + StorageLayout.ObjectKlass, Klass(type));
        Put64(address + StorageLayout.ArrayMaxLength, (ulong)length);
        for (var i = 0; i < length; i++) Fill(address + (ulong)(StorageLayout.ArrayData + i * size), type.Element, $"{key}[{i}]", depth);
        return address;
    }

    private static string RandomText(SplitMix rng)
    {
        const string alphabet = "ab/_.\\0Z";
        return rng.Next(6) == 0 ? "" : new string(Enumerable.Range(0, rng.Next(1, 7)).Select(_ => alphabet[rng.Next(alphabet.Length)]).ToArray());
    }

    /// <summary>字符串对象（内容相同的字符串共用一个对象，字面量也是如此）。</summary>
    public ulong String(string text)
    {
        if (strings.TryGetValue(text, out var address)) return address;
        address = Reserve(StorageLayout.StringChars + 2 * (text.Length + 1), 8);
        strings.Add(text, address);
        Put64(address + StorageLayout.ObjectKlass, Klass(Types.String));
        Put32(address + StorageLayout.StringLength, (uint)text.Length);
        Put(address + StorageLayout.StringChars, Encoding.Unicode.GetBytes(text));
        return address;
    }

    /// <summary>值类型 type 的一份数据（不含对象头），用作值类型方法的 this。</summary>
    public ulong ValueStorage(TypeRef type, string key)
    {
        var address = Reserve(StorageSize(type), 8);
        Fill(address, type, key, 0);
        return address;
    }

    /// <summary>第 ordinal 次调用的返回值（按返回类型合成，两侧相同）。</summary>
    public ulong ReturnValue(int ordinal, TypeRef type)
    {
        if (returns.TryGetValue((ordinal, type), out var value)) return value;
        value = Value(type, $"return{ordinal}", 0);
        returns.Add((ordinal, type), value);
        return value;
    }
}
