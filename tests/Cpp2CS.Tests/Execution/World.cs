using System.Buffers.Binary;
using System.Reflection;
using System.Text;
using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

/// <summary>合成环境不足以执行（缺类型、不支持的 helper 等）：该用例判为不可检查。</summary>
internal sealed class Unsupported(string reason) : Exception(reason);

/// <summary>
/// 跨用例共用的索引：地址 ↔ 方法、无代码方法的伪入口、抽象类型的具体实现候选。伪入口按首次使用的顺序分配，同一次运行内确定。
/// </summary>
internal sealed class WorldIndex
{
    private readonly Dictionary<ulong, List<MethodRef>> byAddress = new();
    private readonly Dictionary<MethodRef, ulong> addresses = new();
    private readonly Dictionary<MethodRef, ulong> fake = new();
    private readonly Dictionary<ulong, MethodRef> fakeMethods = new();
    private readonly Dictionary<TypeRef, DefinitionRef[]> concrete = new();
    private readonly Dictionary<TypeRef, DefinitionRef[]> candidates = new();
    private readonly Dictionary<(TypeRef, TypeRef), TypeRef[]> hintCandidates = new();

    public WorldIndex(ProgramFacts facts, ManagedTypes types)
    {
        Facts = facts;
        Types = types;
        Abi = new ManagedAbi(facts.Layouts);
        StructAbi = new StructAbi(this);
        EagerTypes = EagerClassConstruction.Read(facts);
        void Add(ulong address, MethodRef method)
        {
            if (!byAddress.TryGetValue(address, out var list)) byAddress.Add(address, list = []);
            if (!list.Contains(method)) list.Add(method);
            addresses.TryAdd(method, address);
        }
        foreach (var method in facts.Model.Methods.Where(m => m.Address != 0)) Add(method.Address, new MethodRef(method, [], []));
        foreach (var entry in facts.Registrations.Entries)
            if (entry.Method is { } method && entry.Address != 0) Add(entry.Address, method);
    }

    public ProgramFacts Facts { get; }
    public ManagedTypes Types { get; }
    public ManagedAbi Abi { get; }
    public StructAbi StructAbi { get; }
    public IReadOnlySet<TypeDef> EagerTypes { get; }

    /// <summary>
    /// 方法的代码地址。泛型实例先找自身，再找共享实现（引用类型的实参换成 System.Object，IL2CPP 的共享规则）；
    /// 都没有（抽象、未生成的实例）时分配伪入口。
    /// </summary>
    public ulong CodeAddress(MethodRef method)
    {
        if (addresses.TryGetValue(method, out var address)) return address;
        if (Shared(method) is { } shared && addresses.TryGetValue(shared, out address)) return address;
        if (fake.TryGetValue(method, out address)) return address;
        address = World.CodeBase + 0x100 + (ulong)fake.Count * 4;
        fake.Add(method, address);
        fakeMethods.Add(address, method);
        return address;
    }

    /// <summary>
    /// 共享形式：引用类型的实参换成 System.Object，枚举换成同底层类型的 System.Int32Enum 等（IL2CPP 合成的共享枚举），
    /// 值类型泛型实例的实参递归处理；与原方法相同时为 null。
    /// </summary>
    private MethodRef? Shared(MethodRef method)
    {
        TypeRef Canonical(TypeRef type) => ManagedTypes.IsReferenceType(type) ? Types.Object
            : type is DefinitionRef { Definition.IsEnum: true } e ? Types.Corlib($"System.{ManagedTypes.PrimitiveName(ManagedTypes.Underlying(e))}Enum")
            : type is DefinitionRef { Arguments.Count: > 0 } d ? d with { Arguments = d.Arguments.Select(Canonical).ToArray() } : type;
        var shared = method with { TypeArguments = method.TypeArguments.Select(Canonical).ToArray(), MethodArguments = method.MethodArguments.Select(Canonical).ToArray() };
        return shared.Equals(method) ? null : shared;
    }

    /// <summary>type 的虚表第 slot 项，按 type 的实参实例化；槽位为空时为 null。</summary>
    public static MethodRef? VTableEntry(DefinitionRef type, int slot) =>
        slot < type.Definition.VTable.Count && type.Definition.VTable[slot] is { } entry ? Instantiate(entry, type) : null;

    /// <summary>
    /// 虚表条目在 within 中的实例：元数据以 MethodDef 编码的条目没有类实参，取 within 继承链上该所有者的实例；
    /// 以 MethodRef 编码的条目的实参按 within 的泛型参数代入。
    /// </summary>
    public static MethodRef Instantiate(MethodRef method, DefinitionRef within)
    {
        if (method.TypeArguments.Count == 0 && method.Method.Owner.GenericParameters.Count > 0)
        {
            for (TypeRef? current = within; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, []))
                if (c.Definition == method.Method.Owner) return method with { TypeArguments = c.Arguments };
            throw new Unsupported($"无法在 {within} 中实例化 {method}");
        }
        return method with { TypeArguments = method.TypeArguments.Select(a => a.Substitute(within.Arguments, [])).ToArray() };
    }

    /// <summary>地址上的方法（ICF 合并的全部所有者，或伪入口对应的方法）。</summary>
    public IReadOnlyList<MethodRef> MethodsAt(ulong address) =>
        fakeMethods.TryGetValue(address, out var method) ? [method] : byAddress.TryGetValue(address, out var list) ? list : [];

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
        found = Facts.Model.Types
            .Where(t => IsClass(t) && t.GenericParameters.Count == 0)
            .Select(t => new DefinitionRef(t, []))
            .Concat(Facts.Model.RuntimeTypes.OfType<DefinitionRef>().Where(d => d.Arguments.Count > 0 && IsClass(d.Definition) && Closed(d) && !FieldLayouts.IsFullyShared(d)).Distinct())
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
/// 两侧共用的合成运行时（每个用例一份）：按 IL2CPP 运行时布局在 Runtime 区合成 Il2CppClass、MethodInfo、FieldInfo、字符串、
/// 静态字段块与输入对象图。合成是惰性的、按键记忆的，两侧拿到的地址相同；Runtime 区的这份字节是初始状态，
/// 执行中的写入只落在各侧自己的内存上。执行期间的分配在 Heap 区由各侧按同一规则进行（见 <see cref="Side"/>）。
/// 输入取值由 (用例种子, 键) 的稳定散列决定，与合成顺序无关。
/// </summary>
internal sealed partial class World
{
    public const ulong RuntimeBase = 0x7000_0000_0000, RuntimeSize = 0x100_0000;
    public const ulong HeapBase = 0x7100_0000_0000, HeapSize = 0x100_0000;
    /// <summary>异常对象：不计入比较（判空、越界等检查在原生侧由 helper 直接抛出，没有对应的分配）。</summary>
    public const ulong ExceptionBase = 0x7180_0000_0000, ExceptionSize = 0x10_0000;
    public const ulong StackBase = 0x7200_0000_0000, StackSize = 0x10_0000;
    /// <summary>伪代码区：返回哨兵与无实现方法的伪入口（执行到这里即被钩子截获）。</summary>
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
    private FieldLayouts Layouts => Index.Facts.Layouts;
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

    /// <summary>Il2CppType*：即 &amp;klass->byval_arg。</summary>
    public ulong TypePointer(TypeRef type) => Klass(type) + RuntimeLayout.ClassByvalArg;

    /// <summary>RuntimeTypeHandle（Il2CppType*）对应的类型。</summary>
    public TypeRef TypeOfHandle(ulong handle) =>
        TypeOfKlass(handle - RuntimeLayout.ClassByvalArg) ?? throw new Unsupported($"0x{handle:x} 不是合成的类型句柄");

    public ulong Klass(TypeRef type)
    {
        if (klasses.TryGetValue(type, out var klass)) return klass;
        IReadOnlyList<MethodRef?> vtable;
        DefinitionRef? definition = null;
        switch (type)
        {
            case DefinitionRef d:
                definition = d;
                // 实例化不了的条目留空：用到时原生侧读到 0 而出错，判为不可检查
                vtable = Enumerable.Range(0, d.Definition.VTable.Count).Select(i =>
                {
                    try { return WorldIndex.VTableEntry(d, i); }
                    catch (Unsupported) { return null; }
                }).ToArray();
                break;
            case ArrayRef { IsVector: true }:
                vtable = Types.Corlib("System.Array").Definition.VTable;
                break;
            default:
                throw new Unsupported($"类型 {type} 的 klass");
        }
        klass = Reserve(RuntimeLayout.ClassVtable + vtable.Count * RuntimeLayout.VirtualInvokeDataSize, 8);
        klasses.Add(type, klass);
        klassTypes.Add(klass, type);

        var name = definition?.Definition.Name ?? type.ToString();
        Put64(klass + RuntimeLayout.ClassImage, klass);
        Put64(klass + 0x10, CString(name));
        Put64(klass + 0x18, CString(definition?.Definition.Namespace ?? ""));
        Put8(klass + RuntimeLayout.ClassByvalArg + 0xA, TypeEnum(type));
        Put64(klass + RuntimeLayout.ClassKlass, klass);
        // CodeGenModule 注册的 eager 类型在程序启动时完成构造；完整注册表与特性交叉核对见 EagerClassConstruction。
        var pending = definition is { } withCctor && withCctor.Definition.Methods.Any(m => m.Name == ".cctor") && !type.Equals(initializedOwner)
            && !Index.EagerTypes.Contains(withCctor.Definition) && Rng($"cctor:{type}").Next(3) == 0;
        if (pending) uninitialized.Add(type);
        Put32(klass + RuntimeLayout.ClassCctorStarted, pending ? 0u : 1);
        Put32(klass + RuntimeLayout.ClassCctorFinishedOrNoCctor, pending ? 0u : 1);

        var hierarchy = new List<TypeRef>();
        if (type is ArrayRef array)
        {
            var element = Klass(array.Element);
            Put64(klass + RuntimeLayout.ClassElementClass, element);
            Put64(klass + RuntimeLayout.ClassCastClass, element);
            Put64(klass + RuntimeLayout.ClassParent, Klass(Types.Corlib("System.Array")));
            Put32(klass + RuntimeLayout.ClassInstanceSize, RuntimeLayout.ArrayData);
            Put32(klass + RuntimeLayout.ClassElementSize, (uint)StorageSize(array.Element));
            Put8(klass + RuntimeLayout.ClassRank, 1);
            Put32(klass + RuntimeLayout.ClassFlags, (uint)(TypeAttributes.Public | TypeAttributes.Sealed));
            hierarchy.AddRange(Hierarchy(Types.Corlib("System.Array")));
            hierarchy.Add(type);
        }
        else
        {
            var d = definition!;
            var layout = Layouts.Of(d) ?? throw new Unsupported($"类型 {d} 没有布局");
            var underlying = ManagedTypes.Underlying(d);
            Put64(klass + RuntimeLayout.ClassElementClass, klass);
            Put64(klass + RuntimeLayout.ClassCastClass, underlying.Equals(d) ? klass : Klass(underlying));
            if (d.Definition.DeclaringType is { } outer)
                Put64(klass + RuntimeLayout.ClassDeclaringType, Klass(new DefinitionRef(outer, d.Arguments.Take(outer.GenericParameters.Count).ToArray())));
            if (d.Definition.BaseType?.Substitute(d.Arguments, []) is { } baseType) Put64(klass + RuntimeLayout.ClassParent, Klass(baseType));
            Put64(klass + RuntimeLayout.ClassStaticFields, Reserve(Math.Max(layout.StaticSize, 8)));
            Put32(klass + RuntimeLayout.ClassInstanceSize, (uint)layout.InstanceSize);
            Put32(klass + RuntimeLayout.ClassActualSize, (uint)layout.ActualSize);
            Put32(klass + RuntimeLayout.ClassElementSize, d.Definition.IsValueType ? (uint)layout.ValueSize : 8);
            Put32(klass + RuntimeLayout.ClassStaticFieldsSize, (uint)layout.StaticSize);
            Put32(klass + RuntimeLayout.ClassFlags, (uint)d.Definition.Attributes);
            Put32(klass + RuntimeLayout.ClassToken, d.Definition.Token);
            Put8(klass + RuntimeLayout.ClassMinimumAlignment, (byte)layout.MinimumAlignment);
            var offsets = d.Definition.InterfaceOffsets;
            if (offsets.Count > 0)
            {
                var pairs = Reserve(offsets.Count * RuntimeLayout.InterfaceOffsetPairSize, 8);
                for (var i = 0; i < offsets.Count; i++)
                {
                    Put64(pairs + (ulong)(i * RuntimeLayout.InterfaceOffsetPairSize), Klass(offsets[i].Interface.Substitute(d.Arguments, [])));
                    Put32(pairs + (ulong)(i * RuntimeLayout.InterfaceOffsetPairSize + 8), (uint)offsets[i].Offset);
                }
                Put64(klass + RuntimeLayout.ClassInterfaceOffsets, pairs);
                Put16(klass + RuntimeLayout.ClassInterfaceOffsetsCount, (ushort)offsets.Count);
            }
            // 泛型类实例的 RGCTX（Class+0xC0）：内联的泛型类方法经 MethodInfo→klass→rgctx_data 取类（如 IUniTaskSource<T>）。
            if (d.Arguments.Count > 0 && Index.Facts.Registrations.Rgctx.TryGetValue((d.Definition.Assembly, d.Definition.Token), out var classRgctx))
                Put64(klass + RuntimeLayout.ClassRgctxData, RgctxArray(classRgctx, t => t.Substitute(d.Arguments, [])));
            hierarchy.AddRange(Hierarchy(d));
            byte flags1 = 0x03;
            if (d.Definition.IsEnum) flags1 |= 0x04;
            if (layout.HasReferences) flags1 |= 0x20;
            Put8(klass + RuntimeLayout.ClassBitflags1, flags1);
        }
        Put8(klass + RuntimeLayout.ClassBitflags2, 0x21);
        Put16(klass + RuntimeLayout.ClassVtableCount, (ushort)vtable.Count);
        var chain = Reserve(hierarchy.Count * 8, 8);
        for (var i = 0; i < hierarchy.Count; i++) Put64(chain + (ulong)(i * 8), hierarchy[i].Equals(type) ? klass : Klass(hierarchy[i]));
        Put64(klass + RuntimeLayout.ClassTypeHierarchy, chain);
        Put8(klass + RuntimeLayout.ClassTypeHierarchyDepth, (byte)hierarchy.Count);
        for (var i = 0; i < vtable.Count; i++)
            if (vtable[i] is { } method)
            {
                var entry = klass + (ulong)(RuntimeLayout.ClassVtable + i * RuntimeLayout.VirtualInvokeDataSize);
                Put64(entry, Index.CodeAddress(method));
                Put64(entry + 8, MethodInfo(method));
            }
        return klass;
    }

    /// <summary>从 System.Object 到 type 的继承链（接口只有自身）。</summary>
    private static List<TypeRef> Hierarchy(DefinitionRef type)
    {
        var chain = new List<TypeRef>();
        for (TypeRef? current = type; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, [])) chain.Add(c);
        chain.Reverse();
        return chain;
    }

    private byte TypeEnum(TypeRef type) => type switch
    {
        ArrayRef => 0x1d,
        DefinitionRef d => ManagedTypes.PrimitiveName(d) switch
        {
            "Boolean" => 0x02, "Char" => 0x03, "SByte" => 0x04, "Byte" => 0x05, "Int16" => 0x06, "UInt16" => 0x07, "Int32" => 0x08, "UInt32" => 0x09,
            "Int64" => 0x0a, "UInt64" => 0x0b, "Single" => 0x0c, "Double" => 0x0d, "IntPtr" => 0x18, "UIntPtr" => 0x19, "Void" => 0x01,
            _ when d.Equals(Types.String) => 0x0e, _ when d.Equals(Types.Object) => 0x1c,
            _ when d.Arguments.Count > 0 => 0x15, _ when d.Definition.IsValueType => 0x11, _ => 0x12,
        },
        _ => 0,
    };

    public ulong MethodInfo(MethodRef method)
    {
        if (methodInfos.TryGetValue(method, out var info)) return info;
        info = Reserve(RuntimeLayout.MethodInfoSize, 8);
        methodInfos.Add(method, info);
        methodInfoOwners.Add(info, method);
        var code = Index.CodeAddress(method);
        Put64(info + RuntimeLayout.MethodPointer, code);
        Put64(info + RuntimeLayout.MethodVirtualPointer, code);
        Put64(info + RuntimeLayout.MethodName, CString(method.Method.Name));
        // 调用方几乎不读 MethodInfo 的内容；声明类型合成不了（如未实例化的泛型定义）时 klass 留 0
        try { Put64(info + RuntimeLayout.MethodKlass, Klass(method.DeclaringType)); }
        catch (Unsupported) { }
        Put32(info + RuntimeLayout.MethodToken, method.Method.Token);
        Put16(info + RuntimeLayout.MethodFlags, (ushort)method.Method.Attributes);
        Put16(info + RuntimeLayout.MethodSlot, (ushort)method.Method.Slot);
        Put8(info + RuntimeLayout.MethodParametersCount, (byte)method.Method.Parameters.Count);
        // 泛型方法实例的 RGCTX 数组（MethodInfo+0x38）：按元数据的 RGCTX 定义代入实例实参（内联的泛型方法经它取类，如 Array.Empty<T> 的 EmptyArray<T>）。
        if (method.MethodArguments.Count > 0
            && Index.Facts.Registrations.Rgctx.TryGetValue((method.Method.Owner.Assembly, method.Method.Token), out var entries))
            Put64(info + RuntimeLayout.MethodRgctxData, RgctxArray(entries, t => t.Substitute(method.TypeArguments, method.MethodArguments)));
        return info;
    }

    private int rgctxDepth;

    /// <summary>RGCTX 数组：按元数据的 RGCTX 定义代入实参（内联的泛型代码经它取类、类型与方法）。实例化不了的条目留 0。</summary>
    private ulong RgctxArray(RgctxEntry[] entries, Func<TypeRef, TypeRef> close)
    {
        var array = Reserve(8 * Math.Max(entries.Length, 1), 8);
        if (rgctxDepth >= 3) return array;
        rgctxDepth++;
        try
        {
            for (var i = 0; i < entries.Length; i++)
            {
                try
                {
                    Put64(array + (ulong)(8 * i), entries[i] switch
                    {
                        { Kind: RgctxKind.Class, Value: TypeRef t } => Klass(close(t is ByRefRef r ? r.Element : t)),
                        { Kind: RgctxKind.Type, Value: TypeRef t } => TypePointer(close(t)),
                        { Kind: RgctxKind.Array, Value: TypeRef t } => Klass(new ArrayRef(close(t is ByRefRef r ? r.Element : t), 1)),
                        { Kind: RgctxKind.Method, Value: MethodRef m } => MethodInfo(m with { TypeArguments = m.TypeArguments.Select(close).ToArray(), MethodArguments = m.MethodArguments.Select(close).ToArray() }),
                        _ => 0,
                    });
                }
                catch (Unsupported) { }
            }
        }
        finally { rgctxDepth--; }
        return array;
    }

    /// <summary>合成的 MethodInfo 对应的方法；不是合成的时为 null。</summary>
    public MethodRef? MethodOfInfo(ulong info) => methodInfoOwners.GetValueOrDefault(info);

    public ulong FieldInfo(FieldRef field)
    {
        if (fieldInfos.TryGetValue(field, out var info)) return info;
        info = Reserve(0x20, 8);
        fieldInfos.Add(field, info);
        Put64(info + RuntimeLayout.FieldName, CString(field.Field.Name));
        Put64(info + RuntimeLayout.FieldParent, Klass(field.DeclaringType));
        Put32(info + RuntimeLayout.FieldOffset, (uint)FieldOffset(field));
        return info;
    }

    /// <summary>元数据槽位初始化后的值。</summary>
    public ulong SlotValue(Usage usage) => usage.Kind switch
    {
        UsageKind.TypeInfo => Klass((TypeRef)usage.Value),
        UsageKind.Il2CppType => TypePointer((TypeRef)usage.Value),
        UsageKind.MethodDef or UsageKind.MethodRef => MethodInfo((MethodRef)usage.Value),
        UsageKind.FieldInfo => FieldInfo((FieldRef)usage.Value),
        UsageKind.StringLiteral => String((string)usage.Value),
        _ => throw new Unsupported($"槽位种类 {usage.Kind}"),
    };

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
        var block = BinaryPrimitives.ReadUInt64LittleEndian(runtime.AsSpan((int)(Klass(field.DeclaringType) + RuntimeLayout.ClassStaticFields - RuntimeBase), 8));
        return block + (ulong)FieldOffset(field);
    }

    /// <summary>给方法会读写的静态字段填入初值（其余静态字段保持 0，避免合成整个类型闭包）。</summary>
    public void PrepareStatic(FieldRef field)
    {
        if (!preparedStatics.Add(field)) return;
        var address = StaticAddress(field);
        Fill(address, FieldType(field), $"static:{field}", 0);
    }

    private void Fill(ulong address, TypeRef type, string key, int depth)
    {
        if (Types.Kind(type) == TypeKind.Struct)
        {
            RegisterValue(address, type);
            if (type is not DefinitionRef d || Layouts.Of(d) is not { } layout) throw new Unsupported($"结构 {type} 的布局");
            foreach (var slot in layout.Fields)
                Fill(address + (ulong)(slot.Offset - RuntimeLayout.ObjectHeaderSize), slot.Type.Substitute(d.Arguments, []), $"{key}.{slot.Field.Name}", depth);
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
            case TypeKind.Pointer: return type is ByRefRef b ? ValueStorage(b.Element, key) : 0;
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
        Put64(address + RuntimeLayout.ObjectKlass, Klass(type));
        for (TypeRef? current = type; current is DefinitionRef c; current = c.Definition.BaseType?.Substitute(c.Arguments, []))
            foreach (var slot in Layouts.Of(c)!.Fields)
                Fill(address + (ulong)slot.Offset, slot.Type.Substitute(c.Arguments, []), $"{key}.{slot.Field.Name}", depth);
        return address;
    }

    private ulong Array(ArrayRef type, string key, int depth, int length)
    {
        var size = StorageSize(type.Element);
        var address = Reserve(RuntimeLayout.ArrayData + length * size, 8);
        Put64(address + RuntimeLayout.ObjectKlass, Klass(type));
        Put64(address + RuntimeLayout.ArrayMaxLength, (ulong)length);
        for (var i = 0; i < length; i++) Fill(address + (ulong)(RuntimeLayout.ArrayData + i * size), type.Element, $"{key}[{i}]", depth);
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
        address = Reserve(RuntimeLayout.StringChars + 2 * (text.Length + 1), 8);
        strings.Add(text, address);
        Put64(address + RuntimeLayout.ObjectKlass, Klass(Types.String));
        Put32(address + RuntimeLayout.StringLength, (uint)text.Length);
        Put(address + RuntimeLayout.StringChars, Encoding.Unicode.GetBytes(text));
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
