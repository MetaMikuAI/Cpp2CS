using System.Buffers.Binary;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>可观察事件：分配、调用、抛出、返回。State 为事件发生时本侧写过的（受比较区域内）字节的当前值。</summary>
/// <summary>事件与发生时写入日志的长度；比较时按日志重放出两侧当时写过的内存。</summary>
internal sealed record TraceEvent(string Text, int Log);

/// <summary>
/// 一侧（原生或 CIL）的一次执行：内存读写、写入日志与事件序列。
/// 分配规则两侧相同：Heap 区按 16 字节对齐顺序分配、内容为 0、写入 klass；异常类型的对象分配在异常区，不计入比较也不产生事件。
/// 异常类型的无参构造调用不产生事件，显式与隐式异常采用相同对象模型。
/// </summary>
internal abstract partial class Side(World world)
{
    private readonly Dictionary<ulong, byte> written = new();
    private readonly List<(ulong Address, byte Value)> log = [];
    private ulong heapTop = World.HeapBase;
    private ulong exceptionTop = World.ExceptionBase;
    private int calls;
    private readonly List<(ulong Address, int Size, int Argument)> argumentCopies = [];

    /// <summary>按值副本与参数存储是同一逻辑根，栈上的物理地址不要求相同。</summary>
    public void ArgumentCopy(ulong address, TypeRef type, int argument) => argumentCopies.Add((address, World.StorageSize(type), argument));

    public ulong ArgumentPointer(ulong address)
    {
        foreach (var copy in argumentCopies)
            if (address >= copy.Address && address - copy.Address < (ulong)copy.Size)
                return 0xf300000000000000UL | (ulong)copy.Argument << 32 | (address - copy.Address);
        return address;
    }

    public World World { get; } = world;
    public List<TraceEvent> Events { get; } = [];
    /// <summary>结果：return 值、throw 类型；null 表示尚未结束。</summary>
    public string? Result { get; protected set; }
    public IReadOnlyDictionary<ulong, byte> Written => written;

    public abstract void Read(ulong address, Span<byte> bytes);
    /// <summary>直接写入本侧内存，不记日志。</summary>
    protected abstract void Store(ulong address, ReadOnlySpan<byte> bytes);

    /// <summary>World 合成的初始字节：写入本侧内存，不记日志。</summary>
    public void Synthesized(ulong address, ReadOnlySpan<byte> bytes) => Store(address, bytes);

    public void Write(ulong address, ReadOnlySpan<byte> bytes)
    {
        Store(address, bytes);
        Log(address, bytes);
    }

    protected void Log(ulong address, ReadOnlySpan<byte> bytes)
    {
        for (var i = 0; i < bytes.Length; i++)
            if (World.Observable(address + (ulong)i))
            {
                written[address + (ulong)i] = bytes[i];
                if (log.Count >= LogLimit) throw new Unsupported("写入记录超过上限");
                log.Add((address + (ulong)i, bytes[i]));
            }
    }

    public ulong Read64(ulong address) { Span<byte> b = stackalloc byte[8]; Read(address, b); return BinaryPrimitives.ReadUInt64LittleEndian(b); }

    public ulong ReadValue(ulong address, int bytes)
    {
        Span<byte> b = stackalloc byte[8];
        b.Clear();
        Read(address, b[..bytes]);
        return BinaryPrimitives.ReadUInt64LittleEndian(b);
    }

    public void WriteValue(ulong address, ulong value, int bytes)
    {
        Span<byte> b = stackalloc byte[8];
        BinaryPrimitives.WriteUInt64LittleEndian(b, value);
        Write(address, b[..bytes]);
    }

    /// <summary>写入日志的条数上限：长循环会使日志无界增长，超过时本例不可检查。</summary>
    private const int LogLimit = 20_000_000;

    /// <summary>按次序写入的可观察字节。</summary>
    public IReadOnlyList<(ulong Address, byte Value)> WriteLog => log;

    public void Event(string text) => Events.Add(new TraceEvent(text, log.Count));

    /// <summary>下一次调用的序号（两侧按同样的顺序取返回值）。</summary>
    public int NextCall() => calls++;
    public int CallOrdinal => calls;

    public bool IsException(TypeRef type) =>
        type is DefinitionRef && World.Types.IsAssignable(type, World.Types.Corlib("System.Exception"));

    public static bool InExceptionRegion(ulong address) => address - World.ExceptionBase < World.ExceptionSize;

    /// <summary>新建 type 的对象（size 为含对象头的大小）：清零、写 klass；非异常对象记一个 new 事件。</summary>
    public ulong New(TypeRef type, int size, string? detail = null)
    {
        var exception = IsException(type);
        ref var cursor = ref exception ? ref exceptionTop : ref heapTop;
        cursor = (cursor + 15) & ~15UL;
        var address = cursor;
        cursor += (ulong)size;
        if (cursor > (exception ? World.ExceptionBase + World.ExceptionSize : World.HeapBase + World.HeapSize)) throw new Unsupported("堆已满");
        World.RegisterObject(address, type);
        Write(address, new byte[size]);
        WriteValue(address + StorageLayout.ObjectKlass, World.Klass(type), 8);
        if (!exception) Event(detail is null ? $"new {type}" : $"new {type} {detail}");
        return address;
    }

    public ulong NewArray(ArrayRef type, long length)
    {
        if (length < 0) throw new Unsupported("负的数组长度（OverflowException 尚未建模）");
        var elementSize = World.StorageSize(type.Element);
        if (length > (long)(World.HeapSize - StorageLayout.ArrayData) / elementSize)
            throw new Unsupported("数组超出验证堆容量");
        var address = New(type, StorageLayout.ArrayData + (int)length * elementSize, $"[{length}]");
        WriteValue(address + StorageLayout.ArrayMaxLength, (ulong)length, 8);
        return address;
    }

    /// <summary>对象的运行时类型（读对象头的 klass）。</summary>
    public TypeRef TypeOf(ulong address) =>
        World.TypeOfKlass(Read64(address + StorageLayout.ObjectKlass)) ?? throw new Unsupported($"0x{address:x} 处不是合成的对象");

    /// <summary>
    /// 调用事件：逻辑方法身份与按托管签名排列的实参叶子（整数按宽度截取，浮点为位型）。
    /// 泛型调用额外记录闭合实例；两侧必须对应同一个实例。
    /// </summary>
    public int CallEvents { get; private set; }
    public bool PlannedThrowReached { get; private set; }
    public void CallEvent(ulong target, IEnumerable<ulong> arguments, MethodRef? instance)
    {
        Event($"call 0x{target:x}({string.Join(", ", arguments.Select(a => $"0x{a:x}"))}){(instance is null ? "" : $" <{instance}>")}");
        PlannedCall();
    }

    public void PlannedCall()
    {
        var ordinal = CallEvents++;
        if (World.ThrowPlan is { } plan && plan.CallEvent == ordinal)
        {
            PlannedThrowReached = true;
            throw new PlannedThrow(ExceptionObject(plan.Type));
        }
    }

    public ulong ExceptionObject(TypeRef type) => New(type, (type is DefinitionRef definition ? World.Index.Layouts.Of(definition) : null)?.InstanceSize
        ?? throw new Unsupported($"异常类型 {type} 缺少布局"));

    public void ThrowObject(ulong value, bool record = true)
    {
        if (record) Event($"throw {TypeOf(value)} @0x{value:x}");
        Result = $"throw @0x{value:x}";
    }

    public static bool IsGenericInstance(MethodRef method) => method.TypeArguments.Count > 0 || method.MethodArguments.Count > 0;

    private readonly HashSet<TypeRef> initialized = new();

    /// <summary>
    /// 类尚未初始化时记一个 cctor 事件，并在本侧记录已初始化状态。
    /// 静态构造本身作为外部行为，不展开执行。
    /// beforefieldinit 类型的初始化时机不受约束（ECMA-335 II.10.5.3），不构成可观察事件。
    /// </summary>
    public void RunClassConstructor(TypeRef type)
    {
        if (!World.Precise(type) || !World.Uninitialized(type) || !initialized.Add(type)) return;
        Event($"cctor {type}");
    }

    /// <summary>执行未在步数或指令数上限内结束。</summary>
    public void Diverge()
    {
        Event("diverge");
        Result = "diverge";
    }

    public void Return(string value)
    {
        Event($"return {value}");
        Result = $"return {value}";
    }

    public static ulong Mask(ulong value, int width) => width >= 64 ? value : value & ((1UL << width) - 1);
}

/// <summary>两侧执行结果的比较。</summary>
internal static class Trace
{
    /// <summary>
    /// 第一处不同；相同为 null。每个事件发生时，两侧写过的内存（未写的字节取初值）须相同：按事件次序重放两侧的写入日志，
    /// 增量维护取值不同的地址，等价于逐事件比较两侧当时的全部写入。
    /// </summary>
    public static string? Difference(World world, Side native, Side cil)
    {
        var (nState, cState) = (new Dictionary<ulong, byte>(), new Dictionary<ulong, byte>());
        var differs = new SortedSet<ulong>();
        var (nAt, cAt) = (0, 0);
        byte Value(Dictionary<ulong, byte> state, ulong address) => state.TryGetValue(address, out var v) ? v : world.Initial(address);
        void Replay(Side side, Dictionary<ulong, byte> state, ref int at, int end)
        {
            for (; at < end; at++)
            {
                var (address, value) = side.WriteLog[at];
                state[address] = value;
                if (Value(nState, address) != Value(cState, address)) differs.Add(address); else differs.Remove(address);
            }
        }
        var count = Math.Max(native.Events.Count, cil.Events.Count);
        for (var i = 0; i < count; i++)
        {
            var n = i < native.Events.Count ? native.Events[i] : null;
            var c = i < cil.Events.Count ? cil.Events[i] : null;
            if (n?.Text != c?.Text) return $"事件 {i}：左侧 {n?.Text ?? "（无）"}，右侧 {c?.Text ?? "（无）"}";
            Replay(native, nState, ref nAt, n!.Log);
            Replay(cil, cState, ref cAt, c!.Log);
            if (differs.Count > 0)
            {
                var address = differs.Min;
                return $"事件 {i}（{n.Text}）时内存 0x{address:x}：左侧 {Value(nState, address):x2}，右侧 {Value(cState, address):x2}";
            }
        }
        if (native.Result != cil.Result) return $"结局：左侧 {native.Result}，右侧 {cil.Result}";
        Replay(native, nState, ref nAt, native.WriteLog.Count);
        Replay(cil, cState, ref cAt, cil.WriteLog.Count);
        return differs.Count == 0 ? null : $"结局时堆内存 0x{differs.Min:x} 不同";
    }
}
