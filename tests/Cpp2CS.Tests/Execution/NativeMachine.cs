using System.Buffers.Binary;
using Cpp2CS.Facts;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests.Execution;

/// <summary>原生一侧：内存在 Unicorn 中。</summary>
internal sealed class NativeSide(World world, Unicorn uc) : Side(world)
{
    public override void Read(ulong address, Span<byte> bytes) => uc.Read(address, bytes);
    protected override void Store(ulong address, ReadOnlySpan<byte> bytes) => uc.Write(address, bytes);
    public void Logged(ulong address, ReadOnlySpan<byte> bytes) => Log(address, bytes);
}

/// <summary>
/// 在 Unicorn 中执行被测方法的原机器码。映像的 PT_LOAD 段按 VA 映射一次，应用 RELATIVE 重定位，外部符号填毒值；
/// 每个用例把 World 的初始字节写入 Runtime 区、清空 Heap 区、恢复映像中被改写的字节（守卫字节、槽位）。
/// 控制离开被测函数（及其 erratum 跳板）时：到返回哨兵即结束；到运行时服务类 helper 按其语义打桩（判空等普通代码类的 helper 照常执行）；
/// 到其他地址视为调用，
/// 记录调用事件、按 World 给出返回值、回到 LR（LR 为哨兵时是尾调用，随即结束）。
/// 原生侧调用的目标和返回值要与 CIL 侧对应位置的调用一致，所以 CIL 侧先执行，这里按序号取它的被调方法来解读实参与返回类型。
/// </summary>
[ShapeModel("原生执行", Basis = "Unicorn 执行原始 ARM64 机器码（ARM ARM）；运行时服务按 libil2cpp 的行为建模，未建模的调用作为事件如实记录并参与比较")]
internal sealed partial class NativeMachine : IDisposable
{
    private const ulong InstructionLimit = 200_000;
    private readonly Unicorn uc = new();
    private readonly ProgramFacts facts;
    private readonly HashSet<ulong> erratumStubs;
    private readonly Dictionary<ulong, byte> saved = new();
    private readonly Unicorn.CodeHook blockHook;
    private readonly Unicorn.MemoryHook writeHook;
    private readonly Unicorn.InvalidMemoryHook unmappedHook;
    private NativeSide side = null!;
    private CodeFunction function = null!;
    private IReadOnlyList<MethodRef> callees = [];
    private Aapcs64Classifier.Signature tested = null!;
    private TypeRef testedReturnType = null!;
    private const ulong ReturnBuffer = World.StackBase + 0x10000;
    private readonly List<CodeFunction> entered = new();
    private readonly Dictionary<ulong, bool> genericVirtualHelpers = new();
    private readonly HashSet<ulong> writeBarrierBodies = [];
    private Exception? failure;

    public NativeMachine(ProgramFacts facts)
    {
        this.facts = facts;
        erratumStubs = facts.Code.Patches.Values.Select(p => p.Stub).ToHashSet();
        var image = facts.Model.Image;
        // 从 GC 导出符号追踪薄包装；内部调用的纯跳板不一定出现在托管调用目标表中。
        if (image.Exports.TryGetValue("il2cpp_gc_wbarrier_set_field", out var barrier))
            for (var depth = 0; depth < 6 && writeBarrierBodies.Add(barrier); depth++)
            {
                var entry = facts.Code.EntryIndex(barrier);
                if (entry < 0 || facts.Code.Functions[entry].Size > 32) break;
                var calls = facts.Scan.Of(entry).ToArray().Where(r => r.Kind is RefKind.Call or RefKind.TailCall).ToArray();
                if (calls is not [var next]) break;
                barrier = next.Target;
            }
        var pages = image.Ranges.Select(r => (Start: r.Address & ~0xFFFUL, End: (r.Address + r.MemorySize + 0xFFF) & ~0xFFFUL)).OrderBy(p => p.Start).ToList();
        for (var i = 0; i < pages.Count; i++)
        {
            var (start, end) = pages[i];
            while (i + 1 < pages.Count && pages[i + 1].Start <= end) end = Math.Max(end, pages[++i].End);
            uc.Map(start, end - start);
        }
        var bytes = image.Bytes.ToArray();
        var zeroFill = new List<(ulong, ulong)>();
        foreach (var (address, target) in image.RelocatedPointers)
        {
            var mapping = image.Resolve(address);
            if (mapping.Kind == AddressKind.FileBacked) BinaryPrimitives.WriteUInt64LittleEndian(bytes.AsSpan((int)mapping.FileOffset!.Value), target);
            else if (mapping.Kind == AddressKind.ZeroFill) zeroFill.Add((address, target));
        }
        foreach (var address in image.Imports.Keys)
            if (image.Resolve(address) is { Kind: AddressKind.FileBacked } mapping)
                BinaryPrimitives.WriteUInt64LittleEndian(bytes.AsSpan((int)mapping.FileOffset!.Value), 0x6B6B_0000_0000_0000UL | (address & 0xFFFF_FFFF));
        foreach (var range in image.Ranges.Where(r => r.FileSize > 0))
            uc.Write(range.Address, bytes.AsSpan((int)range.FileOffset, (int)range.FileSize));
        Span<byte> pointer = stackalloc byte[8];
        foreach (var (address, target) in zeroFill)
        {
            BinaryPrimitives.WriteUInt64LittleEndian(pointer, target);
            uc.Write(address, pointer);
        }
        uc.Map(World.RuntimeBase, World.RuntimeSize);
        uc.Map(World.HeapBase, World.HeapSize);
        uc.Map(World.ExceptionBase, World.ExceptionSize);
        uc.Map(World.StackBase, World.StackSize);
        uc.Map(World.CodeBase, World.CodeSize);
        var trap = new byte[World.CodeSize];
        for (var i = 0; i < trap.Length; i += 4) BinaryPrimitives.WriteUInt32LittleEndian(trap.AsSpan(i), 0xD4200000); // brk #0
        uc.Write(World.CodeBase, trap);
        blockHook = OnBlock;
        writeHook = OnWrite;
        unmappedHook = OnUnmapped;
        uc.OnBlock(blockHook);
        uc.OnWrite(writeHook);
        uc.OnUnmapped(unmappedHook);
        // 零链接基址的映像头不是真实进程中的空指针页；无效指针访问不能借 ELF 头映射伪装成正常返回。
        uc.OnNullPage((_, _, address, _, _, _) =>
        {
            failure ??= new Unsupported($"原生访问空指针页 0x{address:x}（pc 0x{uc.Reg(Unicorn.RegPc):x}）");
            uc.Stop();
        });
    }

    /// <summary>本次执行覆盖的被测函数基本块（地址, 字节数）。</summary>
    public HashSet<(ulong Address, uint Size)> Covered { get; } = new();

    /// <summary>
    /// 执行 method（入口 entry）。arguments 为按 ABI 各部分排列的实参位型；calleesFromCil 为 CIL 侧依次调用的方法。
    /// 环境不足时抛出 <see cref="Unsupported"/>。
    /// </summary>
    public NativeSide Run(World world, MethodRef method, Aapcs64Classifier.Signature signature, IReadOnlyList<byte[]> arguments, IReadOnlyList<MethodRef> calleesFromCil, ulong? entry = null)
    {
        var start = entry ?? method.Method.Address;
        function = facts.Code.At(start) ?? throw new Unsupported("入口不在代码地图中");
        side = new NativeSide(world, uc);
        tested = signature;
        testedReturnType = method.Method.ReturnType.Substitute(method.TypeArguments, method.MethodArguments);
        callees = calleesFromCil;
        entered.Clear();
        pendingWrites.Clear();
        failure = null;
        ResetUnwind();
        // 映像恢复原状；Heap 区不必清零：每次分配都先写 0
        Restore();
        uc.Write(World.RuntimeBase, world.RuntimeBytes);
        world.Active = side;
        try
        {
            for (var i = 0; i <= 28; i++) uc.SetReg(Unicorn.X(i), 0x5A5A_0000_0000_0000UL | (ulong)i << 8);
            for (var i = 0; i < 32; i++) uc.SetReg(Unicorn.D(i), 0);
            uc.SetReg(Unicorn.X(29), 0);
            uc.SetReg(Unicorn.X(30), World.Sentinel);
            uc.SetReg(Unicorn.RegSp, World.StackBase + World.StackSize - 0x100);
            uc.SetReg(Unicorn.RegNzcv, 0);
            var locations = StructAbi.Arguments(signature);
            if (locations.Length != arguments.Count) throw new InvalidOperationException("实参个数与 ABI 不符");
            var copy = World.StackBase + 0x20000;
            for (var i = 0; i < locations.Length; i++)
            {
                var location = locations[i];
                if (location.Indirect)
                {
                    uc.Write(copy, arguments[i]);
                    side.ArgumentCopy(copy, StructAbi.ArgumentTypes(method)[i], i);
                    PutLocation(location, StructAbi.Bytes(copy, 8), pointer: true);
                    copy = (copy + (ulong)arguments[i].Length + 15) & ~15UL;
                }
                else PutLocation(location, arguments[i]);
            }
            var methodInfo = world.MethodInfo(method);
            PutLocation(signature.MethodInfo, StructAbi.Bytes(methodInfo, 8));
            // 泛型方法的 RGCTX 守卫同时保护全局元数据槽位；槽位初始未解析时让原生代码执行初始化路径。
            if (method.MethodArguments.Count > 0 && facts.Scan.Of(facts.Code.IndexOf(start)).ToArray()
                .Any(r => r.Kind == RefKind.Call && facts.Helpers.At(r.Target)?.Kind == HelperKind.InitMethodRgctx))
                uc.Write(methodInfo + RuntimeLayout.MethodRgctxData, new byte[8]);
            if (signature.Return is { Indirect: true })
            {
                uc.Write(ReturnBuffer, new byte[world.StorageSize(testedReturnType)]);
                uc.SetReg(Unicorn.X(8), ReturnBuffer);
            }
            var error = uc.Start(start, InstructionLimit);
            if (failure is not null) throw failure is Unsupported or InferredCallError or InvalidDataException ? failure : new Unsupported($"原生侧出错：{failure.Message}");
            if (side.Result is null) throw new Unsupported(error != 0 ? $"原生执行出错：{Unicorn.Error(error)} @0x{uc.Reg(Unicorn.RegPc):x}" : "原生执行超过指令数上限");
            return side;
        }
        finally
        {
            world.Active = null;
        }
    }

    private void SetPiece(Aapcs64Classifier.Piece piece, ulong value)
    {
        if (piece.Register.Bank == Bank.Gpr) uc.SetReg(Unicorn.X(piece.Register.Index), value);
        else if (piece.Register.Bank == Bank.Vec) uc.SetReg(Unicorn.D(piece.Register.Index), Side.Mask(value, piece.Width));
        else throw new Unsupported($"实参位置 {piece.Register}");
    }

    private ulong GetPiece(Aapcs64Classifier.Piece piece) => piece.Register.Bank switch
    {
        Bank.Gpr => Side.Mask(uc.Reg(Unicorn.X(piece.Register.Index)), piece.Width),
        Bank.Vec => Side.Mask(uc.Reg(Unicorn.D(piece.Register.Index)), piece.Width),
        _ => throw new Unsupported($"位置 {piece.Register}"),
    };

    private void Restore()
    {
        foreach (var (address, value) in saved) uc.Write(address, [value]);
        saved.Clear();
    }

    private void SaveImage(ulong address, int size)
    {
        Span<byte> original = stackalloc byte[1];
        for (var a = address; a < address + (ulong)size; a++)
            if (!saved.ContainsKey(a) && uc.TryRead(a, original)) saved.Add(a, original[0]);
    }

    private void OnWrite(IntPtr _, int type, ulong address, int size, long value, IntPtr user)
    {
        if (World.Compared(address))
        {
            pendingWrites.Add((address, size));
        }
        else if (address - World.StackBase >= World.StackSize && address - World.ExceptionBase >= World.ExceptionSize) SaveImage(address, size);
    }

    private bool OnUnmapped(IntPtr _, int type, ulong address, int size, long value, IntPtr user)
    {
        failure ??= new Unsupported($"访问未映射地址 0x{address:x}（pc 0x{uc.Reg(Unicorn.RegPc):x}）");
        return false;
    }

    private void OnBlock(IntPtr _, ulong address, uint size, IntPtr user)
    {
        try
        {
            // 递归调用自身入口也是调用
            var recursive = address == function.Start && uc.Reg(Unicorn.X(30)) != World.Sentinel;
            if (!recursive && (function.Contains(address) || erratumStubs.Contains(address) || entered.Any(f => f.Contains(address))))
            {
                if (function.Contains(address)) helperFrame = null;
                // entered 缓存代码范围，不缓存调用帧；同一 helper 的后续调用也必须保存本次入口上下文。
                else if (entered.Any(f => f.Start == address)) EnterHelperFrame();
                if (function.Contains(address)) Covered.Add((address, size));
                return;
            }
            FlushWrites();
            if (address == World.Sentinel) { Finish(); return; }
            if (side.World.DelegateAtTrap(address) is { } binding) { CallDelegate(binding); return; }
            if (facts.Unregistered.At(address) is not null) Call(address);
            else if (facts.Helpers.At(address) is { } helper)
            {
                if (!genericVirtualHelpers.TryGetValue(address, out var genericVirtual))
                    genericVirtualHelpers[address] = genericVirtual = GenericVirtualDispatch.Matches(facts, address);
                if (genericVirtual)
                {
                    uc.SetReg(Unicorn.X(0), GenericVirtualDispatch.Resolve(side.World, uc.Reg(Unicorn.X(0)), uc.Reg(Unicorn.X(1))));
                    GenericVirtualResolutions++;
                    Back();
                    return;
                }
                // 不属于运行时服务的 helper（未内联的判空、条件抛出等普通代码）照常执行，不按分类结论打桩，
                // 免得两侧共用提升器的同一个分类结论而看不出它的错误
                if (helper.Kind is HelperKind.NullCheck or HelperKind.Unknown or HelperKind.CompareExchangeReference && facts.Code.At(address) is { } body && body.Start == address)
                {
                    entered.Add(body);
                    EnterHelperFrame();
                    return;
                }
                Helper(helper);
            }
            // 没有注册入口、也没有 F8 定义身份的托管函数（如方法的本地副本）是普通代码：照常执行，不打桩、不记调用事件。
            // CIL 侧对应的调用由恢复路径标为透明（执行被认定方法的方法体），两侧的可观察事件都来自实际执行。
            else if (side.World.Index.MethodsAt(address).FirstOrDefault() is null && facts.Code.At(address) is { } local && local.Start == address
                && facts.Code.RegionOf(address) == CodeRegion.Managed)
            {
                entered.Add(local);
                EnterHelperFrame();
                return;
            }
            // GC 页标记不参与单线程托管语义；位置写入已由原始原子指令执行并记入内存对照。
            else if (writeBarrierBodies.Contains(address)
                || facts.Code.Word(address) is { } branch && A64.IsB(branch) && writeBarrierBodies.Contains(A64.Imm26Target(branch, address))) Back();
            else Call(address);
        }
        catch (PlannedThrow e)
        {
            try { RaiseObject(e.Object); }
            catch (Exception failure2) { failure ??= failure2; uc.Stop(); }
        }
        catch (Exception e)
        {
            failure ??= e;
            uc.Stop();
        }
    }

    private void Finish()
    {
        var returned = tested.Return;
        if (returned is null) side.Return("void");
        else side.Return(string.Join(", ", side.World.Index.StructAbi.Observable(testedReturnType,
            ReadLocation(returned, returned.Indirect ? ReturnBuffer : null)).Select(v => $"0x{v:x}")));
        uc.Stop();
    }

    /// <summary>从 helper 或被调方法返回：回到 LR；LR 是哨兵时被测方法随即结束。</summary>
    private void Back()
    {
        var lr = uc.Reg(Unicorn.X(30));
        if (lr == World.Sentinel) Finish();
        else uc.SetReg(Unicorn.RegPc, lr);
    }

    public int InferredIdentityChecks { get; private set; }
    public int GenericVirtualResolutions { get; private set; }

    private void Call(ulong address)
    {
        var world = side.World;
        var ordinal = side.CallOrdinal;
        var expected = ordinal < callees.Count ? callees[ordinal] : null;
        MethodRef callee;
        if (facts.Unregistered.At(address) is { } identity)
        {
            var hidden = identity.Abi.MethodInfo is { } piece ? GetPiece(new Aapcs64Classifier.Piece(piece.Register, piece.Width, piece.Offset))
                : throw new InferredCallError($"0x{address:x}：隐藏 MethodInfo 在栈上");
            callee = InferredCallIdentity.Resolve(world, identity, hidden, expected);
            InferredIdentityChecks++;
            // 核对完整 MethodRef 后才使用其注册/合成入口记事件。未注册专用体可能与共享体地址不同。
            address = world.Index.CodeAddress(callee);
        }
        else callee = expected is not null && world.Index.CodeAddress(expected) == address ? expected
            : world.Index.MethodsAt(address).FirstOrDefault() ?? throw new Unsupported($"调用未知目标 0x{address:x}");
        var signature = world.Index.StructAbi.Signature(callee);
        var types = StructAbi.ArgumentTypes(callee);
        var locations = StructAbi.Arguments(signature);
        var rawArguments = locations.Select(a => ReadLocation(a)).ToArray();
        var arguments = world.Index.StructAbi.ObservableArguments(side, types, rawArguments);
        if (side.RuntimeTypeReturn(callee, arguments) is { } reflected)
        {
            var reflectionResult = signature.Return ?? throw new Unsupported("反射方法没有返回位置");
            PutLocation(reflectionResult, StructAbi.Bytes(reflected, world.StorageSize(callee.Method.ReturnType)));
            Back();
            return;
        }
        if (callee.Method is { Name: "ToString", IsStatic: false, Parameters.Count: 0, Owner.FullName: "System.Enum" }
            && arguments is [var receiver] && receiver >= World.StackBase
            && receiver + RuntimeLayout.ObjectHeaderSize + 8 <= World.StackBase + World.StackSize
            && side.Read64(receiver + RuntimeLayout.ObjectMonitor) == ulong.MaxValue
            && world.TypeOfKlass(side.Read64(receiver + RuntimeLayout.ObjectKlass)) is DefinitionRef { Definition.IsEnum: true } enumType)
        {
            // 原生栈临时对象的 klass、monitor=-1、枚举值构成 Il2CppFakeBox。
            // 只把无参 Enum.ToString 的接收者映射为同值装箱对象；仍比较枚举类型、值、调用与后续内存。
            var size = world.StorageSize(enumType);
            var data = new byte[size];
            side.Read(receiver + RuntimeLayout.ObjectHeaderSize, data);
            var box = side.New(enumType, RuntimeLayout.ObjectHeaderSize + size);
            side.RunClassConstructor(enumType);
            side.Write(box + RuntimeLayout.ObjectHeaderSize, data);
            arguments[0] = box;
        }
        if (callee.Method is { Name: ".ctor", Parameters.Count: 0 } && Side.InExceptionRegion(arguments[0])) { Back(); return; }
        _ = side.NextCall();
        // 异常对象的无参构造不记事件（与 CIL 侧的约定相同）
        MethodRef? instance = null;
        if (Side.IsGenericInstance(callee))
        {
            if (callee.Method.Name == ".ctor" && DelegateConstructorInstance(callee, arguments[0]) is { } constructor) instance = constructor;
            else
            {
                var hidden = StructAbi.Bits(ReadLocation(signature.MethodInfo));
                instance = world.MethodOfInfo(hidden) ?? throw new Unsupported($"调用 {callee} 时隐藏实参 0x{hidden:x} 不是合成的 MethodInfo");
            }
        }
        if (!(callee.Method is { Name: ".ctor", Parameters.Count: 0 } && Side.InExceptionRegion(arguments[0])))
            side.CallEvent(address, world.Index.StructAbi.CallInputs(callee, arguments), instance);
        world.Index.StructAbi.WriteBack(side, callee, ordinal, rawArguments);
        var returnType = callee.Method.ReturnType.Substitute(callee.TypeArguments, callee.MethodArguments);
        if (signature.Return is { } returned)
        {
            var value = side.EnumArrayReturn(callee, arguments) ?? world.ReturnBytes(ordinal, returnType);
            if (returned.Indirect) side.Write(GetPiece(returned.Pieces[0]), value);
            else PutLocation(returned, value);
        }
        Back();
    }

    private void Helper(RuntimeHelper helper)
    {
        if (ExceptionHelper(helper)) return;
        var world = side.World;
        ulong X(int i) => uc.Reg(Unicorn.X(i));
        void Result(ulong value) => uc.SetReg(Unicorn.X(0), value);
        TypeRef TypeOfKlass(ulong klass) => world.TypeOfKlass(klass) ?? throw new Unsupported($"helper {helper} 的 klass 不是合成的");
        switch (helper.Kind)
        {
            case HelperKind.InitMetadata:
            {
                var slot = X(0);
                var usage = facts.Usages.At(slot)?.Usage ?? throw new Unsupported($"0x{slot:x} 不是元数据槽位");
                var value = world.SlotValue(usage);
                SaveImage(slot, 8);
                Span<byte> bytes = stackalloc byte[8];
                BinaryPrimitives.WriteUInt64LittleEndian(bytes, value);
                uc.Write(slot, bytes);
                Result(value);
                break;
            }
            case HelperKind.ClassInit:
                side.RunClassConstructor(TypeOfKlass(X(0)));
                break;
            case HelperKind.InitMethodRgctx:
            {
                var info = X(0);
                if (world.MethodOfInfo(info) is null) throw new Unsupported("泛型上下文初始化的 MethodInfo 不是合成的");
                var offset = checked((int)(info + RuntimeLayout.MethodRgctxData - World.RuntimeBase));
                uc.Write(info + RuntimeLayout.MethodRgctxData, world.RuntimeBytes.Slice(offset, 8));
                break;
            }
            case HelperKind.InitializedTypeInfo or HelperKind.WriteBarrier or HelperKind.MemoryBarrier:
                break;
            case HelperKind.ObjectNew:
            {
                // Object::New → NewAllocSpecific：分配后、返回前对该类调用 Runtime::ClassInit（il2cpp_runtime_class_init）
                var type = TypeOfKlass(X(0));
                Result(side.New(type, (int)side.ReadValue(X(0) + RuntimeLayout.ClassInstanceSize, 4)));
                side.RunClassConstructor(type);
                break;
            }
            case HelperKind.NewArray:
                Result(side.NewArray(TypeOfKlass(X(0)) as ArrayRef ?? throw new Unsupported("NewArray 的 klass 不是数组"), (long)X(1)));
                break;
            case HelperKind.Box:
            {
                var type = TypeOfKlass(X(0));
                if (type is DefinitionRef { Definition.FullName: "System.Nullable" }) throw new Unsupported("Nullable 装箱");
                var size = world.StorageSize(type);
                var data = new byte[size];
                side.Read(X(1), data);
                // Object::Box 也经 NewAllocSpecific 分配（同样触发类初始化），再复制值
                var box = side.New(type, RuntimeLayout.ObjectHeaderSize + size);
                side.RunClassConstructor(type);
                side.Write(box + RuntimeLayout.ObjectHeaderSize, data);
                Result(box);
                break;
            }
            case HelperKind.IsInst:
            {
                var instance = X(0);
                Result(instance != 0 && world.Types.IsAssignable(side.TypeOf(instance), TypeOfKlass(X(1))) ? instance : 0);
                break;
            }
            case HelperKind.Unbox:
                // Object::Unbox 只越过对象头；判空与类型检查由调用方完成。
                Result(X(0) + RuntimeLayout.ObjectHeaderSize);
                break;
            case HelperKind.IsAssignableFrom:
                Result(world.Types.IsAssignable(TypeOfKlass(X(1)), TypeOfKlass(X(0))) ? 1UL : 0);
                break;
            case HelperKind.InterfaceLookup:
            {
                var type = side.TypeOf(X(0)) as DefinitionRef ?? throw new Unsupported("接口查找的接收者不是类");
                var itf = TypeOfKlass(X(1));
                var pair = type.Definition.InterfaceOffsets.FirstOrDefault(p => p.Interface.Substitute(type.Arguments, []).Equals(itf));
                if (pair.Interface is null) throw new Unsupported($"{type} 未实现 {itf}");
                Result(world.Klass(type) + (ulong)(RuntimeLayout.ClassVtable + (pair.Offset + (int)X(2)) * RuntimeLayout.VirtualInvokeDataSize));
                break;
            }
            case HelperKind.GetException:
            {
                var type = world.Types.Corlib(helper.Detail!);
                Result(side.New(type, world.Index.Facts.Layouts.Of(type)!.InstanceSize));
                break;
            }
            case HelperKind.Import when helper.Detail == "modf":
            {
                var fraction = NativeMathLibrary.Modf(BitConverter.Int64BitsToDouble(unchecked((long)uc.Reg(Unicorn.D(0)))), out var integral);
                side.Write(X(0), BitConverter.GetBytes(integral));
                uc.SetReg(Unicorn.D(0), unchecked((ulong)BitConverter.DoubleToInt64Bits(fraction)));
                break;
            }
            case HelperKind.Import when helper.Detail == "sinf":
            {
                var result = NativeMathLibrary.Sinf(BitConverter.UInt32BitsToSingle((uint)uc.Reg(Unicorn.S(0))));
                uc.SetReg(Unicorn.S(0), BitConverter.SingleToUInt32Bits(result));
                break;
            }
            case HelperKind.Import when helper.Detail == "fmodf":
            {
                var result = NativeMathLibrary.Fmodf(BitConverter.UInt32BitsToSingle((uint)uc.Reg(Unicorn.S(0))),
                    BitConverter.UInt32BitsToSingle((uint)uc.Reg(Unicorn.S(1))));
                uc.SetReg(Unicorn.S(0), BitConverter.SingleToUInt32Bits(result));
                break;
            }
            case HelperKind.Import when helper.Detail is "memcpy" or "memmove":
            {
                var data = new byte[X(2)];
                side.Read(X(1), data);
                side.Write(X(0), data);
                break;
            }
            case HelperKind.Import when helper.Detail is "memset":
                side.Write(X(0), Enumerable.Repeat((byte)X(1), (int)X(2)).ToArray());
                break;
            default:
                throw new Unsupported($"helper {helper}");
        }
        Back();
    }

    public void Dispose() => uc.Dispose();
}
