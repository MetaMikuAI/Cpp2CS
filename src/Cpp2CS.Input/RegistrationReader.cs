#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Model;

namespace Cpp2CS.Input
{
    /// <summary>
    /// 按 Unity 2022.3.62f2 libil2cpp 头文件（il2cpp-class-internals.h / il2cpp-metadata.h）的精确布局，
    /// 直接从映像读取 CodeRegistration / MetadataRegistration 中的代码入口表。
    /// 偏移由 gcc 对 Il2CppVersions/headers/2022.3.62f2.h 计算（LP64，与 AArch64 一致）。
    /// 指针一律经 <see cref="ImageDocument.ReadPointer"/> 读取，以应用 RELATIVE 重定位。
    /// </summary>
    public sealed class RegistrationReader
    {
        // Il2CppCodeRegistration
        private const int CrReversePInvokeCount = 0, CrReversePInvoke = 8, CrGenericMethodCount = 16, CrGenericMethods = 24,
            CrGenericAdjustors = 32, CrInvokerCount = 40, CrInvokers = 48, CrUnresolvedCount = 56, CrUnresolvedVirtual = 64,
            CrUnresolvedInstance = 72, CrUnresolvedStatic = 80, CrInteropCount = 88, CrInterop = 96, CrModuleCount = 120, CrModules = 128;
        // Il2CppCodeGenModule
        private const int CmName = 0, CmMethodCount = 8, CmMethods = 16, CmAdjustorCount = 24, CmAdjustors = 32, CmInvokerIndices = 40,
            CmReversePInvokeCount = 48, CmReversePInvokeIndices = 56, CmRgctxRangeCount = 64, CmRgctxRanges = 72, CmRgctxCount = 80,
            CmRgctxs = 88, CmModuleInitializer = 104;
        // Il2CppMetadataRegistration
        private const int MrGenericMethodTableCount = 32, MrGenericMethodTable = 40, MrTypesCount = 48, MrTypes = 56,
            MrUsagesCount = 112, MrUsages = 120;
        private const int InteropSize = 56, AdjustorPairSize = 16, TokenIndexTupleSize = 24, RgctxSize = 16, TokenRangeSize = 12, GenericMethodTableSize = 16;

        private readonly ImageDocument image;
        private readonly ProgramModel model;
        private readonly List<string> problems = new();

        private RegistrationReader(ImageDocument image, ProgramModel model)
        {
            this.image = image;
            this.model = model;
        }

        public IReadOnlyList<string> Problems => problems;

        public static (Registrations Registrations, IReadOnlyList<string> Problems) Read(ProgramModel model, ulong codeRegistration, ulong metadataRegistration)
        {
            var reader = new RegistrationReader(model.Image, model);
            return (reader.Build(codeRegistration, metadataRegistration), reader.problems);
        }

        private ulong Pointer(ulong address) => image.ReadPointer(address) ?? throw new InvalidDataException($"0x{address:x} 引用外部符号，不是注册表指针");
        private uint U32(ulong address) => image.ReadU32(address);
        private int I32(ulong address) => image.ReadI32(address);
        private ulong[] Pointers(ulong array, long count)
        {
            if (count == 0) return Array.Empty<ulong>();
            if (array == 0) throw new InvalidDataException($"注册表数组为空指针但长度为 {count}");
            var result = new ulong[count];
            for (long i = 0; i < count; i++) result[i] = Pointer(array + (ulong)i * 8);
            return result;
        }

        private Registrations Build(ulong code, ulong meta)
        {
            var entries = new List<CodeEntry>();
            void Add(ulong address, EntryKind kind, MethodRef? method, int index, string? detail)
            {
                if (address == 0) return;
                if (!image.IsExecutable(address)) { problems.Add($"{kind} #{index} 指向非代码地址 0x{address:x}"); return; }
                entries.Add(new CodeEntry(address, kind, method, index, detail));
            }

            var typePointers = Pointers(Pointer(meta + MrTypes), I32(meta + MrTypesCount));
            if (typePointers.Length != model.RuntimeTypes.Count)
                throw new InvalidDataException($"types 数量 {typePointers.Length} 与模型 {model.RuntimeTypes.Count} 不一致");
            var typeIndex = new Dictionary<ulong, int>(typePointers.Length);
            for (var i = 0; i < typePointers.Length; i++) typeIndex.TryAdd(typePointers[i], i);

            // 非泛型方法、this 调整桩、反向 P/Invoke、模块初始化、RGCTX：逐个 CodeGenModule
            var byImage = model.Assemblies.ToDictionary(a => a.Name, a => a.Types.SelectMany(t => t.Methods).ToDictionary(m => m.Token));
            var invokerOf = new Dictionary<MethodDef, int>();
            var rgctx = new Dictionary<(string, uint), RgctxEntry[]>();
            var reverseWrappers = Pointers(Pointer(code + CrReversePInvoke), U32(code + CrReversePInvokeCount));
            var modules = Pointers(Pointer(code + CrModules), U32(code + CrModuleCount));
            foreach (var module in modules)
            {
                var name = ReadCString(Pointer(module + CmName));
                if (!byImage.TryGetValue(name, out var tokens)) throw new InvalidDataException($"CodeGenModule {name} 没有对应的程序集");
                var methodCount = U32(module + CmMethodCount);
                var methods = Pointers(Pointer(module + CmMethods), methodCount);
                var invokerIndices = Pointer(module + CmInvokerIndices);
                for (var rid = 1u; rid <= methodCount; rid++)
                {
                    var token = 0x06000000u | rid;
                    if (!tokens.TryGetValue(token, out var method)) { if (methods[rid - 1] != 0) problems.Add($"{name} 方法令牌 0x{token:x8} 有代码但没有定义"); continue; }
                    Add(methods[rid - 1], EntryKind.Method, new MethodRef(method, [], []), (int)rid - 1, name);
                    if (invokerIndices != 0) invokerOf[method] = I32(invokerIndices + (rid - 1) * 4);
                    if (method.Address != methods[rid - 1]) problems.Add($"{method} 的 Address 0x{method.Address:x} 与 methodPointers 0x{methods[rid - 1]:x} 不一致");
                }
                var adjustors = Pointer(module + CmAdjustors);
                for (var i = 0u; i < U32(module + CmAdjustorCount); i++)
                {
                    var pair = adjustors + i * AdjustorPairSize;
                    var token = U32(pair);
                    if (!tokens.TryGetValue(token, out var method)) { problems.Add($"{name} adjustor 令牌 0x{token:x8} 没有定义"); continue; }
                    Add(Pointer(pair + 8), EntryKind.AdjustorThunk, new MethodRef(method, [], []), (int)i, name);
                }
                var tuples = Pointer(module + CmReversePInvokeIndices);
                for (var i = 0u; i < U32(module + CmReversePInvokeCount); i++)
                {
                    var tuple = tuples + i * TokenIndexTupleSize;
                    var token = U32(tuple);
                    var index = I32(tuple + 4);
                    var generic = I32(tuple + 16);
                    MethodRef? method = generic >= 0 && generic < model.MethodSpecs.Count ? model.MethodSpecs[generic]
                        : tokens.TryGetValue(token, out var def) ? new MethodRef(def, [], []) : null;
                    if (index < 0 || index >= reverseWrappers.Length) { problems.Add($"{name} 反向 P/Invoke 序号越界 {index}"); continue; }
                    Add(reverseWrappers[index], EntryKind.ReversePInvoke, method, index, name);
                }
                Add(Pointer(module + CmModuleInitializer), EntryKind.ModuleInitializer, null, 0, name);
                ReadRgctx(name, module, rgctx);
            }

            // 泛型方法实例与泛型 this 调整桩：genericMethodTable[i] = { methodSpec, { methodIndex, invokerIndex, adjustorThunkIndex } }
            var genericPointers = Pointers(Pointer(code + CrGenericMethods), U32(code + CrGenericMethodCount));
            var genericAdjustors = Pointer(code + CrGenericAdjustors);
            var table = Pointer(meta + MrGenericMethodTable);
            var tableCount = I32(meta + MrGenericMethodTableCount);
            for (var i = 0; i < tableCount; i++)
            {
                var row = table + (ulong)i * GenericMethodTableSize;
                var spec = I32(row);
                var methodIndex = I32(row + 4);
                var adjustorIndex = I32(row + 12);
                if (spec < 0 || spec >= model.MethodSpecs.Count || methodIndex < 0 || methodIndex >= genericPointers.Length)
                { problems.Add($"genericMethodTable[{i}] 序号越界：spec {spec}, method {methodIndex}"); continue; }
                Add(genericPointers[methodIndex], EntryKind.GenericMethod, model.MethodSpecs[spec], methodIndex, null);
                if (adjustorIndex >= 0 && genericAdjustors != 0)
                    Add(Pointer(genericAdjustors + (ulong)adjustorIndex * 8), EntryKind.GenericAdjustorThunk, model.MethodSpecs[spec], adjustorIndex, null);
            }

            var invokers = Pointers(Pointer(code + CrInvokers), U32(code + CrInvokerCount));
            for (var i = 0; i < invokers.Length; i++) Add(invokers[i], EntryKind.Invoker, null, i, null);
            var unresolved = U32(code + CrUnresolvedCount);
            foreach (var (offset, kind) in new[] { (CrUnresolvedVirtual, EntryKind.UnresolvedVirtualCall), (CrUnresolvedInstance, EntryKind.UnresolvedInstanceCall), (CrUnresolvedStatic, EntryKind.UnresolvedStaticCall) })
            {
                var array = Pointer(code + (ulong)offset);
                if (array == 0) continue;
                var pointers = Pointers(array, unresolved);
                for (var i = 0; i < pointers.Length; i++) Add(pointers[i], kind, null, i, null);
            }
            var interop = Pointer(code + CrInterop);
            for (var i = 0u; i < U32(code + CrInteropCount); i++)
            {
                var row = interop + i * InteropSize;
                var type = Pointer(row + 48);
                var detail = typeIndex.TryGetValue(type, out var t) ? model.RuntimeTypes[t].ToString() : $"type@0x{type:x}";
                Add(Pointer(row), EntryKind.DelegatePInvokeWrapper, null, (int)i, detail);
                Add(Pointer(row + 8), EntryKind.MarshalToNative, null, (int)i, detail);
                Add(Pointer(row + 16), EntryKind.MarshalFromNative, null, (int)i, detail);
                Add(Pointer(row + 24), EntryKind.MarshalCleanup, null, (int)i, detail);
                Add(Pointer(row + 32), EntryKind.CreateCcw, null, (int)i, detail);
            }

            var usageCount = image.ReadU64(meta + MrUsagesCount);
            var usages = usageCount == 0 ? Array.Empty<ulong>() : Pointers(Pointer(meta + MrUsages), (long)usageCount);

            return new Registrations
            {
                CodeRegistration = code,
                MetadataRegistration = meta,
                Entries = entries,
                ByAddress = entries.GroupBy(e => e.Address).ToDictionary(g => g.Key, g => g.ToArray()),
                Rgctx = rgctx,
                MetadataUsageSlots = usages,
                TypePointers = typeIndex,
                InvokerOf = invokerOf,
            };
        }

        /// <summary>
        /// v27.2+：Il2CppRGCTXDefinition { type; const void* data }，data 指向只读区中的定义数据：
        /// TYPE/CLASS/ARRAY 为 int32 类型表序号，METHOD 为 int32 methodSpec 序号，
        /// CONSTRAINED 为 Il2CppRGCTXConstrainedData { int32 typeIndex; uint32 encodedMethodIndex }。
        /// </summary>
        private void ReadRgctx(string name, ulong module, Dictionary<(string, uint), RgctxEntry[]> rgctx)
        {
            var rangeCount = U32(module + CmRgctxRangeCount);
            if (rangeCount == 0) return;
            var ranges = Pointer(module + CmRgctxRanges);
            var definitions = Pointer(module + CmRgctxs);
            var count = U32(module + CmRgctxCount);
            for (var r = 0u; r < rangeCount; r++)
            {
                var pair = ranges + r * TokenRangeSize;
                var token = U32(pair);
                var start = I32(pair + 4);
                var length = I32(pair + 8);
                if (start < 0 || length < 0 || (long)start + length > count) { problems.Add($"{name} RGCTX 区间越界 0x{token:x8}"); continue; }
                var list = new RgctxEntry[length];
                for (var k = 0; k < length; k++)
                {
                    var def = definitions + (ulong)(start + k) * RgctxSize;
                    var kind = (RgctxKind)U32(def);
                    var data = Pointer(def + 8);
                    object? value = null;
                    switch (kind)
                    {
                        case RgctxKind.Type or RgctxKind.Class or RgctxKind.Array:
                            var t = I32(data);
                            if (t >= 0 && t < model.RuntimeTypes.Count) value = model.RuntimeTypes[t];
                            else problems.Add($"{name} 0x{token:x8} RGCTX[{k}] {kind} 类型序号越界 {t}");
                            break;
                        case RgctxKind.Method:
                            var m = I32(data);
                            if (m >= 0 && m < model.MethodSpecs.Count) value = model.MethodSpecs[m];
                            else problems.Add($"{name} 0x{token:x8} RGCTX[{k}] methodSpec 序号越界 {m}");
                            break;
                        case RgctxKind.Constrained:
                            var constrainedType = I32(data);
                            var encoded = U32(data + 4);
                            var method = model.DecodeToken(encoded >> 29, (encoded & 0x1FFFFFFF) >> 1)?.Value as MethodRef;
                            if (constrainedType < 0 || constrainedType >= model.RuntimeTypes.Count || method is null)
                                problems.Add($"{name} 0x{token:x8} RGCTX[{k}] Constrained 无法解析 ({constrainedType}, 0x{encoded:x})");
                            else value = (model.RuntimeTypes[constrainedType], method);
                            break;
                        default:
                            problems.Add($"{name} 0x{token:x8} RGCTX[{k}] 未知种类 {(int)kind}");
                            break;
                    }
                    list[k] = new RgctxEntry(kind, value);
                }
                if (!rgctx.TryAdd((name, token), list)) problems.Add($"{name} RGCTX 令牌 0x{token:x8} 重复");
            }
        }

        private string ReadCString(ulong address)
        {
            var bytes = image.ReadUpTo(address, 512);
            var end = bytes.IndexOf((byte)0);
            if (end < 0) throw new InvalidDataException($"0x{address:x} 处字符串未终止");
            return System.Text.Encoding.UTF8.GetString(bytes[..end]);
        }
    }
}
