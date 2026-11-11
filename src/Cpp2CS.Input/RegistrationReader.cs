#nullable enable
using System;
using System.Collections.Frozen;
using System.Collections.Immutable;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Cpp2CS.Runtime;
using Cpp2CS.Native.Images;
using Cpp2CS.Model;

namespace Cpp2CS.Input
{
    /// <summary>按 RuntimeSpec 的布局，经 IImage 读取注册代码入口与实体关系。</summary>
    public sealed class RegistrationReader
    {
        private readonly RuntimeData data;
        private ulong CrReversePInvokeCount => data.Offset("Il2CppCodeRegistration", "reversePInvokeWrapperCount");
        private ulong CrReversePInvoke => data.Offset("Il2CppCodeRegistration", "reversePInvokeWrappers");
        private ulong CrGenericMethodCount => data.Offset("Il2CppCodeRegistration", "genericMethodPointersCount");
        private ulong CrGenericMethods => data.Offset("Il2CppCodeRegistration", "genericMethodPointers");
        private ulong CrGenericAdjustors => data.Offset("Il2CppCodeRegistration", "genericAdjustorThunks");
        private ulong CrInvokerCount => data.Offset("Il2CppCodeRegistration", "invokerPointersCount");
        private ulong CrInvokers => data.Offset("Il2CppCodeRegistration", "invokerPointers");
        private ulong CrUnresolvedCount => data.Offset("Il2CppCodeRegistration", "unresolvedIndirectCallCount");
        private ulong CrUnresolvedVirtual => data.Offset("Il2CppCodeRegistration", "unresolvedVirtualCallPointers");
        private ulong CrUnresolvedInstance => data.Offset("Il2CppCodeRegistration", "unresolvedInstanceCallPointers");
        private ulong CrUnresolvedStatic => data.Offset("Il2CppCodeRegistration", "unresolvedStaticCallPointers");
        private ulong CrInteropCount => data.Offset("Il2CppCodeRegistration", "interopDataCount");
        private ulong CrInterop => data.Offset("Il2CppCodeRegistration", "interopData");
        private ulong CrModuleCount => data.Offset("Il2CppCodeRegistration", "codeGenModulesCount");
        private ulong CrModules => data.Offset("Il2CppCodeRegistration", "codeGenModules");
        private ulong CmName => data.Offset("Il2CppCodeGenModule", "moduleName");
        private ulong CmMethodCount => data.Offset("Il2CppCodeGenModule", "methodPointerCount");
        private ulong CmMethods => data.Offset("Il2CppCodeGenModule", "methodPointers");
        private ulong CmAdjustorCount => data.Offset("Il2CppCodeGenModule", "adjustorThunkCount");
        private ulong CmAdjustors => data.Offset("Il2CppCodeGenModule", "adjustorThunks");
        private ulong CmInvokerIndices => data.Offset("Il2CppCodeGenModule", "invokerIndices");
        private ulong CmReversePInvokeCount => data.Offset("Il2CppCodeGenModule", "reversePInvokeWrapperCount");
        private ulong CmReversePInvokeIndices => data.Offset("Il2CppCodeGenModule", "reversePInvokeWrapperIndices");
        private ulong CmRgctxRangeCount => data.Offset("Il2CppCodeGenModule", "rgctxRangesCount");
        private ulong CmRgctxRanges => data.Offset("Il2CppCodeGenModule", "rgctxRanges");
        private ulong CmRgctxCount => data.Offset("Il2CppCodeGenModule", "rgctxsCount");
        private ulong CmRgctxs => data.Offset("Il2CppCodeGenModule", "rgctxs");
        private ulong CmModuleInitializer => data.Offset("Il2CppCodeGenModule", "moduleInitializer");
        private ulong MrGenericMethodTableCount => data.Offset("Il2CppMetadataRegistration", "genericMethodTableCount");
        private ulong MrGenericMethodTable => data.Offset("Il2CppMetadataRegistration", "genericMethodTable");
        private ulong MrTypesCount => data.Offset("Il2CppMetadataRegistration", "typesCount");
        private ulong MrTypes => data.Offset("Il2CppMetadataRegistration", "types");
        private ulong MrUsagesCount => data.Offset("Il2CppMetadataRegistration", "metadataUsagesCount");
        private ulong MrUsages => data.Offset("Il2CppMetadataRegistration", "metadataUsages");
        private ulong InteropSize => data.Size("Il2CppInteropData");
        private ulong AdjustorPairSize => data.Size("Il2CppTokenAdjustorThunkPair");
        private ulong TokenIndexTupleSize => data.Size("Il2CppTokenIndexMethodTuple");
        private ulong RgctxSize => data.Size("Il2CppRGCTXDefinition");
        private ulong TokenRangeSize => data.Size("Il2CppTokenRangePair");
        private ulong GenericMethodTableSize => data.Size("Il2CppGenericMethodFunctionsDefinitions");

        private readonly IImage image;
        private readonly ProgramModel model;
        private readonly List<string> problems = new();

        private RegistrationReader(IImage image, ProgramModel model, RuntimeSpec spec)
        {
            this.image = image;
            data = new RuntimeData(image, spec);
            this.model = model;
        }

        public IReadOnlyList<string> Problems => problems;

        public static (Registrations Registrations, IReadOnlyList<string> Problems) Read(IImage image, ProgramModel model, RuntimeSpec spec, ulong codeRegistration, ulong metadataRegistration)
        {
            var reader = new RegistrationReader(image, model, spec);
            return (reader.Build(codeRegistration, metadataRegistration), reader.problems);
        }

        private ulong Pointer(ulong address) => data.Pointer(address);
        private uint U32(ulong address) => (uint)image.ReadUnsigned(address, sizeof(uint));
        private int I32(ulong address) => unchecked((int)U32(address));
        private ulong[] Pointers(ulong array, long count) => data.Pointers(array, count);
        private ulong F(string record, string field) => data.Offset(record, field);

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
            var genericInvokers = new List<(MethodRef Method, int Index)>();
            var invokerOf = new Dictionary<MethodDef, int>();
            var rgctx = new Dictionary<(string, uint), RgctxEntry[]>();
            var reverseWrappers = Pointers(Pointer(code + CrReversePInvoke), U32(code + CrReversePInvokeCount));
            for (var i = 0; i < reverseWrappers.Length; i++) Add(reverseWrappers[i], EntryKind.ReversePInvoke, null, i, null);
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
                    if (invokerIndices != 0) invokerOf[method] = I32(invokerIndices + (rid - 1) * sizeof(int));
                }
                var adjustors = Pointer(module + CmAdjustors);
                for (var i = 0u; i < U32(module + CmAdjustorCount); i++)
                {
                    var pair = adjustors + i * AdjustorPairSize;
                    var token = U32(pair + F("Il2CppTokenAdjustorThunkPair", "token"));
                    if (!tokens.TryGetValue(token, out var method)) { problems.Add($"{name} adjustor 令牌 0x{token:x8} 没有定义"); continue; }
                    Add(Pointer(pair + F("Il2CppTokenAdjustorThunkPair", "adjustorThunk")), EntryKind.AdjustorThunk, new MethodRef(method, [], []), (int)i, name);
                }
                var tuples = Pointer(module + CmReversePInvokeIndices);
                for (var i = 0u; i < U32(module + CmReversePInvokeCount); i++)
                {
                    var tuple = tuples + i * TokenIndexTupleSize;
                    var token = U32(tuple + F("Il2CppTokenIndexMethodTuple", "token"));
                    var index = I32(tuple + F("Il2CppTokenIndexMethodTuple", "index"));
                    var generic = I32(tuple + F("Il2CppTokenIndexMethodTuple", "__genericMethodIndex"));
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
                var spec = I32(row + F("Il2CppGenericMethodFunctionsDefinitions", "genericMethodIndex"));
                var methodIndex = I32(row + F("Il2CppGenericMethodFunctionsDefinitions", "indices") + F("Il2CppGenericMethodIndices", "methodIndex"));
                var adjustorIndex = I32(row + F("Il2CppGenericMethodFunctionsDefinitions", "indices") + F("Il2CppGenericMethodIndices", "adjustorThunkIndex"));
                if (spec < 0 || spec >= model.MethodSpecs.Count || methodIndex < 0 || methodIndex >= genericPointers.Length)
                { problems.Add($"genericMethodTable[{i}] 序号越界：spec {spec}, method {methodIndex}"); continue; }
                genericInvokers.Add((model.MethodSpecs[spec], I32(row + F("Il2CppGenericMethodFunctionsDefinitions", "indices") + F("Il2CppGenericMethodIndices", "invokerIndex"))));
                Add(genericPointers[methodIndex], EntryKind.GenericMethod, model.MethodSpecs[spec], methodIndex, null);
                if (adjustorIndex >= 0 && genericAdjustors != 0)
                    Add(Pointer(genericAdjustors + (ulong)adjustorIndex * (ulong)image.PointerWidth), EntryKind.GenericAdjustorThunk, model.MethodSpecs[spec], adjustorIndex, null);
            }

            var invokers = Pointers(Pointer(code + CrInvokers), U32(code + CrInvokerCount));
            for (var i = 0; i < invokers.Length; i++) Add(invokers[i], EntryKind.Invoker, null, i, null);
            foreach (var (method, index) in invokerOf.Select(p => (new MethodRef(p.Key, [], []), p.Value)).Concat(genericInvokers))
            {
                if (index == -1) continue;
                if (index < 0 || index >= invokers.Length) throw new InvalidDataException($"调用器索引越界：{index}");
                Add(invokers[index], EntryKind.Invoker, method, index, null);
            }
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
                var type = Pointer(row + F("Il2CppInteropData", "type"));
                var detail = typeIndex.TryGetValue(type, out var t) ? model.RuntimeTypes[t].ToString() : $"type@0x{type:x}";
                Add(Pointer(row + F("Il2CppInteropData", "delegatePInvokeWrapperFunction")), EntryKind.DelegatePInvokeWrapper, null, (int)i, detail);
                Add(Pointer(row + F("Il2CppInteropData", "pinvokeMarshalToNativeFunction")), EntryKind.MarshalToNative, null, (int)i, detail);
                Add(Pointer(row + F("Il2CppInteropData", "pinvokeMarshalFromNativeFunction")), EntryKind.MarshalFromNative, null, (int)i, detail);
                Add(Pointer(row + F("Il2CppInteropData", "pinvokeMarshalCleanupFunction")), EntryKind.MarshalCleanup, null, (int)i, detail);
                Add(Pointer(row + F("Il2CppInteropData", "createCCWFunction")), EntryKind.CreateCcw, null, (int)i, detail);
            }

            var usageCount = image.ReadUnsigned(meta + MrUsagesCount, image.PointerWidth);
            var usages = usageCount == 0 ? Array.Empty<ulong>() : Pointers(Pointer(meta + MrUsages), (long)usageCount);

            if (problems.Count > 0) throw new InvalidDataException(string.Join("\n", problems));
            return new Registrations
            {
                CodeRegistration = code,
                MetadataRegistration = meta,
                Entries = entries.ToImmutableArray(),
                ByAddress = entries.GroupBy(e => e.Address).ToFrozenDictionary(g => g.Key, g => g.ToImmutableArray()),
                Rgctx = rgctx.ToFrozenDictionary(p => p.Key, p => p.Value.ToImmutableArray()),
                MetadataUsageSlots = usages.ToImmutableArray(),
                UsageEntities = usages.ToFrozenDictionary(slot => slot, slot => MetadataTokens.ReadSlot(image, model, slot) ?? throw new InvalidDataException($"注册元数据槽 0x{slot:x} 无法解码。")),
                TypePointers = typeIndex.ToFrozenDictionary(),
                InvokerOf = invokerOf.ToFrozenDictionary(),
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
                var token = U32(pair + F("Il2CppTokenRangePair", "token"));
                var start = I32(pair + F("Il2CppTokenRangePair", "range") + F("Il2CppRange", "start"));
                var length = I32(pair + F("Il2CppTokenRangePair", "range") + F("Il2CppRange", "length"));
                if (start < 0 || length < 0 || (long)start + length > count) { problems.Add($"{name} RGCTX 区间越界 0x{token:x8}"); continue; }
                var list = new RgctxEntry[length];
                for (var k = 0; k < length; k++)
                {
                    var def = definitions + (ulong)(start + k) * RgctxSize;
                    var kind = (RgctxKind)U32(def + F("Il2CppRGCTXDefinition", "type"));
                    var data = Pointer(def + F("Il2CppRGCTXDefinition", "data"));
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
                            var constrainedType = I32(data + F("Il2CppRGCTXConstrainedData", "__typeIndex"));
                            var encoded = U32(data + F("Il2CppRGCTXConstrainedData", "__encodedMethodIndex"));
                            var method = MetadataTokens.Decode(model, encoded >> 29, (encoded & 0x1FFFFFFF) >> 1)?.Value as MethodRef;
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

        private string ReadCString(ulong address) => data.CString(address);
    }
}
