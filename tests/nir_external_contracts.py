"""按标准声明、精确导出绑定和纯跳转字节补充外部接口。"""
from collections import Counter, defaultdict
import copy
import json
import re
import struct


SOURCE_ROOT = ("https://github.com/Unity-Technologies/SimpleUIDemo/blob/"
               "c33907f1ffa0f8a30b46f958d3cf45e5da08b01c/"
               "Tiny3D/Library/DotsRuntimeBuild/artifacts/Stevedore/il2cpp/libil2cpp/")
HEADER_SHA256 = "EB8ABC97CA0740BAB88FCD2CB5B6B51AE368937D581D83C53D0A96407823A91D"
TYPES_SHA256 = "F513F47A2D9B3BBA9269AAC30FEAAC5C133FD34541070E58C839CE84DFDE4D97"
# 只采用声明中可直接表示的固定原型；不以符号词义或活跃寄存器推断参数。
DECLARATIONS = """
DO_API(void*, il2cpp_alloc, (size_t size));
DO_API(void, il2cpp_free, (void* ptr));
DO_API(Il2CppMethodPointer, il2cpp_resolve_icall, (const char* name));
DO_API(Il2CppClass*, il2cpp_array_class_get, (Il2CppClass * element_class, uint32_t rank));
DO_API(uint32_t, il2cpp_array_length, (Il2CppArray * array));
DO_API(uint32_t, il2cpp_array_get_byte_length, (Il2CppArray * array));
DO_API(Il2CppArray*, il2cpp_array_new, (Il2CppClass * elementTypeInfo, il2cpp_array_size_t length));
DO_API(Il2CppArray*, il2cpp_array_new_specific, (Il2CppClass * arrayTypeInfo, il2cpp_array_size_t length));
DO_API(Il2CppArray*, il2cpp_array_new_full, (Il2CppClass * array_class, il2cpp_array_size_t * lengths, il2cpp_array_size_t * lower_bounds));
DO_API(Il2CppClass*, il2cpp_bounded_array_class_get, (Il2CppClass * element_class, uint32_t rank, bool bounded));
DO_API(int, il2cpp_array_element_size, (const Il2CppClass * array_class));
DO_API(const Il2CppImage*, il2cpp_assembly_get_image, (const Il2CppAssembly * assembly));
DO_API(const Il2CppType*, il2cpp_class_enum_basetype, (Il2CppClass * klass));
DO_API(bool, il2cpp_class_is_generic, (const Il2CppClass * klass));
DO_API(bool, il2cpp_class_is_inflated, (const Il2CppClass * klass));
DO_API(bool, il2cpp_class_is_assignable_from, (Il2CppClass * klass, Il2CppClass * oklass));
DO_API(bool, il2cpp_class_is_subclass_of, (Il2CppClass * klass, Il2CppClass * klassc, bool check_interfaces));
DO_API(bool, il2cpp_class_has_parent, (Il2CppClass * klass, Il2CppClass * klassc));
DO_API(Il2CppClass*, il2cpp_class_from_il2cpp_type, (const Il2CppType * type));
DO_API(Il2CppClass*, il2cpp_class_from_name, (const Il2CppImage * image, const char* namespaze, const char *name));
DO_API(Il2CppClass*, il2cpp_class_from_system_type, (Il2CppReflectionType * type));
DO_API(Il2CppClass*, il2cpp_class_get_element_class, (Il2CppClass * klass));
DO_API(const MethodInfo*, il2cpp_class_get_method_from_name, (Il2CppClass * klass, const char* name, int argsCount));
DO_API(const char*, il2cpp_class_get_name, (Il2CppClass * klass));
DO_API(const char*, il2cpp_class_get_namespace, (Il2CppClass * klass));
DO_API(Il2CppClass*, il2cpp_class_get_parent, (Il2CppClass * klass));
DO_API(Il2CppClass*, il2cpp_class_get_declaring_type, (Il2CppClass * klass));
DO_API(int32_t, il2cpp_class_instance_size, (Il2CppClass * klass));
DO_API(size_t, il2cpp_class_num_fields, (const Il2CppClass * enumKlass));
DO_API(bool, il2cpp_class_is_valuetype, (const Il2CppClass * klass));
DO_API(int32_t, il2cpp_class_value_size, (Il2CppClass * klass, uint32_t * align));
DO_API(bool, il2cpp_class_is_blittable, (const Il2CppClass * klass));
DO_API(int, il2cpp_class_get_flags, (const Il2CppClass * klass));
DO_API(Il2CppClass*, il2cpp_class_from_type, (const Il2CppType * type));
DO_API(const Il2CppType*, il2cpp_class_get_type, (Il2CppClass * klass));
DO_API(Il2CppDomain*, il2cpp_domain_get, ());
DO_API(const Il2CppAssembly*, il2cpp_domain_assembly_open, (Il2CppDomain * domain, const char* name));
DO_API(const Il2CppAssembly**, il2cpp_domain_get_assemblies, (const Il2CppDomain * domain, size_t * size));
DO_API_NO_RETURN(void, il2cpp_raise_exception, (Il2CppException*));
DO_API(Il2CppException*, il2cpp_exception_from_name_msg, (const Il2CppImage * image, const char *name_space, const char *name, const char *msg));
DO_API(Il2CppException*, il2cpp_get_exception_argument_null, (const char *arg));
DO_API(void, il2cpp_field_get_value, (Il2CppObject * obj, FieldInfo * field, void *value));
DO_API(Il2CppObject*, il2cpp_field_get_value_object, (FieldInfo * field, Il2CppObject * obj));
DO_API(void, il2cpp_field_set_value, (Il2CppObject * obj, FieldInfo * field, void *value));
DO_API(void, il2cpp_field_static_get_value, (FieldInfo * field, void *value));
DO_API(void, il2cpp_field_static_set_value, (FieldInfo * field, void *value));
DO_API(void, il2cpp_gc_wbarrier_set_field, (Il2CppObject * obj, void **targetAddress, void *object));
DO_API(const Il2CppType*, il2cpp_method_get_return_type, (const MethodInfo * method));
DO_API(const MethodInfo*, il2cpp_method_get_from_reflection, (const Il2CppReflectionMethod * method));
DO_API(Il2CppReflectionMethod*, il2cpp_method_get_object, (const MethodInfo * method, Il2CppClass * refclass));
DO_API(Il2CppClass*, il2cpp_object_get_class, (Il2CppObject * obj));
DO_API(uint32_t, il2cpp_object_get_size, (Il2CppObject * obj));
DO_API(const MethodInfo*, il2cpp_object_get_virtual_method, (Il2CppObject * obj, const MethodInfo * method));
DO_API(Il2CppObject*, il2cpp_object_new, (const Il2CppClass * klass));
DO_API(void*, il2cpp_object_unbox, (Il2CppObject * obj));
DO_API(Il2CppObject*, il2cpp_value_box, (Il2CppClass * klass, void* data));
DO_API(void, il2cpp_monitor_enter, (Il2CppObject * obj));
DO_API(void, il2cpp_monitor_exit, (Il2CppObject * obj));
DO_API(Il2CppObject*, il2cpp_runtime_invoke, (const MethodInfo * method, void *obj, void **params, Il2CppException **exc));
DO_API(void, il2cpp_runtime_class_init, (Il2CppClass * klass));
DO_API(void, il2cpp_runtime_object_init, (Il2CppObject * obj));
DO_API(void, il2cpp_runtime_object_init_exception, (Il2CppObject * obj, Il2CppException** exc));
DO_API(int32_t, il2cpp_string_length, (Il2CppString * str));
DO_API(Il2CppChar*, il2cpp_string_chars, (Il2CppString * str));
DO_API(Il2CppString*, il2cpp_string_new, (const char* str));
DO_API(Il2CppString*, il2cpp_string_new_len, (const char* str, uint32_t length));
DO_API(Il2CppString*, il2cpp_string_new_utf16, (const Il2CppChar * text, int32_t len));
DO_API(Il2CppString*, il2cpp_string_new_wrapper, (const char* str));
DO_API(Il2CppString*, il2cpp_string_intern, (Il2CppString * str));
DO_API(Il2CppString*, il2cpp_string_is_interned, (Il2CppString * str));
DO_API(Il2CppThread*, il2cpp_thread_current, ());
DO_API(Il2CppThread*, il2cpp_thread_attach, (Il2CppDomain * domain));
DO_API(void, il2cpp_thread_detach, (Il2CppThread * thread));
DO_API(Il2CppObject*, il2cpp_type_get_object, (const Il2CppType * type));
DO_API(int, il2cpp_type_get_type, (const Il2CppType * type));
DO_API(Il2CppClass*, il2cpp_type_get_class_or_element_class, (const Il2CppType * type));
DO_API(char*, il2cpp_type_get_name, (const Il2CppType * type));
DO_API(bool, il2cpp_type_is_byref, (const Il2CppType * type));
DO_API(bool, il2cpp_type_equals, (const Il2CppType * type, const Il2CppType * otherType));
DO_API(const Il2CppClass*, il2cpp_image_get_class, (const Il2CppImage * image, size_t index));
"""


def scalar(declaration):
    declaration = declaration.strip()
    if "*" in declaration or declaration.split()[0] == "Il2CppMethodPointer":
        return {"width": 64, "kind": "Address"}
    kind = declaration.split()[0]
    if kind == "void":
        return None
    width = {"bool": 8, "int": 32, "int32_t": 32, "uint32_t": 32,
             "size_t": 64, "il2cpp_array_size_t": 64}[kind]
    return {"width": width, "kind": "Integer"}


def standard_prototypes():
    prototypes = {}
    for declaration in DECLARATIONS.strip().splitlines():
        match = re.fullmatch(r"DO_API(?:_NO_RETURN)?\((.+?), (il2cpp_\w+), \((.*)\)\);", declaration)
        assert match is not None, declaration
        result, name, arguments = match.groups()
        parameters = [] if not arguments else [scalar(argument) for argument in arguments.split(",")]
        assert all(parameter is not None for parameter in parameters)
        prototypes[name] = ({"arguments": parameters, "result": scalar(result)}, declaration)
    return prototypes


def pure_jump(binary, address):
    size = 4 if binary.architecture == "Arm64" else 5
    offset = binary.offset(address, size)
    if offset is None:
        return None
    data = bytes(binary.data[offset:offset + size])
    if binary.architecture == "Arm64":
        word = int.from_bytes(data, "little")
        if address % 4 or word & 0xFC000000 != 0x14000000:
            return None
        displacement = word & 0x3FFFFFF
        if displacement & 0x2000000:
            displacement -= 0x4000000
        target = address + displacement * 4
    else:
        if data[0] != 0xE9:
            return None
        target = address + 5 + struct.unpack_from("<i", data, 1)[0]
    if not binary.executable(target):
        return None
    return target, {"kind": "machine.pure-jump-alias", "address": hex(address),
                    "target": hex(target), "recordFileOffset": hex(offset), "bytes": data.hex(),
                    "instruction": "B imm26" if binary.architecture == "Arm64" else "JMP rel32",
                    "binarySha256": binary.identity["sha256"]}


def jump_paths(binary):
    jumps = {}
    pending = list(binary.entries)
    while pending:
        address = pending.pop()
        if address in jumps:
            continue
        jump = pure_jump(binary, address)
        jumps[address] = jump
        if jump is not None and jump[0] not in jumps:
            pending.append(jump[0])
    terminals = {}
    for address in jumps:
        chain, visited = [], set()
        cursor = address
        while cursor not in terminals and cursor not in visited:
            visited.add(cursor)
            chain.append(cursor)
            jump = jumps[cursor]
            if jump is None:
                terminals[cursor] = cursor
                break
            cursor = jump[0]
        terminal = terminals.get(cursor)
        for item in chain:
            terminals[item] = terminal
    return jumps, terminals


def path_evidence(address, jumps):
    evidence = []
    while jumps[address] is not None:
        address, step = jumps[address]
        evidence.append(step)
    return evidence


def adopt(binary, address, signature, evidence, counts):
    entry = binary.entries.get(address)
    if entry is None:
        entry = binary.add(address, {"kind": "machine.export-jump-target", "exportAddress": evidence[0]["exportAddress"],
                                     "binarySha256": binary.identity["sha256"]})
    if entry["contract"] is not None:
        counts["compatibleExistingContracts"] += 1
        return
    entry["signatureEvidence"].extend(copy.deepcopy(evidence))
    entry["signatureEvidence"].append({"kind": "conservative-external-effects",
        "scope": "all effects remain possible; no absence inferred from prototype or jump"})
    entry["signatureStatus"] = "known"
    entry["gaps"] = []
    entry["contract"] = {
        "name": f"external_{address:x}", "entryAddress": address, "signature": copy.deepcopy(signature),
        "abi": "Aapcs64" if binary.architecture == "Arm64" else "WindowsX64",
        "effects": {"readsMemory": True, "writesMemory": True, "externalEffects": True, "mayThrow": True,
                    "mayReturn": True, "mayDiverge": True, "mayTerminate": True},
        "assumptions": ["The exact exported symbol adopts the cited standard native prototype.",
                        "Any alias path contains only register-and-memory-preserving direct jumps.",
                        "Effects are conservative; the prototype establishes no absence of effects.",
                        "Analysis domain is conditional; no runtime equivalence claim is made."],
        "domain": {"normalExecution": True, "validPrivateFrame": True, "stableThreadEnvironment": True,
                   "sequentialMemory": True}}
    counts["addedContracts"] += 1


def augment_external_contracts(binary):
    """在所有 managed/generic 别名归并后调用；冲突和未解别名阻止传播。"""
    prototypes = standard_prototypes()
    jumps, terminals = jump_paths(binary)
    exports = defaultdict(list)
    direct_exports = defaultdict(list)
    counts = Counter()
    for address, entry in binary.entries.items():
        for record in entry["evidence"]:
            name = record.get("name")
            if record["kind"] not in ("elf.symbol", "pe.export") or name not in prototypes:
                continue
            terminal = terminals[address]
            signature, declaration = prototypes[name]
            evidence = {"kind": "adopted-standard-export-prototype", "name": name,
                        "source": SOURCE_ROOT + "il2cpp-api-functions.h", "sourceSha256": HEADER_SHA256,
                        "declaration": declaration, "exportAddress": hex(address), "symbolBinding": record,
                        "binarySha256": binary.identity["sha256"],
                        "typedefSource": SOURCE_ROOT + "il2cpp-api-types.h", "typedefSourceSha256": TYPES_SHA256,
                        "typedefs": {"Il2CppMethodPointer": "void(*)()", "il2cpp_array_size_t": "uintptr_t"},
                        "scope": "conditional adoption of the published standard export prototype"}
            direct_exports[address].append((signature, evidence))
            if terminal is None:
                counts["cyclicExportAliases"] += 1
            else:
                exports[terminal].append((signature, evidence, path_evidence(address, jumps)))
            counts["exactExportBindings"] += 1
    for address, candidates in direct_exports.items():
        entry = binary.entries[address]
        signatures = {json.dumps(signature, sort_keys=True) for signature, _ in candidates}
        if entry["contract"] is not None:
            signatures.add(json.dumps(entry["contract"]["signature"], sort_keys=True))
        if len(signatures) != 1 or entry.get("unresolvedSignatureAliases") or entry["signatureStatus"] == "conflict":
            counts["rejectedDirectExports"] += 1
            entry["signatureEvidence"].extend(copy.deepcopy([evidence for _, evidence in candidates]))
            entry["signatureStatus"] = "conflict" if len(signatures) != 1 else "unsupported"
            entry["contract"] = None
            entry["gaps"].append("standard export prototype conflicts with or cannot discharge existing entry aliases")
            continue
        adopt(binary, address, candidates[0][0], [evidence for _, evidence in candidates], counts)
    groups = defaultdict(list)
    for address, terminal in terminals.items():
        if terminal in exports:
            groups[terminal].append(address)
    for terminal, addresses in groups.items():
        candidates = exports[terminal]
        signatures = {json.dumps(signature, sort_keys=True) for signature, _, _ in candidates}
        unresolved = False
        for address in addresses:
            entry = binary.entries.get(address)
            if entry is None:
                continue
            unresolved |= bool(entry.get("unresolvedSignatureAliases")) or entry["signatureStatus"] == "conflict"
            if entry["contract"] is not None:
                signatures.add(json.dumps(entry["contract"]["signature"], sort_keys=True))
        if unresolved or len(signatures) != 1:
            counts["rejectedAliasGroups"] += 1
            continue
        signature, _, source_path = candidates[0]
        for address in addresses:
            evidence = [item for _, item, _ in candidates]
            evidence.extend(source_path)
            evidence.extend(path_evidence(address, jumps))
            adopt(binary, address, signature, evidence, counts)
    return dict(counts)
