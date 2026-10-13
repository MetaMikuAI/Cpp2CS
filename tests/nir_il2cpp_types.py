"""解析注册泛型实参和有字段证据的 IL2CPP 值类型布局。"""
from collections import Counter
import struct


SCALAR_WIDTHS = {2: 8, 3: 16, 4: 8, 5: 8, 6: 16, 7: 16, 8: 32, 9: 32,
                 10: 64, 11: 64, 24: 64, 25: 64}
POINTER_TYPES = {14, 15, 16, 18, 20, 27, 28, 29}


class Types:
    def __init__(self, binary, metadata, registration):
        self.binary, self.metadata = binary, metadata
        self.registration_address, self.registration, self.pointers = registration
        self.indices = {pointer: index for index, pointer in enumerate(self.pointers)}
        assert len(self.indices) == len(self.pointers)
        assert self.registration[10] == self.registration[12] == len(metadata.types)
        self.field_offsets = binary.words(self.registration[11], self.registration[10])
        self.type_sizes = binary.words(self.registration[13], self.registration[12])
        assert self.field_offsets is not None and self.type_sizes is not None
        self.cache = {}
        self.shared_markers = {}
        self.marker_cache = {}
        for index, definition in enumerate(metadata.types):
            name = metadata.string(definition[0])
            namespace = metadata.string(definition[1])
            if namespace != "Unity.IL2CPP.Metadata" or name not in ("__Il2CppFullySharedGenericType", "__Il2CppFullySharedGenericStructType"):
                continue
            _, bits, raw_type = self.read(definition[2])
            assert (bits >> 16) & 255 == 17 and definition[18] == 0 and definition[6] < 0
            size_pointer = self.type_sizes[index]
            size_offset = binary.offset(size_pointer, 16)
            assert size_offset is not None
            instance_size, native_size, _, _ = struct.unpack_from("<IiII", binary.data, size_offset)
            assert native_size == -1
            self.shared_markers[index] = {
                "kind": "il2cpp.fully-shared-type-marker", "typeDefinition": index,
                "metadataRecordFileOffset": hex(metadata.type_offset + index * 88),
                "name": namespace + "." + name, "bitfield": definition[24], "fieldCount": definition[18],
                "sizeRecordFileOffset": hex(size_offset), "instanceSize": instance_size,
                "nativeSize": native_size, "runtimeType": raw_type}

    def markers(self, pointer, active=()):
        if pointer in self.marker_cache:
            return self.marker_cache[pointer]
        assert pointer not in active, "cyclic generic type descriptor"
        data, bits, _ = self.read_pointer(pointer)
        kind = (bits >> 16) & 255
        result = set()
        if kind in (17, 18) and data in self.shared_markers:
            result.add(data)
        elif kind == 21:
            generic = self.binary.words(data, 3)
            assert generic is not None
            for inst_pointer in generic[1:]:
                if not inst_pointer:
                    continue
                count, argv = self.binary.words(inst_pointer, 2)
                arguments = self.binary.words(argv, count)
                assert arguments is not None
                for argument in arguments:
                    result.update(self.markers(argument, active + (pointer,)))
        elif kind in (15, 16, 29):
            result.update(self.markers(data, active + (pointer,)))
        elif kind == 20:
            array = self.binary.words(data, 1)
            assert array is not None
            result.update(self.markers(array[0], active + (pointer,)))
        self.marker_cache[pointer] = tuple(sorted(result))
        return self.marker_cache[pointer]

    def read_pointer(self, pointer):
        offset = self.binary.offset(pointer, 12)
        assert offset is not None
        data, bits = struct.unpack_from("<QI", self.binary.data, offset)
        return data, bits, {"typeIndex": self.indices.get(pointer), "typeAddress": hex(pointer),
                            "typeFileOffset": hex(offset), "typeCode": (bits >> 16) & 255,
                            "byref": bool(bits & (1 << 29)), "data": hex(data)}

    def read(self, index):
        assert 0 <= index < len(self.pointers)
        return self.read_pointer(self.pointers[index])

    def scalar(self, index, context=((), ())):
        assert 0 <= index < len(self.pointers)
        return self.resolve(self.pointers[index], context)

    def resolve(self, pointer, context=((), ()), active=()):
        data, bits, evidence = self.read_pointer(pointer)
        kind = (bits >> 16) & 255
        key = pointer, context if kind in (19, 30) else ((), ())
        if key in self.cache:
            return self.cache[key]
        if key in active:
            return None, [evidence], "recursive by-value type layout is unresolved"
        scalar, nested, gap = self.resolve_kind(data, bits, kind, context, active + (key,))
        result = scalar, [evidence] + nested, gap
        self.cache[key] = result
        return result

    def resolve_kind(self, data, bits, kind, context, active):
        if bits & (1 << 29) or kind in POINTER_TYPES:
            return {"width": 64, "kind": "Address"}, [], None
        if kind == 1:
            return None, [], None
        if kind in SCALAR_WIDTHS:
            return {"width": SCALAR_WIDTHS[kind], "kind": "Integer"}, [], None
        if kind in (12, 13):
            return {"width": 32 if kind == 12 else 64, "kind": "Float"}, [], None
        if kind in (19, 30):
            assert data < len(self.metadata.generic_parameters)
            parameter = self.metadata.generic_parameters[data]
            container_index, ordinal = parameter[0], parameter[4]
            assert 0 <= container_index < len(self.metadata.generic_containers)
            container = self.metadata.generic_containers[container_index]
            method_context = int(kind == 30)
            assert bool(container[2]) == bool(method_context)
            assert container[3] + ordinal == data and ordinal < container[1]
            evidence = [{"kind": "metadata.generic-parameter", "genericParameter": data,
                         "recordFileOffset": hex(self.metadata.generic_parameter_offset + data * 16),
                         "container": container_index, "ordinal": ordinal, "methodContext": bool(method_context)}]
            arguments = context[method_context]
            if ordinal >= len(arguments):
                return None, evidence, "generic parameter has no concrete registered instantiation"
            value, nested, gap = self.resolve(arguments[ordinal], context, active)
            return value, evidence + nested, gap
        if kind == 17:
            assert data < len(self.metadata.types)
            definition = self.metadata.types[data]
            if definition[24] & 2:
                field_index = definition[8]
                assert 0 <= field_index < len(self.metadata.fields)
                assert self.metadata.string(self.metadata.fields[field_index][0]) == "value__"
                value, nested, gap = self.resolve(self.pointers[self.metadata.fields[field_index][1]], context, active)
                evidence = {"kind": "metadata.enum-underlying", "typeDefinition": data, "fieldDefinition": field_index,
                            "recordFileOffset": hex(self.metadata.field_offset + field_index * 12)}
                assert gap or value is not None and value["kind"] == "Integer"
                return value, [evidence] + nested, gap
            return self.aggregate(data, context, active)
        if kind == 21:
            generic = self.binary.words(data, 4)
            assert generic is not None
            definition, definition_bits, type_evidence = self.read_pointer(generic[0])
            evidence = [{"kind": "il2cpp.generic-class", "recordAddress": hex(data),
                         "recordFileOffset": self.binary.file_location(data), "definitionType": hex(generic[0]),
                         "classInst": hex(generic[1]), "methodInst": hex(generic[2])}, type_evidence]
            definition_kind = (definition_bits >> 16) & 255
            if definition_kind == 18:
                return {"width": 64, "kind": "Address"}, evidence, None
            assert definition_kind == 17
            return None, evidence, "generic value-type instance has no registered concrete field layout"
        return None, [], f"unsupported IL2CPP type 0x{kind:02x}"

    def aggregate(self, definition_index, context, active):
        definition = self.metadata.types[definition_index]
        evidence = [{"kind": "metadata.value-type", "typeDefinition": definition_index,
                     "recordFileOffset": hex(self.metadata.type_offset + definition_index * 88),
                     "flags": definition[7], "bitfield": definition[24]}]
        if not definition[24] & 1:
            return None, evidence, "runtime value-type descriptor has no metadata value-type layout (shared generic representation)"
        if definition[6] >= 0:
            return None, evidence, "generic value-type definition has no concrete registered layout"
        size_pointer = self.type_sizes[definition_index]
        size_offset = self.binary.offset(size_pointer, 16)
        assert size_offset is not None
        instance_size, native_size, static_size, thread_size = struct.unpack_from("<IiII", self.binary.data, size_offset)
        evidence.append({"kind": "il2cpp.type-definition-size", "typeDefinition": definition_index,
                         "recordAddress": hex(size_pointer), "recordFileOffset": hex(size_offset),
                         "pointerRecordFileOffset": self.binary.file_location(self.registration[13] + definition_index * 8),
                         "instanceSize": instance_size, "nativeSize": native_size,
                         "staticFieldsSize": static_size, "threadStaticFieldsSize": thread_size, "objectHeaderSize": 16})
        if instance_size <= 16 or instance_size == 0xFFFFFFFF:
            return None, evidence, "value-type registered instance size is unavailable or empty"
        size = instance_size - 16
        fields, field_alignments, covered = [], [], 0
        offsets_pointer = self.field_offsets[definition_index]
        field_count = definition[18]
        offsets_offset = self.binary.offset(offsets_pointer, field_count * 4)
        if field_count and offsets_offset is None:
            return None, evidence, "value-type registered field offsets are unavailable"
        pack_code = (definition[24] >> 6) & 15
        assert pack_code <= 8
        packing = 0 if pack_code == 0 else 1 << (pack_code - 1)
        for local_index in range(field_count):
            field_index = definition[8] + local_index
            field = self.metadata.fields[field_index]
            _, field_bits, _ = self.read(field[1])
            if field_bits & 0x10:
                continue
            offset = struct.unpack_from("<i", self.binary.data, offsets_offset + local_index * 4)[0] - 16
            evidence.append({"kind": "il2cpp.value-field", "fieldDefinition": field_index,
                             "metadataRecordFileOffset": hex(self.metadata.field_offset + field_index * 12),
                             "offsetRecordFileOffset": hex(offsets_offset + local_index * 4), "byteOffset": offset,
                             "pointerRecordFileOffset": self.binary.file_location(self.registration[11] + definition_index * 8)})
            value, nested, gap = self.resolve(self.pointers[field[1]], context, active)
            evidence.extend(nested)
            if gap or value is None:
                return None, evidence, gap or "void value-type field is invalid"
            field_size = value["width"] // 8
            alignment = value.get("aggregate", {}).get("alignmentBytes", field_size)
            effective_alignment = min(alignment, packing) if packing else alignment
            if effective_alignment != alignment:
                return None, evidence, "aggregate packing reduces a field's natural alignment"
            if offset != covered or offset % alignment or offset + field_size > size:
                return None, evidence, "aggregate layout has padding, overlap, or inconsistent registered offsets"
            fields.append({"byteOffset": offset, "type": value})
            field_alignments.append(alignment)
            covered += field_size
        if covered != size or not fields:
            return None, evidence, "aggregate layout has trailing padding or no supported fields"
        alignment = max(field_alignments)
        if size % alignment:
            return None, evidence, "aggregate size is inconsistent with field alignment"
        return {"width": size * 8, "kind": "Aggregate", "aggregate": {"alignmentBytes": alignment, "fields": fields}}, evidence, None


class GenericMethods:
    def __init__(self, binary, metadata, registration, code_registration, types):
        self.binary, self.metadata = binary, metadata
        self.types = types
        self.registration, self.code_registration = registration[1], code_registration[1]
        inst_count, inst_table = self.registration[2:4]
        self.inst_pointers = binary.words(inst_table, inst_count)
        assert self.inst_pointers is not None
        self.instances = []
        self.inst_evidence = []
        self.inst_markers = []
        for index, pointer in enumerate(self.inst_pointers):
            count, argv = binary.words(pointer, 2)
            assert 0 < count < 1024
            arguments = binary.words(argv, count)
            assert arguments is not None and all(binary.offset(item, 12) is not None for item in arguments)
            self.instances.append(arguments)
            self.inst_markers.append(tuple(sorted({marker for argument in arguments for marker in types.markers(argument)})))
            self.inst_evidence.append({"kind": "il2cpp.generic-inst", "instantiationIndex": index,
                                       "recordAddress": hex(pointer), "recordFileOffset": binary.file_location(pointer),
                                       "pointerRecordFileOffset": binary.file_location(inst_table + index * 8),
                                       "argumentCount": count, "argumentTypes": [hex(item) for item in arguments],
                                       "argvRecordFileOffset": binary.file_location(argv)})
        spec_count, spec_table = self.registration[8:10]
        offset = binary.offset(spec_table, spec_count * 12)
        assert offset is not None
        self.specs = list(struct.iter_unpack("<iii", binary.data[offset:offset + spec_count * 12]))
        for method, class_index, method_index in self.specs:
            assert 0 <= method < len(metadata.methods)
            assert -1 <= class_index < inst_count and -1 <= method_index < inst_count
        table_count, table = self.registration[4:6]
        offset = binary.offset(table, table_count * 16)
        assert offset is not None
        self.rows = list(struct.iter_unpack("<iiii", binary.data[offset:offset + table_count * 16]))
        self.pointers = code_registration[2]
        assert all(0 <= spec < spec_count and 0 <= pointer < len(self.pointers) for spec, pointer, _, _ in self.rows)
        self.counts = Counter(instantiations=inst_count, methodSpecs=spec_count, methodTableRecords=table_count,
                              referencedMethodSpecs=len({row[0] for row in self.rows}))

    def records(self):
        for table_index, (spec_index, pointer_index, invoker_index, adjustor_index) in enumerate(self.rows):
            method, class_index, method_index = self.specs[spec_index]
            definition = self.metadata.methods[method]
            class_container = self.metadata.types[definition[1]][6]
            method_container = self.metadata.method_parts(definition)[1]
            context, evidence = [], []
            markers = set()
            for inst_index, container_index, is_method in ((class_index, class_container, False), (method_index, method_container, True)):
                if inst_index < 0:
                    assert container_index < 0
                    context.append(())
                    continue
                assert container_index >= 0
                container = self.metadata.generic_containers[container_index]
                assert bool(container[2]) == is_method and container[1] == len(self.instances[inst_index])
                assert container[0] == (method if is_method else definition[1])
                context.append(self.instances[inst_index])
                markers.update(self.inst_markers[inst_index])
                evidence.append(self.inst_evidence[inst_index])
            evidence.extend(self.types.shared_markers[marker] for marker in sorted(markers))
            evidence[:0] = [
                {"kind": "il2cpp.generic-method-table", "recordIndex": table_index,
                 "recordFileOffset": self.binary.file_location(self.registration[5] + table_index * 16),
                 "methodSpec": spec_index, "pointerIndex": pointer_index, "invokerIndex": invoker_index, "adjustorIndex": adjustor_index},
                {"kind": "il2cpp.method-spec", "methodSpec": spec_index,
                 "recordFileOffset": self.binary.file_location(self.registration[9] + spec_index * 12),
                 "methodDefinition": method, "classInstantiation": class_index, "methodInstantiation": method_index},
                {"kind": "il2cpp.generic-method-pointer", "pointerIndex": pointer_index,
                 "recordFileOffset": self.binary.file_location(self.code_registration[3] + pointer_index * 8)}]
            yield {"methodDefinition": method, "methodSpec": spec_index, "tableIndex": table_index,
                   "pointerIndex": pointer_index, "classInstantiation": class_index, "methodInstantiation": method_index,
                   "fullySharedMarkers": sorted(markers),
                   "address": self.pointers[pointer_index], "context": tuple(context), "evidence": evidence}
