using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>位置与局部：读取、字段链、可寻址局部与局部的分配。</summary>
internal sealed partial class BodyBuilder
{
    /// <summary>类指针所属的对象：引用类型对象偏移 0 处的 64 位读取。</summary>
    private Sym? ClassOwner(Sym klass) => SymTable.Resolve(klass) is ReadSym { Width: 64 } read
        && oracle.Decompose(read.Address) is (var root, 0, null, _) && oracle.TypeOf(root) is { } type && ManagedTypes.IsReferenceType(type) ? root : null;

    /// <summary>地址逃逸的单元对应的可寻址局部。</summary>
    private LocalValue CellLocal(LocalSym root)
    {
        if (!locals.TryGetValue(root, out var local))
        {
            var cell = analysis.Memory.Find(root.Space, root.Offset, 1)!;
            locals[root] = local = NewLocal(oracle.CellType(cell)!);
        }
        return local;
    }

    private LocalValue NewLocal(TypeRef type) => new(new Variable(Storage.Temp(1000 + nextLocal++), 1), type, Width(type));

    private LocalValue Local(Sym sym, TypeRef type)
    {
        sym = SymTable.Resolve(sym);
        if (!locals.TryGetValue(sym, out var local)) locals[sym] = local = NewLocal(type);
        return local;
    }

    private int Width(TypeRef type) => ManagedTypes.IsReferenceType(type) || type is ByRefRef or PointerRef ? 64
        : types.Kind(type) == TypeKind.Struct ? 0 : Math.Max(1, types.Bits(type));

    private ManagedValue? Read(ReadSym read, ulong address)
    {
        if (oracle.Decompose(read.Address) is (ResultSym { Site: { Op.Kind: OpKind.BeginCatch } begin }, 0, null, _) && exceptions.TryGetValue(begin, out var exception))
            return exception;
        if (oracle.Locate(read.Address, read.Width) is not { } location) return Hole(address, $"内存 读取位置 {read.Address}", null);
        return LocationValue(location, address);
    }

    /// <summary>
    /// 位置的托管值。写入目标（store）中值类型的根与中间字段以地址给出：stfld 需要对象引用或托管地址。
    /// </summary>
    private ManagedValue LocationValue(Location location, ulong address, bool store = false)
    {
        var path = location.Path;
        switch (location.Kind)
        {
            case LocationKind.Static or LocationKind.ThreadStatic:
                {
                    var type = FieldType(path[0], path.Count == 1 ? location.Type : null);
                    var root = StaticFieldAccess(path[0], type, store && path.Count == 1, address);
                    return path.Count == 1 ? root : Nest(store ? new AddressValue(root) : root, path.Skip(1).ToArray(), location.Type, store, address);
                }
            case LocationKind.Instance:
                return Nest(View(location.Base!, oracle.TypeOf(location.Base!), address), path, location.Type, store, address);
            case LocationKind.Reference:
                {
                    var pointer = View(location.Base!, oracle.TypeOf(location.Base!), address);
                    return path.Count == 0 ? new IndirectValue(pointer, location.Type, Width(location.Type)) : Nest(pointer, path, location.Type, store, address);
                }
            case LocationKind.Element:
                {
                    var array = View(location.Base!, oracle.TypeOf(location.Base!), address);
                    var index = location.Index is { } i ? ElementIndex(i, address) : new ConstantValue((ulong)location.ConstantIndex, types.Int32, 32);
                    var element = array.Type is ArrayRef a ? a.Element : location.Type;
                    ManagedValue value = new ArrayElementValue(array, index, element, Width(element));
                    return path.Count == 0 ? value : Nest(store ? new AddressValue(value) : value, path, location.Type, store, address);
                }
            case LocationKind.Length:
                return new ArrayLengthValue(View(location.Base!, oracle.TypeOf(location.Base!), address), types.Int32, 32);
            case LocationKind.Local:
                {
                    var local = CellLocal((LocalSym)location.Base!);
                    return path.Count == 0 ? local : Nest(store ? new AddressValue(local) : local, path, location.Type, store, address);
                }
        }
        return Hole(address, $"内存 位置 {location.Kind} 尚未接入", location.Type);
    }

    /// <summary>
    /// 元素下标（ECMA-335 III.4.7）：下标是 int32 或 native int，int32 按符号扩展参与寻址，界外访问抛出 IndexOutOfRangeException。
    /// 按比例寻址时丢弃的高位、32 位下标的符号或零扩展都只影响界外访问，下标取其来源；仍为 64 位时按 int64 写出，由写出转为 native int。
    /// </summary>
    private ManagedValue ElementIndex(Sym index, ulong address)
    {
        while (true)
        {
            index = SymTable.Resolve(index);
            if (index is SliceSym { Low: 0, Width: >= 32 } slice && slice.Base.Width > slice.Width) index = slice.Base;
            else if (index is OpSym { Op: { Kind: OperatorKind.Convert } op, Args: [{ Width: 32 } narrow] } && op.Conversion == ConvKind.SignExtend) index = narrow;
            else if (index is ConcatSym { Parts: [{ Width: 32 } low, ConstSym { Value: 0 }] }) index = low;
            else break;
        }
        return index.Width == 32 ? View(index, types.Int32, address) : View(index, types.Int64, address);
    }

    private TypeRef FieldType(FieldRef field, TypeRef? leaf) => leaf ?? field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);

    /// <summary>字段链：写入目标中值类型的中间字段以地址给出；每一级按可访问性取字段或被内联的访问器。</summary>
    private ManagedValue Nest(ManagedValue receiver, IReadOnlyList<FieldRef> path, TypeRef leaf, bool store, ulong address)
    {
        var value = receiver;
        for (var i = 0; i < path.Count; i++)
        {
            var last = i == path.Count - 1;
            var type = FieldType(path[i], last ? leaf : null);
            if (store && !last && !Accessible(path[i].Field))
                return Hole(address, $"内存 写入经过不可访问的值类型字段 {path[i].Field.Name}", leaf);
            value = FieldAccess(value, path[i], type, store && last, address);
            if (store && !last && types.Kind(type) == TypeKind.Struct) value = new AddressValue(value);
        }
        return value;
    }
}
