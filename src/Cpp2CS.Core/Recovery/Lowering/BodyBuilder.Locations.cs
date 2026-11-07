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

    private int Width(TypeRef type) => types.ValueWidth(type);

    private ManagedValue? Read(ReadSym read, ulong address)
    {
        if (oracle.Decompose(read.Address) is (ResultSym { Site: { Op.Kind: OpKind.BeginCatch } begin }, 0, null, _) && exceptions.TryGetValue(begin, out var exception))
            return exception;
        if (oracle.Locate(read.Address, read.Width) is not { } location)
        {
            if (oracle.NarrowRead(read) is not { } part) return Hole(address, $"内存 读取位置 {read.Address}", null);
            var value = LocationValue(part.Leaf, address);
            if (part.FieldBit != 0)
                value = new BinaryValue(BinOp.LShr, value, new ConstantValue((ulong)part.FieldBit, types.Int32, 32), value.Type, Width(value.Type));
            return new ConversionValue(ConvKind.Truncate, value, types.Integer(read.Width, true), read.Width);
        }
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
            case LocationKind.Argument:
                return View(location.Base!, location.Type, address);
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
                    if (location.ByteOffset is { } offset)
                        pointer = new PointerOffsetValue(pointer, View(offset, types.Int64, address));
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
            case LocationKind.StringLength:
                return new StringLengthValue(View(location.Base!, types.String, address), types.Int32);
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
        index = TypeOracle.ArrayIndex(index);
        return index.Width == 32 ? View(index, types.Int32, address) : View(index, types.Int64, address);
    }

    private TypeRef FieldType(FieldRef field, TypeRef? leaf) => leaf ?? field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);

    /// <summary>
    /// 字段链：写入目标中值类型的中间字段以地址给出；每一级按可访问性取字段或被内联的访问器。
    /// 写入经过的不可访问中间字段没有访问器可以代替（取不到它的地址）；和调用方同一程序集时按原生代码直接取址，见 <see cref="FieldValue.Unfolded"/>。
    /// </summary>
    private ManagedValue Nest(ManagedValue receiver, IReadOnlyList<FieldRef> path, TypeRef leaf, bool store, ulong address)
    {
        var value = receiver;
        for (var i = 0; i < path.Count; i++)
        {
            var last = i == path.Count - 1;
            var type = FieldType(path[i], last ? leaf : null);
            if (store && !last && !fields.Accessible(path[i], value.Type))
            {
                var reason = $"内存 写入经过不可访问的值类型字段 {path[i].Field.Name}";
                if (path[i].Field.Owner.Assembly != analysis.Method.Method.Owner.Assembly
                    || Inlining.TemplateRecovery.SharedArgument(analysis.Method, path[i].DeclaringType)) return Hole(address, reason, leaf);
                unfolded.Add(new Cpp2CS.Diagnostics.RuleTrace(Inlining.TemplateRecovery.UnfoldedRule, address, Cpp2CS.Diagnostics.RewriteStatus.Applied, "same-assembly-path", reason, null));
                value = new FieldValue(value, path[i], type, Width(type)) { Unfolded = true };
                if (types.Kind(type) == TypeKind.Struct) value = new AddressValue(value);
                continue;
            }
            value = (store ? null : OverlappingPieces(value, path[i], type, address)) ?? FieldAccess(value, path[i], type, store && last, address);
            if (store && !last && types.Kind(type) == TypeKind.Struct) value = new AddressValue(value);
        }
        return value;
    }

    /// <summary>
    /// 显式布局中不可访问的整数字段，其位同时由可访问的整数字段连续覆盖（联合体式的结构）时，读取它等于按小端把这些字段拼起来。
    /// </summary>
    private ManagedValue? OverlappingPieces(ManagedValue receiver, FieldRef field, TypeRef type, ulong address)
    {
        if (fields.Accessible(field, receiver.Type) || types.Kind(type) != TypeKind.Int || !ExplicitLayout(field, out var owner)) return null;
        var slots = types.Fields(owner).ToArray();
        if (slots.FirstOrDefault(f => f.Path[0].Equals(field)) is not { } self) return null;
        var bit = self.Bit;
        ManagedValue? packed = null;
        foreach (var piece in slots.Where(f => !f.Path[0].Equals(field) && self.Contains(f.Bit, f.Width) && fields.Accessible(f.Path[0], receiver.Type)
            && types.Kind(f.Type) is TypeKind.Int or TypeKind.Bool).OrderBy(f => f.Bit))
        {
            if (piece.Bit != bit) return null;
            var part = Resize(FieldAccess(receiver, piece.Path[0], piece.Type, false, address), type);
            if (bit > self.Bit) part = new BinaryValue(BinOp.Shl, part, new ConstantValue((ulong)(bit - self.Bit), types.Int32, 32), type, Width(type));
            packed = packed is null ? part : new BinaryValue(BinOp.Or, packed, part, type, Width(type));
            bit += piece.Width;
        }
        return bit == self.Bit + self.Width ? packed : null;
    }

    private static bool ExplicitLayout(FieldRef field, out DefinitionRef owner)
    {
        owner = (DefinitionRef)field.DeclaringType;
        return (owner.Definition.Attributes & System.Reflection.TypeAttributes.LayoutMask) == System.Reflection.TypeAttributes.ExplicitLayout;
    }
}
