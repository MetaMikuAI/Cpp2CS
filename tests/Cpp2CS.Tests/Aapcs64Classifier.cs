using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

/// <summary>
/// 独立的 AAPCS64（2025Q1，小端 LP64，基本 PCS）分类器。只共享 L1 布局，不调用 ManagedAbi。
/// Shape/Allocate 可脱离 IL2CPP 模型测试；Location 保留栈偏移及“栈上传副本指针”，供后续原生对照器使用。
/// 不支持的语言映射（共享泛型、原生 SIMD 等）必须显式失败，不推测布局。
/// </summary>
internal sealed class Aapcs64Classifier(FieldLayouts layouts)
{
    internal enum Kind { Void, Integer, Pointer, Float, Aggregate }
    internal sealed record Shape(Kind Kind, int Size, int Alignment, int FloatWidth = 0, int[]? HfaOffsets = null)
    {
        public string Category => Kind != Kind.Aggregate ? Kind.ToString()
            : HfaOffsets is { Length: > 0 } h ? $"HFA{h.Length}x{FloatWidth}"
            : Size <= 16 ? "打包≤16" : "间接>16";
    }
    /// <summary>Width 截到类型的存储大小，仍可含内部/尾部填充；对照必须另按 Leaves 比较可观察的字段。</summary>
    internal sealed record Piece(Storage Register, int Width, int Offset);
    internal sealed record Location(Shape Shape, bool Indirect, Piece[] Pieces, int? StackOffset = null)
    {
        public override string ToString() => $"{Shape.Category}/{(Indirect ? "副本地址:" : "")}" +
            (StackOffset is { } s ? $"sp+{s}" : string.Join(",", Pieces.Select(p => $"{p.Register}:{p.Width}@{p.Offset}")));
    }
    /// <summary>StackBytes 是参数区长度；调用方分配帧时仍须满足 AAPCS64 §6.4.5 的 SP 16 字节对齐。</summary>
    internal sealed record Signature(Location? This, Location[] Parameters, Location MethodInfo, Location? Return, int StackBytes);
    internal sealed record Leaf(int Offset, int Size, TypeRef Type, string Path);
    internal sealed class Cursor { public int Gpr; public int Vector; public int Stack; }
    private readonly Dictionary<TypeRef, Shape> cache = new();
    private readonly Dictionary<TypeRef, Leaf[]> leafCache = new();

    public static bool IsStruct(TypeRef type) => type is DefinitionRef { Definition.IsValueType: true, Definition.IsEnum: false } d
        && Primitive(d) is null;

    private static Shape? Primitive(DefinitionRef type)
    {
        if (type.Definition is not { Assembly: "mscorlib.dll", Namespace: "System", DeclaringType: null } t) return null;
        return t.Name switch
        {
            "Void" => new(Kind.Void, 0, 1),
            "Boolean" or "Byte" or "SByte" => new(Kind.Integer, 1, 1),
            "Char" or "Int16" or "UInt16" => new(Kind.Integer, 2, 2),
            "Int32" or "UInt32" => new(Kind.Integer, 4, 4),
            "Int64" or "UInt64" => new(Kind.Integer, 8, 8),
            "IntPtr" or "UIntPtr" => Pointer,
            "Single" => new(Kind.Float, 4, 4, 32),
            "Double" => new(Kind.Float, 8, 8, 64),
            _ => null,
        };
    }

    private static readonly Shape Pointer = new(Kind.Pointer, 8, 8);
    public Shape Describe(TypeRef type)
    {
        if (cache.TryGetValue(type, out var old)) return old;
        Shape result;
        switch (type)
        {
            case PrimitiveRef { Name: "void" }: result = new(Kind.Void, 0, 1); break;
            case ByRefRef or PointerRef or ArrayRef: result = Pointer; break;
            case DefinitionRef d when FieldLayouts.IsFullyShared(d): throw new NotSupportedException($"共享占位类型 {type}");
            case DefinitionRef d when Primitive(d) is { } p: result = p; break;
            case DefinitionRef { Definition.IsValueType: false }: result = Pointer; break;
            case DefinitionRef { Definition.IsEnum: true } d:
                result = Describe(d.Definition.Fields.Single(f => !f.IsStatic).Type.Substitute(d.Arguments, [])); break;
            case DefinitionRef d:
            {
                var layout = layouts.Of(d) ?? throw new NotSupportedException($"布局未知 {type}");
                var leaves = Leaves(type);
                // §5.10.5：按完成布局后的、可独立寻址的同类浮点成员判定，包括同地址的联合成员。
                var unique = leaves.DistinctBy(l => (l.Offset, l.Size, l.Type)).OrderBy(l => l.Offset).ToArray();
                var floating = unique.Length is >= 1 and <= 4 && unique.All(l => Describe(l.Type).Kind == Kind.Float)
                    && unique.All(l => l.Type.Equals(unique[0].Type))
                    && unique.Select((l, i) => l.Offset == i * unique[0].Size).All(x => x)
                    && layout.ValueSize == unique.Length * unique[0].Size;
                result = new(Kind.Aggregate, layout.ValueSize, layout.MinimumAlignment,
                    floating ? unique[0].Size * 8 : 0, floating ? unique.Select(l => l.Offset).ToArray() : null);
                break;
            }
            default: throw new NotSupportedException($"未知语言映射 {type}");
        }
        if (result.Kind != Kind.Void && (result.Size <= 0 || result.Alignment <= 0)) throw new NotSupportedException($"无效布局 {type}");
        cache[type] = result;
        return result;
    }

    /// <summary>偏移相对未装箱数据；L1 的值类型 FieldSlot 含对象头，因此每一层均扣除 0x10。</summary>
    public Leaf[] Leaves(TypeRef type)
    {
        if (leafCache.TryGetValue(type, out var old)) return old;
        var leaves = new List<Leaf>();
        void Visit(TypeRef current, int offset, string path, HashSet<TypeRef> active)
        {
            if (!IsStruct(current))
            {
                var shape = Describe(current);
                leaves.Add(new(offset, shape.Size, current, path));
                return;
            }
            if (!active.Add(current)) throw new NotSupportedException($"递归值类型 {current}");
            var layout = layouts.Of((DefinitionRef)current) ?? throw new NotSupportedException($"布局未知 {current}");
            foreach (var slot in layout.Fields)
                Visit(slot.Type, offset + slot.Offset - RuntimeLayout.ObjectHeaderSize,
                    path.Length == 0 ? slot.Field.Name : path + "." + slot.Field.Name, active);
            active.Remove(current);
        }
        Visit(type, 0, "", []);
        return leafCache[type] = leaves.ToArray();
    }

    public Signature Classify(MethodRef method)
    {
        var state = new Cursor();
        Location? self = method.Method.IsStatic ? null : Allocate(Pointer, state);
        var args = method.Method.Parameters.Select(p => Allocate(Describe(p.Type.Substitute(method.TypeArguments, method.MethodArguments)), state)).ToArray();
        var info = Allocate(Pointer, state);
        var result = Result(Describe(method.Method.ReturnType.Substitute(method.TypeArguments, method.MethodArguments)));
        return new(self, args, info, result, state.Stack);
    }

    public static Location? Result(Shape shape)
    {
        if (shape.Kind == Kind.Void) return null;
        // §6.9：按独立第一个参数可否放在寄存器决定；间接结果一律经 x8。
        var result = Allocate(shape, new Cursor());
        return result.Indirect ? new(shape, true, [new(Storage.Gpr(8), 64, 0)]) : result;
    }

    public static Location Allocate(Shape shape, Cursor state)
    {
        if (shape.Kind == Kind.Void) throw new NotSupportedException("void 参数");
        var hfa = shape.HfaOffsets;
        if (shape.Kind == Kind.Float || hfa is { Length: > 0 })
        {
            var offsets = hfa ?? [0];
            if (state.Vector + offsets.Length <= 8)
                return new(shape, false, offsets.Select(o => new Piece(Storage.Vec(state.Vector++), shape.FloatWidth, o)).ToArray());
            // C.3–C.6：HFA 放不下时整体上栈，封闭向量寄存器池，不能改用整数寄存器。
            state.Vector = 8;
            return OnStack(shape, false, shape.Size, Math.Max(8, shape.Alignment), state);
        }
        // B.4 先把大聚合替换为指针；指针本身也可能按 C.13–C.17 上栈。
        var indirect = shape.Kind == Kind.Aggregate && shape.Size > 16;
        var size = indirect ? 8 : shape.Size;
        var alignment = indirect ? 8 : shape.Alignment;
        if (alignment == 16) state.Gpr = Round(state.Gpr, 2); // C.10
        var words = (size + 7) / 8;
        if (state.Gpr + words <= 8)
            return new(shape, indirect, Enumerable.Range(0, words)
                .Select(i => new Piece(Storage.Gpr(state.Gpr++), Math.Min(8, size - 8 * i) * 8, 8 * i)).ToArray());
        state.Gpr = 8; // C.12–C.17：不拆分到寄存器与栈。
        return OnStack(shape, indirect, size, Math.Max(8, alignment), state);
    }

    private static Location OnStack(Shape shape, bool indirect, int size, int alignment, Cursor state)
    {
        state.Stack = Round(state.Stack, alignment);
        var offset = state.Stack;
        state.Stack += Round(size, 8);
        return new(shape, indirect, [], offset);
    }

    private static int Round(int value, int alignment) => checked((value + alignment - 1) / alignment * alignment);

    [Command("struct-abi-unit", "独立 AAPCS64 规范边界检查", Gate = Gate.Unit)]
    public static int Check()
    {
        var a = new Assertions();
        var hfa = new Shape(Kind.Aggregate, 24, 8, 64, [0, 8, 16]);
        a.Equal(Storage.Vec(2), Result(hfa)!.Pieces[2].Register, "B.3 优先于 B.4：24 字节 HFA 不间接返回");
        var state = new Cursor { Vector = 7 };
        a.Equal(0, Allocate(hfa, state).StackOffset, "HFA 寄存器不足时整体上栈");
        a.Equal(24, Allocate(new(Kind.Float, 4, 4, 32), state).StackOffset, "HFA 溢出后浮点仍上栈");
        a.Equal(Storage.Gpr(0), Allocate(Pointer, state).Pieces[0].Register, "浮点溢出不消耗整数寄存器");
        state = new() { Gpr = 1 };
        a.Equal(Storage.Gpr(2), Allocate(new(Kind.Aggregate, 16, 16), state).Pieces[0].Register, "C.10 偶数寄存器对齐");
        state = new() { Gpr = 7 };
        a.Equal(0, Allocate(new(Kind.Aggregate, 16, 8), state).StackOffset, "C.12 小聚合不拆分");
        a.Equal(16, Allocate(Pointer, state).StackOffset, "C.13 后续整数上栈");
        var large = Allocate(new(Kind.Aggregate, 40, 8), state);
        a.True(large.Indirect && large.StackOffset == 24 && state.Stack == 32, "大结构的副本指针占一个栈字");
        a.Equal(Storage.Gpr(8), Result(new(Kind.Aggregate, 40, 8))!.Pieces[0].Register, "§6.9 x8 间接返回");
        a.Equal(8, Result(new(Kind.Aggregate, 9, 1))!.Pieces[1].Width, "填充高位不作为有效值比较");
        return a.Finish("独立 AAPCS64 边界检查");
    }
}
