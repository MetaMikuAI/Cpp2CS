using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

internal sealed partial class StructAbi
{
    /// <summary>
    /// ECMA-335 I.12.4.1.5.2：通过托管指针传递存储位置，调用可以写回。
    /// 将显式 Out 与值类型构造器 this 的后值作为独立的桩输出，和返回值一样按签名/调用序号合成；
    /// 不读取被测方法或被调方法的指令，不猜普通 ref 是否修改，也不把填充当字段。
    /// </summary>
    public void WriteBack(Side side, MethodRef method, int ordinal, IReadOnlyList<byte[]> arguments)
    {
        if (side.ResizeArray(method, arguments)) return;
        var parameters = ArgumentTypes(method);
        for (var i = 0; i < parameters.Length; i++)
        {
            var parameter = i - (method.Method.IsStatic ? 0 : 1);
            var writes = parameter < 0 ? method.Method.Name == ".ctor" && method.Method.Owner.IsValueType
                : (method.Method.Parameters[parameter].Attributes & System.Reflection.ParameterAttributes.Out) != 0;
            if (!writes || parameters[i] is not ByRefRef byref || !Aapcs64Classifier.IsStruct(byref.Element)) continue;
            var address = Bits(arguments[i]);
            var value = side.World.CallWriteBytes(ordinal, i, byref.Element);
            foreach (var leaf in Classifier.Leaves(byref.Element))
                side.Write(address + (ulong)leaf.Offset, value.AsSpan(leaf.Offset, leaf.Size));
        }
    }

    /// <summary>
    /// ECMA-335 I.12.1.6.1 / I.12.4.1.5.2：局部变量的地址由实现选择，ref 传递的是存储位置。
    /// 方法级桩不保留 ref；在每次调用中比较全部输入叶子与别名关系，不能比较两台执行器的物理栈地址。
    /// 参数副本沿用既有逻辑身份；堆/静态地址保持精确比较。规则只依赖签名、实际地址和独立布局。
    /// </summary>
    public ulong[] ObservableArguments(Side side, IReadOnlyList<TypeRef> types, IReadOnlyList<byte[]> bytes)
    {
        var ranges = types.Select((t, i) => (Type: t, Index: i)).Where(v => v.Type is ByRefRef)
            .Select(v => (v.Type, v.Index, Address: Bits(bytes[v.Index])))
            .Where(v => v.Address - World.StackBase < World.StackSize
                && side.ArgumentPointer(v.Address) == v.Address)
            .Select(v => (v.Index, v.Address, Size: side.World.StorageSize(((ByRefRef)v.Type).Element))).ToArray();
        var groups = ranges.Select((_, i) => i).ToArray();
        int Root(int i) => groups[i] == i ? i : groups[i] = Root(groups[i]);
        for (var i = 0; i < ranges.Length; i++)
        for (var j = 0; j < i; j++)
            if (ranges[i].Address < ranges[j].Address + (ulong)ranges[j].Size && ranges[j].Address < ranges[i].Address + (ulong)ranges[i].Size)
                groups[Root(i)] = Root(j);
        var result = new List<ulong>();
        for (var i = 0; i < types.Count; i++)
        {
            var slot = Array.FindIndex(ranges, r => r.Index == i);
            if (slot < 0) { result.AddRange(ObservableArgument(side, types[i], bytes[i])); continue; }
            var root = Root(slot);
            var members = Enumerable.Range(0, ranges.Length).Where(j => Root(j) == root).ToArray();
            var first = members.Min(j => ranges[j].Index);
            var start = members.Min(j => ranges[j].Address);
            result.Add(0xf330000000000000UL | (ulong)first << 32 | (ranges[slot].Address - start));
            var type = ((ByRefRef)types[i]).Element;
            var content = new byte[side.World.StorageSize(type)];
            side.Read(ranges[slot].Address, content);
            result.AddRange(Observable(type, content));
        }
        return result.ToArray();
    }
}
