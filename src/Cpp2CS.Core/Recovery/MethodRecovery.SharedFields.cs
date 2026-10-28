using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    // IL2CPP 的共享字段写入模板：固定宽度存储或按运行时大小复制，随后通知 GC。
    private int SharedFieldSetter(ulong address)
    {
        uint W(int offset) => facts.Code.Word(address + (uint)offset) ?? 0;
        ulong Target(int offset) => A64.Imm26Target(W(offset), address + (uint)offset);
        bool Barrier(ulong target)
        {
            if (facts.Code.Word(target) == 0xaa0103e0 && facts.Code.Word(target + 4) is { } jump && A64.IsB(jump))
                target = A64.Imm26Target(jump, target + 4);
            return facts.Helpers.InternalCall(target).Kind == HelperKind.WriteBarrier;
        }
        if (W(0) != 0xa9be57fe || W(4) != 0xa9014ff4) return 0;
        if (W(8) == 0xaa0103f4 && W(12) == 0xaa0003f5 && W(20) == 0xaa1403e0
            && A64.IsBl(W(28)) && facts.Code.Word(Target(28)) == 0xd65f03c0
            && W(32) == 0xaa1503e0 && W(36) == 0xaa1403e1 && A64.IsBl(W(40))
            && facts.Helpers.InternalCall(Target(40)).Kind == HelperKind.FieldAddress
            && W(48) == 0xaa0003e1 && W(52) == 0xf9400680 && W(56) == 0xa9414ff4
            && W(60) == 0xaa1f03e2 && W(64) == 0xa8c257fe && A64.IsB(W(68)) && Barrier(Target(68)))
        {
            if (W(16) == 0x52800101 && W(24) == 0xaa0203f3 && W(44) == 0xf9000013) return 64;
            if (W(16) == 0x52800081 && W(24) == 0x2a0203f3 && W(44) == 0xb9000013) return 32;
        }
        if (W(8) == 0xaa0203f3 && W(12) == 0x2a0303f4 && A64.IsBl(W(16))
            && facts.Helpers.InternalCall(Target(16)).Kind == HelperKind.FieldAddress
            && W(20) == 0xaa1303e1 && W(24) == 0xaa1403e2 && W(28) == 0xaa0003f5
            && A64.IsBl(W(32)) && facts.Code.At(Target(32))?.Import == "memcpy"
            && W(36) == 0xa9414ff4 && W(40) == 0xaa1503e0 && W(44) == 0xa8c257fe
            && A64.IsB(W(48)) && Barrier(Target(48))) return -1;
        return 0;
    }

    private sealed partial class Context
    {
        private readonly HashSet<ulong> sharedSites = [];

        private static Intrinsic FieldAddress(Expr receiver, Symbol field) => new("managed_field_address", [receiver, field], 64);
        private static TypeRef FieldType(FieldRef field) => field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);

        private void NormalizeSharedFields()
        {
            foreach (var block in function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Call call) continue;
                    if (call.Op is { Kind: OpKind.CallMethodPointer, Operand: MethodRef })
                    {
                        block.Statements[i] = call with { Target = Expr.C(0, 64) };
                        continue;
                    }
                    if (call is { Op.Kind: OpKind.FieldAddress, Arguments: [var receiver, Symbol { Kind: SymbolKind.Field } field] }
                        && call.Defines.FirstOrDefault() is { } result)
                    {
                        block.Statements[i] = new Define(call.Address, result, FieldAddress(receiver, field));
                        sharedSites.Add(call.Address);
                    }
                    else if (call is { Op: null, Target: Const target, Arguments: [var obj, Symbol { Kind: SymbolKind.Field, Value: FieldRef info } symbol, var value, ..] }
                        && owner.SharedFieldSetter(target.Value) is > 0 and var width && types.Bits(FieldType(info)) == width)
                    {
                        block.Statements[i] = new Store(call.Address, FieldAddress(obj, symbol),
                            value.Width == width ? value : new Ir.Convert(ConvKind.Truncate, value, width));
                        if (call.Kind == CallKind.Tail) block.Statements.Insert(++i, new Return(call.Address));
                        sharedSites.Add(call.Address);
                    }
                }
        }

        private RecoveryResult<ManagedValue> SharedAddress(Intrinsic address) => address switch
        {
            { Name: "managed_generic_buffer", Arguments: [_, Const id] } => new AddressValue(sharedBuffers[id.Value]),
            { Name: "managed_generic_argument", Arguments: [_, Const register] } => new AddressValue(sharedIncoming[Storage.Gpr((int)register.Value)]),
            { Name: "managed_field_address", Arguments: [var receiver, Symbol { Value: FieldRef field }] }
                => RecoverAs(receiver, field.DeclaringType, 0).Map<ManagedValue>(value => new AddressValue(new FieldValue(value, field, FieldType(field), Math.Max(0, types.Bits(FieldType(field)))))),
            _ => Fail(0, $"共享地址 {address.Name} 尚未支持"),
        };
    }
}
