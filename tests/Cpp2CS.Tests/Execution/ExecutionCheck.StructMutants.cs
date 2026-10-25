using Cpp2CS.Facts;
using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

internal static partial class ExecutionCheck
{
    /// <summary>按独立布局挑选叶子变异；不改输入、不放宽比较，合法但未检出的变异仍留在分母。</summary>
    [MutationFamily("结构体", 30)]
    private static IEnumerable<(string, Action, Action)> StructFamily(MutationSite site) => StructMutations(site.Method, site.Cecil, site.Index, site.Initializations);

    private static IEnumerable<(string, Action, Action)> StructMutations(MethodDefinition method, CecilModel cecil, WorldIndex index, IReadOnlySet<Instruction> initializations)
    {
        TypeRef FieldType(FieldReference reference)
        {
            var field = cecil.Field(reference);
            return field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
        }
        var il = method.Body.GetILProcessor();
        var instructions = method.Body.Instructions.ToArray();
        var fields = instructions.Where(i => i.OpCode.Code is Code.Ldfld or Code.Stfld or Code.Ldflda)
            .Where(i => ((FieldReference)i.Operand).Resolve()?.DeclaringType.IsValueType == true).ToArray();
        foreach (var instruction in fields)
        {
            var original = (FieldReference)instruction.Operand;
            var field = original.Resolve();
            var at = Array.IndexOf(instructions, instruction);
            foreach (var other in field.DeclaringType.Fields.Where(f => f != field && !f.IsStatic
                && FieldType(new FieldReference(f.Name, f.FieldType, original.DeclaringType)).Equals(FieldType(original))))
            {
                var replacement = new FieldReference(other.Name, other.FieldType, original.DeclaringType);
                yield return ($"#{at} 结构体：换叶子 {field.Name} → {other.Name}",
                    () => instruction.Operand = replacement, () => instruction.Operand = original);
            }
            var type = index.Types.Kind(FieldType(original));
            if (instruction.OpCode.Code is Code.Ldfld or Code.Stfld && type is TypeKind.Int or TypeKind.Bool)
            for (var bitIndex = 0; bitIndex < (type == TypeKind.Bool ? 1 : index.Types.Bits(FieldType(original))); bitIndex++)
            {
                // 所有有效位都检查，不能只验证低位正确；bool 仅取规范的 0/1 位。
                var wide = index.Types.Bits(FieldType(original)) == 64;
                var bit = wide ? il.Create(OpCodes.Ldc_I8, unchecked((long)(1UL << bitIndex))) : il.Create(OpCodes.Ldc_I4, 1 << bitIndex);
                var flip = il.Create(OpCodes.Xor);
                var normalize = index.Types.Bits(FieldType(original)) switch
                {
                    8 => il.Create(ManagedTypes.IsSigned(FieldType(original)) ? OpCodes.Conv_I1 : OpCodes.Conv_U1),
                    16 => il.Create(ManagedTypes.IsSigned(FieldType(original)) ? OpCodes.Conv_I2 : OpCodes.Conv_U2),
                    _ => null,
                };
                yield return ($"#{at} 结构体：改{(instruction.OpCode.Code == Code.Stfld ? "写入" : "读取")}位段 {field.Name} bit{bitIndex}",
                    () =>
                    {
                        if (instruction.OpCode.Code == Code.Stfld)
                        { il.InsertBefore(instruction, bit); il.InsertBefore(instruction, flip); if (normalize is not null) il.InsertBefore(instruction, normalize); }
                        else
                        { il.InsertAfter(instruction, bit); il.InsertAfter(bit, flip); if (normalize is not null) il.InsertAfter(flip, normalize); }
                    },
                    () => { if (normalize is not null) il.Remove(normalize); il.Remove(flip); il.Remove(bit); });
            }
        }
        var stores = fields.Where(i => i.OpCode.Code == Code.Stfld).ToArray();
        for (var i = 0; i < stores.Length; i++)
        for (var j = i + 1; j < stores.Length; j++)
        {
            var first = stores[i]; var second = stores[j];
            var a = (FieldReference)first.Operand; var b = (FieldReference)second.Operand;
            if (a.DeclaringType.FullName != b.DeclaringType.FullName || !FieldType(a).Equals(FieldType(b))) continue;
            var af = cecil.Field(a); var bf = cecil.Field(b);
            if (af.DeclaringType is not DefinitionRef owner || index.Facts.Layouts.Of(owner) is not { } layout) continue;
            var ao = layout.Field(af.Field)!.Offset - RuntimeLayout.ObjectHeaderSize;
            var bo = layout.Field(bf.Field)!.Offset - RuntimeLayout.ObjectHeaderSize;
            if (ao == bo) continue;
            yield return ($"#{Array.IndexOf(instructions, first)}/#{Array.IndexOf(instructions, second)} 结构体：交换叶子写入 {a.Name}/{b.Name}",
                () => { first.Operand = b; second.Operand = a; }, () => { first.Operand = a; second.Operand = b; });
        }
        foreach (var instruction in instructions.Where(initializations.Contains))
        {
            var type = instruction.Operand;
            // 消耗原地址，保持 IL 栈平衡。首次清零可能与 initlocals 等价，未检出仍计入分母。
            yield return ($"#{Array.IndexOf(instructions, instruction)} 结构体：漏掉 initobj {type}",
                () => { instruction.OpCode = OpCodes.Pop; instruction.Operand = null; },
                () => { instruction.OpCode = OpCodes.Initobj; instruction.Operand = type; });
        }
    }
}
