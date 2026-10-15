using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

/// <summary>真实元数据的值类型字段边界检查，以及可计算自然布局的覆盖统计。</summary>
internal static class LayoutModelCheck
{
    public static int Run(string binary, string metadata)
    {
        var model = ModelCheck.Load(binary, metadata);
        var types = new ManagedTypes(model, 16);
        int fields = 0, unknown = 0, errors = 0, checkedLayouts = 0;
        foreach (var type in model.Types.Where(t => t.IsValueType && t.GenericParameters.Count == 0 && t.Size > 0))
        {
            if (types.Layouts.Get(new DefinitionRef(type, [])) is not null) checkedLayouts++;
            foreach (var field in type.Fields.Where(f => !f.IsStatic))
            {
                var size = types.Size(field.Type);
                if (field.Offset < 0 || size <= 0) { unknown++; continue; }
                fields++;
                if ((long)field.Offset + size <= type.Size) continue;
                errors++;
                Console.WriteLine($"越界 {field}: +{field.Offset} 宽 {size}，所属类型大小 {type.Size}");
            }
        }
        var instances = model.RuntimeTypes.OfType<DefinitionRef>().Where(d => d.Definition.IsValueType && d.Arguments.Count > 0).Distinct().ToArray();
        Console.WriteLine($"字段边界 {fields}  未知 {unknown}  越界 {errors}  可核对布局 {checkedLayouts}");
        Console.WriteLine($"泛型值实例 {instances.Length}  可计算 {instances.Count(t => types.Layouts.Get(t) is not null)}");
        foreach (var type in model.Types.Where(t => t.FullName is "UnityEngine.Vector3" or "UnityEngine.Quaternion"))
        {
            Console.WriteLine($"{type}: 大小 {type.Size} packing {type.PackingSize} 默认大小 {type.ClassSizeIsDefault}");
            foreach (var field in type.Fields.Where(f => !f.IsStatic)) Console.WriteLine($"  +{field.Offset} {field.Name}: {field.Type}");
        }
        return errors == 0 ? 0 : 1;
    }
}
