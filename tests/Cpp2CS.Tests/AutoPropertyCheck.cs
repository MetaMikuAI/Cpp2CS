using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class AutoPropertyCheck
{
    [Command("autoprop-rules", "F9b 语言证据与合成边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var a = new Assertions();
        var generated = facts.Model.Fields.First(f => AutoPropertyAccessor.Generated(f.CustomAttributes)).CustomAttributes
            .Where(x => x.Constructor.Owner.FullName == AutoPropertyAccessor.CompilerGenerated).ToArray();
        (FieldDef Field, MethodDef Get, MethodDef Set) Fixture(bool isStatic = false)
        {
            var owner = new TypeDef { Index = -1, Assembly = "F9b.Tests.dll", Namespace = "Tests", Name = "Value", Token = 0,
                Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
            MethodDef Method(bool write) => new() { Index = write ? -2 : -1, Owner = owner, Name = write ? "set_Value" : "get_Value", Token = 0,
                Attributes = MethodAttributes.Public | MethodAttributes.SpecialName | (isStatic ? MethodAttributes.Static : 0), ImplAttributes = 0, Slot = -1,
                ReturnType = write ? types.Corlib("System.Void") : types.Int32, Parameters = write ? [new("value", types.Int32, 0, null, false)] : [],
                CustomAttributes = generated };
            var get = Method(false);
            var set = Method(true);
            var field = new FieldDef { Index = -1, Owner = owner, Name = "<Value>k__BackingField", Token = 0, Type = types.Int32,
                Offset = isStatic ? 0 : 16, Attributes = FieldAttributes.Private | (isStatic ? FieldAttributes.Static : 0), CustomAttributes = generated };
            owner.Fields = [field];
            owner.Methods = [get, set];
            owner.Properties = [new() { Name = "Value", Token = 0, Attributes = 0, Getter = get, Setter = set }];
            return (field, get, set);
        }
        foreach (var isStatic in new[] { false, true })
        {
            var (field, get, set) = Fixture(isStatic);
            a.True(AutoPropertyAccessor.Problem(field, types) is null, "实例/静态的字段、属性、特性、签名全部匹配");
            foreach (var (method, write) in new[] { (get, false), (set, true) })
            {
                var accessor = new FieldAccessor(new(method, [], []), new(field, new DefinitionRef(field.Owner, [])), field.Type, 32, write) { LanguageDefined = true };
                a.True(FieldAccessor.Recognize(AutoPropertyAccessor.Synthesize(accessor), write, types) is not null, "无原生地址也只合成严格单字段读写体");
            }
            var wrongStatic = new FieldDef { Index = field.Index, Owner = field.Owner, Name = field.Name, Token = 0, Type = field.Type,
                Offset = field.Offset, Attributes = field.Attributes ^ FieldAttributes.Static, CustomAttributes = generated };
            field.Owner.Fields = [wrongStatic];
            a.Equal("签名或静态性不符", AutoPropertyAccessor.Problem(wrongStatic, types), "拒绝字段与访问器的静态性不符");
            field.Owner.Fields = [field];
            get.Parameters = [new("index", types.Int32, 0, null, false)];
            a.Equal("签名或静态性不符", AutoPropertyAccessor.Problem(field, types), "拒绝索引器签名");
            get.Parameters = [];
            field.CustomAttributes = [];
            a.Equal("字段缺少CompilerGenerated", AutoPropertyAccessor.Problem(field, types), "只有后备字段名称不足以证明");
            field.CustomAttributes = generated;
            get.CustomAttributes = [];
            a.Equal("访问器缺少CompilerGenerated", AutoPropertyAccessor.Problem(field, types), "所有现存访问器都必须有编译器特性");
            get.CustomAttributes = generated;
            get.ReturnType = types.Int64;
            a.Equal("签名或静态性不符", AutoPropertyAccessor.Problem(field, types), "拒绝 getter 类型不符");
            get.ReturnType = types.Int32;
            set.Parameters = [new("value", types.Int64, 0, null, false)];
            a.Equal("签名或静态性不符", AutoPropertyAccessor.Problem(field, types), "拒绝 setter 类型不符");
            set.Parameters = [new("value", types.Int32, 0, null, false)];
            field.Owner.Properties = [];
            a.Equal("属性关联不唯一或缺失", AutoPropertyAccessor.Problem(field, types), "裁掉属性定义时不猜访问器");
        }
        var candidates = AutoPropertyAccessor.Candidates(types);
        a.True(candidates.Count > 10000, "全程序自动属性证据覆盖不得退步");
        foreach (var c in candidates.Values)
        {
            a.True(c.LanguageDefined && AutoPropertyAccessor.Problem(c.Field.Field, types) is null, "语言候选保留全部元数据证据");
            a.True(FieldAccessor.Recognize(AutoPropertyAccessor.Synthesize(c), c.Write, types) is not null, "每个合成体符合 F9 单字段限制");
        }
        return a.Finish("F9b 自动属性证据与合成边界");
    }
}
