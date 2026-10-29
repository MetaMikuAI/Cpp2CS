using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceBooleanValuesCheck
{
    [Command("source-boolean-values", "布尔分支事实的合流、覆盖、取址和异常边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var owner = new TypeDef { Index = -1, Assembly = "Tests.dll", Namespace = "Tests", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodRef(new MethodDef { Index = -1, Owner = owner, Name = "Read", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = types.Boolean }, [], []);
        var flag = new ArgumentValue(0, types.Boolean, 1);
        var local = new LocalValue(new(Storage.Temp(0), 1), types.Boolean, 1);
        var a = new Assertions();
        foreach (var mode in new[] { "branch", "comparison", "negated", "copy", "reset", "addressed", "merge", "handler" })
        {
            ManagedValue condition = mode switch
            {
                "comparison" => new ComparisonValue(Cond.Ne, flag, new ConstantValue(0, flag.Type, 1), flag.Type),
                "negated" => new NegatedValue(flag, flag.Type),
                _ => flag,
            };
            var prefix = new List<ManagedStatement>();
            if (mode == "addressed") prefix.Add(new ManagedCall(0, new(method, null, [new AddressValue(flag)], false), null, false));
            prefix.Add(new ManagedBranch(1, condition, new(2, []), new(mode == "merge" ? 2UL : 3UL, [])));
            var yes = new List<ManagedStatement>();
            if (mode == "reset") yes.Add(new ManagedStore(2, flag, new ArgumentValue(1, flag.Type, 1)));
            if (mode == "copy") yes.Add(new ManagedAssignment(2, local, flag));
            yes.Add(new ManagedReturn(2, mode == "copy" ? local : flag));
            var body = new ManagedBody(method, [new(0, prefix), new(2, yes), new(3, [new ManagedReturn(3, flag)])]);
            if (mode == "handler") body = body with { Regions = [new([0], 2, [2], null, ManagedRegionKind.Catch)] };
            var result = SourceNonNullReceivers.FoldBooleans(body, types);
            var value = ((ManagedReturn)result.Blocks[1].Statements[^1]).Value;
            if (mode is "branch" or "comparison" or "negated" or "copy")
                a.True(value is ConstantValue constant && constant.Bits == (mode == "negated" ? 0UL : 1UL), mode + " 使用已证实布尔值");
            else a.True(value is ArgumentValue, mode + " 不沿用未知或失效事实");
        }
        return a.Finish("source-boolean-values");
    }
}
