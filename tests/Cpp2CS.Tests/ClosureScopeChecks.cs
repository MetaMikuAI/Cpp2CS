using System.Text.Json;
using Cpp2CS.Native;

public static class ClosureScopeChecks
{
    public static void Native(Action<bool, string> check, string config)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!;
        using var session = new RecoverySession(inputs);
        Directory.CreateDirectory("artifacts/closure-scopes");
        foreach (var address in new ulong[] { 0x5b2c96c, 0x50fbef8, 0x5ca5a0c, 0x5ca5cb4 })
        {
            var result = session.Recover(address); session.Save(result, "artifacts/recovered");
            var projection = session.SourceView(session.View(result));
            check(result.Problems.Count == 0, $"0x{address:x}: 原始指令全部接通");
            check(projection.Diagnostics.Length == 0 && projection.Closures.Length == (address is 0x5ca5a0c or 0x5ca5cb4 ? 2 : 1), $"0x{address:x}: 环境身份完整");
            var output = new SemanticWriter(session.Symbols).Structured(projection.View);
            check(!output.Contains("Runtime.") && !output.Contains("DisplayClass") && !output.Contains("static_fields"), $"0x{address:x}: 编译器环境已投影");
            var owner = result.Method.Name.Split("$$")[0]; var split = owner.LastIndexOf('.');
            File.WriteAllText($"artifacts/closure-scopes/Method_{address:x}.cs", "using Sekai;\nusing Sekai.Mysekai;\nnamespace " + owner[..split] + ";\npublic partial class " + owner[(split + 1)..] + " {\npublic\n" + output + "\n}");
            if (address == 0x50fbef8) check(output.IndexOf("while (true)") < output.IndexOf("var capturedIndex"), "每轮捕获索引在循环内声明");
            if (address == 0x5b2c96c) check(output.IndexOf("var capturedI") < output.IndexOf("while (true)") && output.Contains("loopIndex"), "共享捕获在循环外，机器索引有回边值");
            if (address == 0x5ca5a0c)
            {
                var lambdas = projection.Closures.SelectMany(c => c.Lambdas).ToArray();
                check(lambdas.Length == 2 && lambdas.All(l => SemanticWriter.Expression(l.Lambda).Contains("capturedCell")), "父环境字段由两个回调共享");
                var lowered = session.View(result);
                var link = lowered.Blocks.Values.SelectMany(b => b.Statements).OfType<StoreStatement>().Single(s => s.Target is MemberExpression { Field.Name: "CS___8__locals1" });
                var reassigned = SourceTree.Map(lowered, e => e);
                var ownerBlock = reassigned.Blocks.Values.Single(b => b.Statements.Contains(link));
                ownerBlock.Statements.Insert(ownerBlock.Statements.IndexOf(link) + 1, link with { Pc = link.Address + 1 });
                check(session.SourceView(reassigned).Closures.Length == 0, "父环境链接重赋值时拒绝消除身份");
                File.WriteAllText("artifacts/closure-scopes/Shared.cs", $$"""
                    using Sekai;
                    using Sekai.Mysekai.ContentList;
                    public static class SharedCaptures
                    {
                        public static (Action<UserResource>, Action<UserResource>, Action<UIPartsItemThumbnailListViewItem, UserResource>) Create(UserResourceContentList owner, UIPartsItemThumbnailListViewItem cell, UserResource initial)
                        {
                            var capturedThis = owner;
                            var capturedCell = cell;
                            var capturedUserResource = initial;
                            var capturedPlaceableUserResource = initial;
                            Action<UserResource> outer = {{SemanticWriter.Expression(lambdas[0].Lambda)}};
                            Action<UserResource> inner = {{SemanticWriter.Expression(lambdas[1].Lambda)}};
                            return (outer, inner, (nextCell, nextResource) => { capturedCell = nextCell; capturedPlaceableUserResource = nextResource; });
                        }
                    }
                    """);
            }
        }
        using var decoder = new Arm64Decoder(inputs.Capstone);
        var cmp = decoder.Decode(Convert.FromHexString("3F010A6B"), 0).Single();
        check(cmp.Reads.Contains("w9") && cmp.Reads.Contains("w10") && !cmp.Writes.Contains("w9"), "CMP 两个操作数均为读取");
    }
}
