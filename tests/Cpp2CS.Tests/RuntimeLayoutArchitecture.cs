using System.Text.Json;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests;

// 语法检查补足程序集扫描：const 被内联后，仅扫描使用方 IL 会失去布局名称。
internal sealed class RuntimeLayoutArchitecture
{
    private readonly HashSet<string> names = new(StringComparer.OrdinalIgnoreCase);
    private readonly HashSet<string> records = new(StringComparer.OrdinalIgnoreCase);
    private static string Normalize(string name) => new string(name.Where(char.IsLetterOrDigit).ToArray()).ToLowerInvariant();

    public RuntimeLayoutArchitecture(string root)
    {
        foreach (var path in Directory.EnumerateFiles(Path.Combine(root, "spec"), "unity-*.json"))
        {
            using var doc = JsonDocument.Parse(File.ReadAllText(path));
            foreach (var record in doc.RootElement.GetProperty("records").EnumerateObject())
            {
                records.Add(Normalize(record.Name));
                foreach (var suffix in new[] { "size", "alignment" }) names.Add(Normalize(record.Name + suffix));
                foreach (var field in record.Value.GetProperty("fields").EnumerateArray())
                    names.Add(Normalize(record.Name + field.GetProperty("name").GetString()));
            }
        }
        using var legacy = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "spec", "gen", "legacy-map.json")));
        foreach (var item in legacy.RootElement.EnumerateObject())
            if (item.Name != "UnityVersion") names.Add(Normalize(item.Name));
    }

    private bool LayoutName(string name) => names.Any(n => Normalize(name) == n || Normalize(name) == n + "offset");
    private bool LayoutContainer(string name) => records.Contains(Normalize(name)) ||
        Normalize(name).Equals("runtimelayout", StringComparison.OrdinalIgnoreCase) ||
        records.Any(r => Normalize(name) == r + "layout" || Normalize(name) == r + "offsets");

    public IEnumerable<string> Inspect(string text, string path)
    {
        var tree = CSharpSyntaxTree.ParseText(text, path: path);
        foreach (var literal in tree.GetRoot().DescendantNodes().OfType<LiteralExpressionSyntax>()
                     .Where(n => n.IsKind(SyntaxKind.NumericLiteralExpression)))
        {
            var member = literal.Ancestors().OfType<MemberDeclarationSyntax>().FirstOrDefault();
            var identifiers = member switch
            {
                FieldDeclarationSyntax f => f.Declaration.Variables.Select(v => v.Identifier.ValueText),
                PropertyDeclarationSyntax p => [p.Identifier.ValueText],
                MethodDeclarationSyntax m => [m.Identifier.ValueText],
                EnumMemberDeclarationSyntax e => [e.Identifier.ValueText],
                _ => Enumerable.Empty<string>()
            };
            var variable = literal.Ancestors().OfType<VariableDeclaratorSyntax>().FirstOrDefault();
            var named = identifiers.Any(LayoutName) || (variable is not null && LayoutName(variable.Identifier.ValueText));
            var container = literal.Ancestors().OfType<BaseTypeDeclarationSyntax>().Any(t => LayoutContainer(t.Identifier.ValueText));
            // 含运行时结构全名的数值初始化器，覆盖字典、数组与元组布局表。
            var initializer = literal.Ancestors().OfType<EqualsValueClauseSyntax>().FirstOrDefault();
            var table = initializer is not null && initializer.DescendantTokens().Any(t =>
                t.IsKind(SyntaxKind.StringLiteralToken) && records.Any(r => Normalize(t.ValueText).StartsWith(r, StringComparison.OrdinalIgnoreCase)));
            if (named || container || table)
                yield return $"{path}:{literal.GetLocation().GetLineSpan().StartLinePosition.Line + 1}：布局数值应来自 RuntimeSpec（{literal.Token.Text}）。";
        }
    }

    public static void Check(Assertions checks, string root)
    {
        var guard = new RuntimeLayoutArchitecture(root);
        foreach (var file in Directory.EnumerateFiles(Path.Combine(root, "src"), "*.cs", SearchOption.AllDirectories)
                     .Where(p => !p.Split(Path.DirectorySeparatorChar).Any(s => s is "obj" or "bin")))
        {
            // Runtime 的读取模型本身含位/字节换算；仍扫描它的具名布局声明。
            foreach (var violation in guard.Inspect(File.ReadAllText(file), Path.GetRelativePath(root, file)))
                checks.True(false, violation);
        }
        using var doc = JsonDocument.Parse(File.ReadAllText(Directory.EnumerateFiles(Path.Combine(root, "spec"), "unity-*.json").First()));
        var value = doc.RootElement.GetProperty("records").GetProperty("Il2CppObject").GetProperty("size").GetRawText();
        foreach (var code in new[] {
            $"class Probe {{ const int ObjectHeaderSize = {value}; }}",
            $"class Il2CppClassOffsets {{ static readonly int Vtable = {value}; }}",
            $"class Probe {{ int Il2CppClass_vtableOffset => {value}; }}",
            $"class Probe {{ object table = new object[] {{ (\"Il2CppObject\", {value}) }}; }}" })
            checks.True(guard.Inspect(code, "fixture").Any(), "布局架构检查必须拒绝违规声明或表");
        checks.True(!guard.Inspect("class Probe { int Count = 3; string Text = \"ObjectHeaderSize\"; }", "fixture").Any(),
            "普通计数、字符串与注释不应误报");
        checks.True(!guard.Inspect("class Probe { long ObjectHeaderSize => spec.Record(\"Il2CppObject\").Size; }", "fixture").Any(),
            "按名称查询规格应通过");
    }
}
