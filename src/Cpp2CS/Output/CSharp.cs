using System.Text;
using Cpp2CS.Metadata;
using Cpp2CS.Semantics;

namespace Cpp2CS.Output;

public sealed record SourceLine(int Line, string Method, string Address, int Node);

/// <summary>只处理已绑定的托管表示，不读取 ctree 或伪代码。</summary>
public sealed class CSharp(Catalog catalog)
{
    readonly StringBuilder text = new();
    readonly Layouts layouts = new(catalog);
    readonly List<SourceLine> mapping = [];
    int line, temporary;
    string current = "";
    void Write(string value = "") { text.AppendLine(value); line++; }
    public IReadOnlyList<SourceLine> Mapping => mapping;
    public static string Type(string type) => type switch
    {
        "System.Void" => "void", "System.Boolean" => "bool", "System.SByte" => "sbyte", "System.Byte" => "byte",
        "System.Int16" => "short", "System.UInt16" => "ushort", "System.Int32" => "int", "System.UInt32" => "uint",
        "System.Int64" => "long", "System.UInt64" => "ulong", "System.Single" => "float", "System.Double" => "double",
        _ => "global::" + type
    };
    static string Id(string name) => "@" + name;
    static string Name(string full) => full[(full.LastIndexOf('.') + 1)..];
    static string Cast(string expression, string type) => type == "System.Boolean" ? expression : $"(({Type(type)})({expression}))";
    string Number(Constant value)
    {
        if (value.Type == "System.Boolean") return value.Bits == 0 ? "false" : "true";
        return value.Type switch
        {
            "System.Int32" => unchecked((int)value.Bits).ToString(System.Globalization.CultureInfo.InvariantCulture),
            "System.UInt32" => unchecked((uint)value.Bits).ToString(System.Globalization.CultureInfo.InvariantCulture) + "U",
            "System.Int64" => unchecked((long)value.Bits).ToString(System.Globalization.CultureInfo.InvariantCulture) + "L",
            "System.UInt64" => $"0x{value.Bits:x}UL",
            _ => Cast($"0x{value.Bits:x}UL", value.Type)
        };
    }
    static string Narrow(string expression, string type) => type is "System.Byte" or "System.SByte" or "System.Int16" or "System.UInt16" ? Cast(expression, type) : expression;
    string Expression(Value value) => value switch
    {
        Local local => local.Name == "this" ? "this" : Id(local.Name),
        Constant constant => Number(constant),
        Conversion convert when convert.Type == "System.Boolean" => $"({Expression(convert.Operand)} != 0)",
        Conversion convert => Cast(Expression(convert.Operand), convert.Type),
        FieldValue field => Expression(field.Root) + "." + Id(field.Field.Name),
        Binary binary => Narrow($"({Expression(binary.Left)} {binary.Operation} {Expression(binary.Right)})", binary.Type),
        Unary unary => Narrow($"({unary.Operation}{Expression(unary.Operand)})", unary.Type),
        Choice choice => Cast($"({Expression(choice.Condition)} ? {Expression(choice.True)} : {Expression(choice.False)})", choice.Type),
        PackedLoad load => Cast(string.Join(" | ", load.Fields.Select(f =>
            $"((ulong){Cast(Expression(new FieldValue(load.Root, f.Field)), Layouts.Integer(layouts.Size(f.Field.Type), false))} << {f.Shift})")), load.Type),
        _ => throw new NotSupportedException(value.GetType().Name)
    };

    void Statements(IEnumerable<Statement> statements, string indent)
    {
        foreach (var statement in statements)
        {
            mapping.Add(new(line + 1, current, statement.Source.Address, statement.Source.Node));
            switch (statement)
            {
                case Store store:
                    Write($"{indent}{Expression(store.Target)} = {Expression(store.Value)};"); break;
                case PackedStore store:
                    var name = "bits" + temporary++;
                    Write($"{indent}{Type(Layouts.Integer(store.Width, false))} {name} = {Expression(store.Value)};");
                    foreach (var field in store.Fields)
                        Write($"{indent}{Expression(new FieldValue(store.Root, field.Field))} = {Cast($"({name} >> {field.Shift})", field.Field.Type)};");
                    break;
                case Return ret: Write($"{indent}return{(ret.Value is null ? "" : " " + Expression(ret.Value))};"); break;
                case BaseInitialize:
                    Write($"{indent}// System.Object 的构造由 C# 构造入口执行。"); break;
                case If branch:
                    Write($"{indent}if ({Expression(branch.Condition)})"); Write(indent + "{");
                    Statements(branch.True, indent + "    "); Write(indent + "}");
                    if (branch.False.Length > 0)
                    {
                        Write(indent + "else"); Write(indent + "{");
                        Statements(branch.False, indent + "    "); Write(indent + "}");
                    }
                    break;
                default: throw new NotSupportedException(statement.GetType().Name);
            }
        }
    }

    string Parameters(Method method) => string.Join(", ", method.Parameters.Select(p =>
        $"{Type(p.Type)} {Id(p.Name)}" + (p.Default is null ? "" : $" = ({Type(p.Type)})({p.Default})")));

    public string Generate(IReadOnlyDictionary<string, Body[]> bodies)
    {
        Write("// 从 IDA ctree 与匹配元数据生成；原生地址映射见 source-map.json。");
        foreach (var model in catalog.Enums)
        {
            Write($"namespace {model.Name[..model.Name.LastIndexOf('.')]}"); Write("{");
            Write($"    public enum {Id(Name(model.Name))} : int"); Write("    {");
            foreach (var member in model.Members) Write($"        {Id(member.Key)} = {member.Value},");
            Write("    }"); Write("}");
        }
        foreach (var model in catalog.Types)
        {
            Write($"namespace {model.Name[..model.Name.LastIndexOf('.')]}"); Write("{");
            if (model.ValueType) Write("    [global::System.Runtime.InteropServices.StructLayout(global::System.Runtime.InteropServices.LayoutKind.Sequential)]");
            Write($"    public {(model.ValueType ? "struct" : model.Sealed ? "sealed class" : "class")} {Id(Name(model.Name))}"); Write("    {");
            foreach (var field in model.Fields)
                Write($"        {(field.Public ? "public" : "private")} {(field.ReadOnly ? "readonly " : "")}{Type(field.Type)} {Id(field.Name)};");
            foreach (var body in bodies[model.Name])
            {
                var method = body.Method;
                current = model.Name + "." + method.Name;
                Write(); Write($"        // RVA {method.Address}; Token {method.Token}");
                string prefix = "        public " + (method.Static ? "static " : "");
                if (method.Name == ".ctor") Write(prefix + Id(Name(model.Name)) + "(" + Parameters(method) + ")");
                else if (method.Property is not null) Write(prefix + Type(method.ReturnType) + " " + Id(method.Property));
                else if (method.Name is "op_Addition" or "op_Subtraction")
                    Write(prefix + Type(method.ReturnType) + " operator " + (method.Name == "op_Addition" ? "+" : "-") + "(" + Parameters(method) + ")");
                else Write(prefix + Type(method.ReturnType) + " " + Id(method.Name) + "(" + Parameters(method) + ")");
                Write("        {");
                string indent = "            ";
                if (method.Property is not null) { Write(indent + "get"); Write(indent + "{"); indent += "    "; }
                Write(indent + "unchecked"); Write(indent + "{"); indent += "    ";
                foreach (var local in body.Locals) Write($"{indent}{Type(local.Type)} {Id(local.Name)};");
                Statements(body.Statements, indent);
                indent = indent[..^4]; Write(indent + "}");
                if (method.Property is not null) Write("            }");
                Write("        }");
            }
            Write("    }"); Write("}");
        }
        return text.ToString();
    }
}
