using Cpp2CS.Input;
using Cpp2CS.Metadata;
using Cpp2CS.Semantics;
using static Cpp2CS.Semantics.Layouts;

namespace Cpp2CS.Recovery;

/// <summary>将 ctree 的读写和运算绑定到托管存储；不匹配方法名或具体计算公式。</summary>
public sealed class Recover
{
    readonly Catalog catalog;
    readonly TypeModel owner;
    readonly Method method;
    readonly Ctree tree;
    readonly Layouts layouts;
    readonly Dictionary<int, Local> variables = [];
    readonly List<Local> locals = [];

    public Recover(Catalog catalog, TypeModel owner, Method method, Ctree tree)
    {
        this.catalog = catalog; this.owner = owner; this.method = method; this.tree = tree;
        layouts = new(catalog);
        int expected = method.Parameters.Length + (method.Static ? 0 : 1) + 1;
        if (tree.Arguments.Length != expected) throw new InvalidOperationException("ctree 参数数量与元数据不符");
        int slot = 0;
        if (!method.Static)
        {
            var self = tree.Variables.Single(v => v.Id == tree.Arguments[slot]);
            if (self.NativeType.Kind != "pointer" || self.NativeType.Pointee != owner.NativeName)
                throw new InvalidOperationException("this 的原生类型与元数据不符");
            variables.Add(tree.Arguments[slot++], new("this", owner.Name, true));
        }
        foreach (var parameter in method.Parameters)
        {
            var native = tree.Variables.Single(v => v.Id == tree.Arguments[slot]);
            string managed = layouts.Managed(native.NativeType);
            if (managed != parameter.Type && !(catalog.IsEnum(parameter.Type) && managed == "System.Int32"))
                throw new InvalidOperationException($"参数类型不符: {parameter.Name}");
            variables.Add(tree.Arguments[slot++], new(parameter.Name, parameter.Type, true));
        }
        var runtime = tree.Variables.Single(v => v.Id == tree.Arguments[slot]);
        if (runtime.NativeType.Pointee != "const MethodInfo") throw new InvalidOperationException("缺少 MethodInfo 参数");
        // 未使用的原生临时变量不需要托管声明；被引用时才建立局部变量。
    }

    Local Variable(int index)
    {
        if (variables.TryGetValue(index, out var value)) return value;
        var native = tree.Variables.Single(v => v.Id == index);
        if (native.Argument) throw new NotSupportedException("业务逻辑读取 MethodInfo");
        value = new("local" + index, layouts.Managed(native.NativeType), false);
        variables.Add(index, value); locals.Add(value);
        return value;
    }
    Node Child(Node n, string role) => tree[n.Int(role)];
    static Origin Source(Node n) => new(n.Id, n.Address);
    Exception Unsupported(Node n, string reason) => new NotSupportedException($"{owner.Name}.{method.Name} {n.Address} node {n.Id} {n.Op}: {reason}");

    public Body Run()
    {
        var statements = Statements(tree[tree.Root]);
        if (!owner.ValueType && method.Name == ".ctor" && statements.FirstOrDefault() is not BaseInitialize)
            throw new NotSupportedException("引用构造必须首先调用已确认的 Object 构造");
        if (statements.Skip(1).Any(s => s is BaseInitialize)) throw new InvalidOperationException("重复或后置基类初始化");
        return new(method, locals.ToArray(), statements);
    }

    Statement[] Statements(Node n)
    {
        if (n.Int("label") >= 0) throw Unsupported(n, "带标签语句尚未恢复");
        return n.Op switch
        {
            "block" => n.List("items").SelectMany(i => Statements(tree[i])).ToArray(),
            "expr" => [Effect(Child(n, "expression"))],
            "return" => [new Return(Source(n), Cast(Value(Child(n, "expression")), method.ReturnType))],
            "if" => [new If(Source(n), Boolean(Value(Child(n, "condition"))), Statements(Child(n, "then")),
                n.Data.GetProperty("else").ValueKind == System.Text.Json.JsonValueKind.Null ? [] : Statements(Child(n, "else")))],
            _ => throw Unsupported(n, "语句未支持")
        };
    }

    Statement Effect(Node n)
    {
        if (n.Op == "call")
        {
            var callee = Child(n, "x");
            var arguments = n.List("arguments");
            if (method.Name != ".ctor" || owner.ValueType || callee.Op != "obj" ||
                !callee.Text("object").Equals(catalog.ObjectConstructorAddress, StringComparison.OrdinalIgnoreCase) || arguments.Length != 2)
                throw Unsupported(n, "调用没有托管契约");
            var receiver = Place(tree[arguments[0]]);
            var info = Value(tree[arguments[1]]);
            if (receiver.Root.Name != "this" || receiver.Offset != 0 || info is not Constant { Bits: 0 })
                throw Unsupported(n, "Object 构造实参不符");
            return new BaseInitialize(Source(n), callee.Text("object"));
        }
        if (n.Op is not ("asg" or "asgadd" or "asgsub")) throw Unsupported(n, "赋值未支持");
        var target = Child(n, "x");
        var value = Value(Child(n, "y"));
        if (n.Op != "asg")
        {
            var type = layouts.Managed(n.Type);
            value = new Binary(n.Op == "asgadd" ? "+" : "-", Cast(Value(target), type), Cast(value, type), type);
        }
        if (target.Op == "var") return new Store(Source(n), Variable(target.Int("variable")), Cast(value, Variable(target.Int("variable")).Type));
        var place = Place(target);
        int width = checked((int)target.Type.Bytes);
        var fields = layouts.Span(place, width);
        if (fields.Any(f => f.Field.ReadOnly) && (method.Name != ".ctor" || place.Root.Name != "this"))
            throw Unsupported(n, "只读字段写入不在本对象构造中");
        if (fields.Length == 1)
            return new Store(Source(n), new FieldValue(place.Root, fields[0].Field), Cast(value, fields[0].Field.Type));
        if (width is not (2 or 4 or 8)) throw Unsupported(n, "合并写入超过标量宽度");
        layouts.RequirePackable(fields);
        return new PackedStore(Source(n), place.Root, fields, Cast(value, Integer(width, false)), width);
    }

    Storage Place(Node n) => n.Op switch
    {
        "var" => new(Variable(n.Int("variable")), 0),
        "memptr" or "memref" => Offset(Place(Child(n, "x")), n.Int("offset")),
        "cast" when n.Type.Kind == "pointer" => Place(Child(n, "x")),
        "ref" or "ptr" => Place(Child(n, "x")),
        _ => throw Unsupported(n, "地址来源未确定")
    };
    static Storage Offset(Storage storage, int offset) => storage with { Offset = checked(storage.Offset + offset) };

    Value Boolean(Value value) => value.Type == "System.Boolean" ? value :
        new Binary("!=", value, new Constant(0, value.Type), "System.Boolean");

    Value Value(Node n)
    {
        if (n.Op == "var") return Variable(n.Int("variable"));
        if (n.Op == "num") return new Constant(ulong.Parse(n.Text("number")), layouts.Managed(n.Type));
        if (n.Op is "memptr" or "memref" or "ptr") return layouts.Load(Place(n), layouts.Managed(n.Type));
        if (n.Op == "cast") return Cast(Value(Child(n, "x")), layouts.Managed(n.Type));
        if (n.Op == "tern") return new Choice(Boolean(Value(Child(n, "x"))), Value(Child(n, "y")), Value(Child(n, "z")), layouts.Managed(n.Type));
        if (n.Op is "lnot" or "bnot" or "neg")
        {
            var type = layouts.Managed(n.Type);
            var operand = Value(Child(n, "x"));
            return new Unary(n.Op == "lnot" ? "!" : n.Op == "bnot" ? "~" : "-",
                n.Op == "lnot" ? Boolean(operand) : Cast(operand, type), type);
        }
        var operation = n.Op switch
        {
            "add" => "+", "sub" => "-", "mul" => "*", "band" => "&", "bor" => "|", "xor" => "^",
            "land" => "&&", "lor" => "||", "eq" => "==", "ne" => "!=",
            "sge" or "uge" => ">=", "sgt" or "ugt" => ">", "sle" or "ule" => "<=", "slt" or "ult" => "<",
            "shl" => "<<", "sshr" or "ushr" => ">>",
            _ => throw Unsupported(n, "表达式未支持")
        };
        var left = Value(Child(n, "x")); var right = Value(Child(n, "y"));
        string result = layouts.Managed(n.Type);
        if (n.Op is "land" or "lor") return new Binary(operation, Boolean(left), Boolean(right), result);
        string operandType = result;
        if (n.Op is "sge" or "uge" or "sgt" or "ugt" or "sle" or "ule" or "slt" or "ult" or "eq" or "ne")
            operandType = Integer(Math.Max(checked((int)Child(n, "x").Type.Bytes), checked((int)Child(n, "y").Type.Bytes)),
                n.Op.StartsWith('s') || (n.Op is "eq" or "ne" && Child(n, "x").Type.Signed));
        return new Binary(operation, Cast(left, operandType),
            Cast(right, n.Op is "shl" or "sshr" or "ushr" ? "System.Int32" : operandType), result);
    }
}
