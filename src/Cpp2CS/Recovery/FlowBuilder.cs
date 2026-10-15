using Cpp2CS.Input;
using Cpp2CS.Semantics;

namespace Cpp2CS.Recovery;

/// <summary>把结构化语句和显式跳转统一为基本块，保留跳入条件分支的合法原生边。</summary>
public sealed class FlowBuilder(Ctree tree, Func<Node,Value> value, Func<Node,Statement> effect, Func<Value,Value> boolean, string returnType)
{
    sealed record NativeJump(int Label) : Transfer;
    sealed record MissingReturn : Transfer;
    readonly Dictionary<int,FlowBlock> blocks = [];
    readonly Dictionary<int,int> labels = [];
    int nextId;
    Node Child(Node n,string key) => tree[n.Int(key)];
    Origin Source(Node n) => new(n.Id,n.Address);
    int Block(Node n,Transfer transfer, params Statement[] statements)
    {
        int id = nextId++;
        blocks.Add(id,new(id,Source(n),statements,transfer));
        return id;
    }
    int Expression(Node n,int next) => n.Op == "empty" ? next : Block(n,new Jump(next),effect(n));
    int Compile(Node n,int next,int? onBreak,int? onContinue)
    {
        int entry;
        switch (n.Op)
        {
            case "block":
                entry = next;
                foreach (int child in n.List("items").Reverse()) entry = Compile(tree[child],entry,onBreak,onContinue);
                break;
            case "expr": entry = Expression(Child(n,"expression"),next); break;
            case "empty": entry = next; break;
            case "return":
                var expression = Child(n,"expression");
                entry = Block(n,new Finish(expression.Op == "empty" ? null : Layouts.Cast(value(expression),returnType))); break;
            case "goto": entry = Block(n,new NativeJump(n.Int("target"))); break;
            case "break": entry = Block(n,new Jump(onBreak ?? throw new InvalidOperationException("break 没有目标"))); break;
            case "continue": entry = Block(n,new Jump(onContinue ?? throw new InvalidOperationException("continue 没有目标"))); break;
            case "if":
                int yes = Compile(Child(n,"then"),next,onBreak,onContinue);
                int no = n.Data.GetProperty("else").ValueKind == System.Text.Json.JsonValueKind.Null ? next : Compile(Child(n,"else"),next,onBreak,onContinue);
                entry = Block(n,new Branch(boolean(value(Child(n,"condition"))),yes,no)); break;
            case "while":
            case "do":
            case "for":
                int test = Block(n,new Jump(next));
                int step = n.Op == "for" ? Expression(Child(n,"step"),test) : test;
                int body = Compile(Child(n,"body"),step,next,step);
                var conditionNode = Child(n,"condition");
                var condition = conditionNode.Op == "empty" ? new Constant(1,"System.Boolean") : boolean(value(conditionNode));
                blocks[test] = blocks[test] with { Transfer = new Branch(condition,body,next) };
                entry = n.Op == "do" ? body : n.Op == "for" ? Expression(Child(n,"init"),test) : test;
                break;
            case "switch":
                var cases = n.Data.GetProperty("cases").EnumerateArray().ToArray();
                var arms = new List<SwitchArm>();
                int fallThrough = next, fallback = next;
                foreach (var arm in cases.Reverse())
                {
                    fallThrough = Compile(tree[arm.GetProperty("body").GetInt32()],fallThrough,next,onContinue);
                    var values = arm.GetProperty("values").EnumerateArray().ToArray();
                    if (values.Length == 0) fallback = fallThrough;
                    foreach (var literal in values)
                        arms.Add(new(literal.TryGetUInt64(out var bits) ? bits : unchecked((ulong)literal.GetInt64()),fallThrough));
                }
                entry = Block(n,new Select(value(Child(n,"expression")),arms.ToArray(),fallback));
                break;
            default: throw new NotSupportedException($"控制流节点未支持: {n.Id} {n.Op}");
        }
        if (n.Int("label") >= 0) labels.Add(n.Int("label"),entry);
        return entry;
    }

    public ControlFlow Build()
    {
        var root = tree[tree.Root];
        int finish = Block(root,returnType == "System.Void" ? new Finish(null) : new MissingReturn());
        int entry = Compile(root,finish,null,null);
        foreach (var (id,block) in blocks.ToArray())
        {
            if (block.Transfer is NativeJump jump)
                blocks[id] = block with { Transfer = new Jump(labels[jump.Label]) };
            else if (block.Transfer is Branch { Condition: Constant { Type: "System.Boolean" } c } branch)
                blocks[id] = block with { Transfer = new Jump(c.Bits == 0 ? branch.False : branch.True) };
        }
        var reachable = new HashSet<int>();
        var pending = new Stack<int>();
        pending.Push(entry);
        while (pending.TryPop(out int id))
        {
            if (!reachable.Add(id)) continue;
            foreach (int target in blocks[id].Transfer switch
            {
                Jump jump => new[] { jump.Target }, Branch branch => new[] { branch.True,branch.False },
                Select select => select.Arms.Select(a=>a.Target).Append(select.Default),
                Finish => [], _ => throw new InvalidOperationException("存在未返回的控制流路径")
            }) pending.Push(target);
        }
        return new(Source(root),entry,blocks.Values.Where(b=>reachable.Contains(b.Id)).ToArray());
    }
}
