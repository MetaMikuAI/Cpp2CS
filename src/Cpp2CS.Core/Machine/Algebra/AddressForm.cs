using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Algebra;

internal enum AddressShape { Sum, LeftConstants }
internal enum AddressExpansion { None, Leaves, BeforeSplit }

internal sealed record AddressPolicy
{
    public AddressShape Shape { get; init; }
    public AddressExpansion Expansion { get; init; }
    public bool SignedConstants { get; init; } = true;
    public bool PreserveLeaf { get; init; }
    public Func<Expr, Expr>? Expand { get; init; }
    public Func<Expr, bool>? Root { get; init; }
    public Func<Binary, bool>? Addition { get; init; }
}

/// <summary>地址分解只处理代数形态；根的含义、定义展开与常量符号由调用方指定。</summary>
internal sealed record AddressForm(Expr? Root, long Offset, List<Expr> Terms)
{
    public static AddressForm Decompose(Expr address, AddressPolicy policy)
    {
        long offset = 0;
        var terms = new List<Expr>();
        long Value(Const c) => policy.SignedConstants ? c.Signed : unchecked((long)c.Value);
        if (policy.Shape == AddressShape.LeftConstants)
        {
            while (address is Binary { Op: BinOp.Add, Right: Const constant } add && (policy.Addition?.Invoke(add) ?? true))
            {
                offset = unchecked(offset + Value(constant));
                address = add.Left;
            }
            return new(address, offset, []);
        }
        // 显式栈保持从左到右的求值顺序，避免地址树深度影响宿主调用栈。
        var pending = new Stack<Expr>();
        pending.Push(address);
        while (pending.TryPop(out var original))
        {
            var value = policy.Expansion == AddressExpansion.BeforeSplit ? policy.Expand!(original) : original;
            if (value is Binary { Op: BinOp.Add } add && (policy.Addition?.Invoke(add) ?? true))
            {
                pending.Push(add.Right);
                pending.Push(add.Left);
                continue;
            }
            if (policy.Expansion == AddressExpansion.Leaves) value = policy.Expand!(value);
            if (value is Const constant) offset = unchecked(offset + Value(constant));
            else terms.Add(policy.PreserveLeaf ? original : value);
        }
        var root = policy.Root is { } predicate ? terms.FirstOrDefault(predicate) : terms.Count == 1 ? terms[0] : null;
        if (root is not null) terms.Remove(root);
        return new(root, offset, terms);
    }
}
