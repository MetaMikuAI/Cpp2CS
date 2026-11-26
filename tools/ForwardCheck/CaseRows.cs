using System.Collections.Immutable;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Sources;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// 情况行与走查路径在路径条件格下的读法（设计 7.7）。分情况与走查只枚举结构、按边代入；
/// 一组文字能否同时成立、各项在它们之下的取值，都问格。
/// </summary>
internal static class CaseRows
{
    /// <summary>
    /// 把一组沿路径成立的文字加进格里；矛盾时为空。含未定义位的文字不加入：同一个未定义的项可以代表互不相关的位（设计 7.2），
    /// 少加文字只会少剔除。调用的正常返回与展开不是项上的文字，不加入。
    /// </summary>
    public static PathConditions? Assume(PathConditions lattice, IEnumerable<PathLiteral> literals, TermPool terms)
    {
        PathConditions? current = lattice;
        foreach (var literal in literals)
        {
            if (current is null) return null;
            if (literal.Term is not { HasUndefined: false } term) continue;
            switch (literal.Kind)
            {
                case LiteralKind.Condition:
                    current = current.With(term, literal.Value != 0);
                    break;
                case LiteralKind.Selector:
                    current = current.With(terms.Eq(term, terms.Constant(literal.Value, term.Width)), true);
                    break;
                case LiteralKind.SelectorDefault:
                    for (long k = 0; current is not null && k < literal.Value; k++)
                        current = current.With(terms.Eq(term, terms.Constant(k, term.Width)), false);
                    break;
            }
        }
        return current;
    }

    /// <summary>行在格下可行时，各项在这一行的条件下求值的结果；不可行时为空。</summary>
    public static ImmutableArray<Term>? Evaluate(Case row, PathConditions lattice, TermPool terms) =>
        Assume(lattice, row.Conditions, terms) is { } assumed ? [.. row.Terms.Select(assumed.Evaluate)] : null;

    /// <summary>对照用的键：只取求值之后的项。条件的写法两边可以不同，可行与否已由格判断。</summary>
    public static string Key(ImmutableArray<Term> terms) => string.Join(",", terms.Select(t => t.Id));
}
