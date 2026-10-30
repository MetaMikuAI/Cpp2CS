using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class DefinedPass
{
    internal static HashSet<Variable> Defined(IEnumerable<Block> blocks)
    {
        var set = new HashSet<Variable>();
        foreach (var stmt in blocks.SelectMany(b => b.Statements))
            switch (stmt)
            {
                case Define d:
                    set.Add(d.Target);
                    break;
                case Phi p:
                    set.Add(p.Target);
                    break;
                case Call c:
                    foreach (var v in c.Defines)
                        if (v is not null)
                            set.Add(v);
                    break;
            }

        return set;
    }
}
