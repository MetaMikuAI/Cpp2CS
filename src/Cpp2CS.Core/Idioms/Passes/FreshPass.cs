using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class FreshPass
{
    internal static Variable Fresh(this IdiomState state)
    {
        if (state.Names is null)
        {
            var variables = state.function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
            {
                Define d => [d.Target],
                Phi p => p.Sources.Append(p.Target),
                Call c => c.Defines.Where(v => v is not null),
                _ => Array.Empty<Variable>(),
            }).Concat(state.function.Dead.Select(d => d.Define.Target));
            state.Names = new(variables.Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1);
        }

        return new Variable(Storage.Temp(state.Names.Next()), 1);
    }
}
