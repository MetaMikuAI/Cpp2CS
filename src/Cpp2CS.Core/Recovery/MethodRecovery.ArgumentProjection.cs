using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private Dictionary<Storage, int> StructArgumentWidths(Call call)
        {
            var widths = new Dictionary<Storage, int>();
            var methods = Callee(call) is { } indirect ? [indirect]
                : call.Op is null && call.Target is Const target ? facts.EntriesAt(target.Value)
                    .Where(e => e.Kind is EntryKind.Method or EntryKind.GenericMethod && e.Method is not null)
                    .Select(e => e.Method!).Distinct().ToArray() : Array.Empty<MethodRef>();
            if (methods.Length == 0) return widths;
            var signatures = methods.Select(m => owner.abi.Classify(m, out _)).ToArray();
            if (signatures.Any(s => s is null)) return widths;
            foreach (var register in call.Sources.Where(s => s.Bank == Bank.Gpr))
            {
                var pieces = signatures.Select(s => s!.Arguments.Where(a => RegisterStruct(a))
                    .SelectMany(a => a.Pieces).SingleOrDefault(p => p.Register == register)).ToArray();
                // 共用入口须全部认定为同宽结构体片，不能根据其中一种签名丢弃参数位。
                if (pieces.All(p => p is not null) && pieces.Select(p => p!.Width).Distinct().ToArray() is [> 0 and < 64 and var width])
                    widths[register] = width;
            }
            return widths;
        }
    }
}
