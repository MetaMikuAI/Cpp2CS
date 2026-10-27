using System.Buffers.Binary;
using System.Runtime.InteropServices;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using CallingConvention = System.Runtime.InteropServices.CallingConvention;

namespace Cpp2CS.Recovery;

/// <summary>IL2CPP 的缓存导入包装：PInvokeArguments、一次解析、参数原样转调；不处理封送。</summary>
internal static class PlatformImportPattern
{
    internal static NativeImport? Match(MachineFunction function, AbiSignature signature, Func<ulong, ulong, string?> readName, Func<ulong, bool> emptyCache)
    {
        if (function.Problems.Count != 0 || function.Blocks.Count != 3 || function.Blocks.Any(b => b.Handler is not null || b.IsLandingPad)) return null;
        var entry = function.EntryBlock;
        if (entry.Statements.LastOrDefault() is not Branch { Condition: Compare { Cond: Cond.Ne, Left: Use cached, Right: Const { Value: 0 } } } branch
            || entry.Statements.OfType<Define>().SingleOrDefault(d => d.Target == cached.Variable) is not { Value: Load { Address: Const cache, Width: 64 } } cacheRead
            || !emptyCache(cache.Value)) return null;
        var resolve = function.Blocks.SingleOrDefault(b => b.Start == branch.Fallthrough);
        var invoke = function.Blocks.SingleOrDefault(b => b.Start == branch.Target);
        if (resolve is null || invoke is null || resolve == entry || invoke == entry || resolve == invoke
            || !resolve.Predecessors.SequenceEqual([entry]) || !resolve.NormalSuccessors.SequenceEqual([invoke]) || invoke.Successors.Count != 0
            || resolve.Statements.OfType<Call>().ToArray() is not [{ Kind: CallKind.Direct, Op: null, Target: Const, Arguments: [FrameAddress buffer, ..] } resolver]
            || invoke.Statements.OfType<Call>().ToArray() is not [{ Kind: CallKind.Indirect, Op: null, Target: Use target } call]
            || resolver.Defines.FirstOrDefault(v => v.Storage == Storage.Gpr(0)) is not { } resolved
            || invoke.Statements.OfType<Phi>().SingleOrDefault(p => p.Target == target.Variable) is not { } targetPhi
            || targetPhi.Sources.Length != 2 || targetPhi.Sources.Length != invoke.Predecessors.Count
            || !invoke.Predecessors.Select((b, i) => b == entry ? targetPhi.Sources[i] == cached.Variable
                : b == resolve && targetPhi.Sources[i] == resolved).All(v => v)) return null;
        var stores = resolve.Statements.OfType<Store>().ToArray();
        if (stores.LastOrDefault() is not { Target: Const written, Value: Use pointer } cacheWrite
            || written != cache || pointer.Variable != resolved || pointer.Width != 64
            || resolve.Statements.IndexOf(cacheWrite) < resolve.Statements.IndexOf(resolver)) return null;
        Span<byte> arguments = stackalloc byte[45];
        Span<bool> assigned = stackalloc bool[45];
        assigned.Clear();
        foreach (var store in stores.Where(s => s != cacheWrite))
        {
            if (store is not { Target: FrameAddress frame, Value: Const value } || value.Width is not (8 or 16 or 32 or 64)
                || frame.Offset < buffer.Offset || frame.Offset - buffer.Offset > arguments.Length - value.Width / 8
                || resolve.Statements.IndexOf(store) > resolve.Statements.IndexOf(resolver)) return null;
            var offset = (int)(frame.Offset - buffer.Offset);
            for (var i = 0; i < value.Width / 8; i++)
            {
                if (assigned[offset + i]) return null;
                arguments[offset + i] = (byte)(value.Value >> (8 * i));
                assigned[offset + i] = true;
            }
        }
        if (assigned.Contains(false)) return null;
        // StringView<char> 的长度不含终止零；后接调用约定、字符集、参数大小、禁止名称修饰。
        var library = readName(BinaryPrimitives.ReadUInt64LittleEndian(arguments), BinaryPrimitives.ReadUInt64LittleEndian(arguments[8..]));
        var symbol = readName(BinaryPrimitives.ReadUInt64LittleEndian(arguments[16..]), BinaryPrimitives.ReadUInt64LittleEndian(arguments[24..]));
        var convention = BinaryPrimitives.ReadInt32LittleEndian(arguments[32..]);
        var charset = BinaryPrimitives.ReadInt32LittleEndian(arguments[36..]);
        if (library is null || symbol is null || convention is < 0 or > 4 || charset is < 0 or > 2 || arguments[44] > 1
            || BinaryPrimitives.ReadInt32LittleEndian(arguments[40..]) != signature.Parameters.Sum(p => Math.Max(4, p.Pieces[0].Width / 8))) return null;
        var inputs = call.ArgumentsBySource();
        foreach (var parameter in signature.Parameters)
        {
            var piece = parameter.Pieces[0];
            if (!inputs.TryGetValue(piece.Register, out var input)
                || ScalarVectorNarrowing.Low(input, piece.Width) is not Use { Variable.Version: 0 } original
                || original.Variable.Storage != piece.Register) return null;
        }
        if (invoke.Statements.LastOrDefault() is not Return returned || returned.Buffer is not null || returned.Pieces.Length != 0) return null;
        if (signature.Return is { } result)
        {
            var piece = result.Pieces[0];
            if (returned.Value is null || ScalarVectorNarrowing.Low(returned.Value, piece.Width) is not Use output
                || !call.Defines.Contains(output.Variable) || output.Variable.Storage != piece.Register) return null;
        }
        else if (returned.Value is not null) return null;
        // 不允许额外调用、访存或控制流；寄存器保存必须落在参数结构之外。
        foreach (var block in function.Blocks)
            foreach (var statement in block.Statements)
            {
                if (statement == cacheRead || statement == branch || statement == resolver || statement == call || statement == returned || stores.Contains(statement)) continue;
                if (statement is Nop || block == invoke && statement is Phi || block == resolve && statement is Jump { Target: var destination } && destination == invoke.Start) continue;
                if (block == entry && statement is Store { Target: FrameAddress saved, Value: Use { Variable.Version: 0 } register }
                    && (saved.Offset + register.Width / 8 <= buffer.Offset || saved.Offset >= buffer.Offset + arguments.Length)
                    && (register.Variable.Storage == Storage.Gpr(30) || Enumerable.Range(19, 10).Any(i => register.Variable.Storage == Storage.Gpr(i)))) continue;
                return null;
            }
        return new(library, symbol)
        {
            CallingConvention = convention switch { 0 => CallingConvention.Winapi, 1 => CallingConvention.Cdecl, 2 => CallingConvention.StdCall, 3 => CallingConvention.ThisCall, _ => CallingConvention.FastCall },
            CharSet = charset switch { 0 => CharSet.Ansi, 1 => CharSet.Unicode, _ => CharSet.None }, ExactSpelling = arguments[44] != 0
        };
    }
}
