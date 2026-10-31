using System.Buffers.Binary;
using System.Runtime.InteropServices;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using CallingConvention = System.Runtime.InteropServices.CallingConvention;

namespace Cpp2CS.Recovery;

/// <summary>IL2CPP 的缓存导入包装：PInvokeArguments、一次解析、标量转发及 HandleRef 句柄投影。</summary>
internal static class PlatformImportPattern
{
    internal static bool IsHandleRef(TypeRef type) => type is DefinitionRef
    {
        Definition: { Assembly: "mscorlib.dll", Namespace: "System.Runtime.InteropServices", Name: "HandleRef", DeclaringType: null, IsValueType: true }, Arguments.Count: 0
    };

    internal static AbiPiece? ForwardedPiece(AbiValue value) => value.Passing != Passing.Registers ? null
        : IsHandleRef(value.Type) ? value.Pieces is [{ Register.Bank: Bank.Gpr, Width: 64, Offset: 0 }, { Register.Bank: Bank.Gpr, Width: 64, Offset: 8 } handle] ? handle : null
        : value.Pieces is [var scalar] ? scalar : null;

    internal static NativeImport? Match(MachineFunction function, AbiSignature signature, Func<ulong, ulong, string?> readName, Func<ulong, bool> emptyCache)
    {
        var forwarded = signature.Parameters.Select(ForwardedPiece).ToArray();
        if (forwarded.Any(p => p is null)) return null;
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
            || BinaryPrimitives.ReadInt32LittleEndian(arguments[40..]) != forwarded.Sum(p => Math.Max(4, p!.Width / 8))) return null;
        var inputs = call.ArgumentsBySource();
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
        var conversions = new HashSet<Define>();
        Expr Expand(Expr expression, int depth = 12) => depth == 0 ? expression : Fold.Simplify(ExprMap.Map(expression, part =>
        {
            if (part is not Use use || !definitions.TryGetValue(use.Variable, out var define) || !InlineConstructors.Pure(define.Value)) return null;
            conversions.Add(define);
            return ScalarVectorNarrowing.Low(Expand(define.Value, depth - 1), use.Width);
        }));
        static Expr Strip(Expr value)
        {
            while (value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } conversion) value = conversion.Operand;
            return value;
        }
        var integer = 0;
        var vector = 0;
        for (var i = 0; i < forwarded.Length; i++)
        {
            var piece = forwarded[i];
            var native = piece!.Register.Bank == Bank.Gpr ? Storage.Gpr(integer++) : Storage.Vec(vector++);
            if (!inputs.TryGetValue(native, out var input)) return null;
            input = Expand(input);
            // IL2CPP 的 bool 输入是 0/1；默认 P/Invoke BOOL 将其扩成 32 位。
            if (ManagedTypes.PrimitiveName(signature.Parameters[i].Type) == "Boolean"
                && Strip(input) is Binary { Op: BinOp.And, Left: var boolean, Right: Const { Value: 1 } }) input = boolean;
            if (ScalarVectorNarrowing.Low(input, piece.Width) is not Use { Variable.Version: 0 } original
                || original.Variable.Storage != piece.Register) return null;
        }
        if (invoke.Statements.LastOrDefault() is not Return returned || returned.Buffer is not null || returned.Pieces.Length != 0) return null;
        if (signature.Return is { } result)
        {
            var piece = result.Pieces[0];
            if (returned.Value is null) return null;
            var value = Expand(returned.Value);
            if (ManagedTypes.PrimitiveName(result.Type) == "Boolean")
            {
                value = Strip(value);
                value = value switch
                {
                    Select { Condition: Compare { Cond: Cond.Eq, Left: Use { Width: 32 } boolean, Right: Const { Value: 0 } }, True: Const { Value: 0 }, False: Const { Value: 1 } } => boolean,
                    Compare { Cond: Cond.Ne, Left: Use { Width: 32 } boolean, Right: Const { Value: 0 } } => boolean,
                    _ => null!,
                };
                if (value is null) return null;
            }
            if (ScalarVectorNarrowing.Low(value, piece.Width) is not Use output
                || !call.Defines.Contains(output.Variable) || output.Variable.Storage != piece.Register) return null;
        }
        else if (returned.Value is not null) return null;
        // 不允许额外调用、访存或控制流；寄存器保存必须落在参数结构之外。
        foreach (var block in function.Blocks)
            foreach (var statement in block.Statements)
            {
                if (statement == cacheRead || statement == branch || statement == resolver || statement == call || statement == returned || stores.Contains(statement)) continue;
                if (statement is Define conversion && conversions.Contains(conversion)) continue;
                if (statement is Nop || block == invoke && statement is Phi || block == resolve && statement is Jump { Target: var destination } && destination == invoke.Start) continue;
                if (block == entry && statement is Store { Target: FrameAddress saved, Value: Use { Variable.Version: 0 } register }
                    && (saved.Offset + register.Width / 8 <= buffer.Offset || saved.Offset >= buffer.Offset + arguments.Length)
                    && (register.Variable.Storage == Storage.Gpr(30) || Enumerable.Range(19, 10).Any(i => register.Variable.Storage == Storage.Gpr(i))
                        || register.Width == 64 && register.Variable.Storage is { Bank: Bank.Vec, Index: >= 8 and <= 15 })) continue;
                return null;
            }
        return new(library, symbol)
        {
            CallingConvention = convention switch { 0 => CallingConvention.Winapi, 1 => CallingConvention.Cdecl, 2 => CallingConvention.StdCall, 3 => CallingConvention.ThisCall, _ => CallingConvention.FastCall },
            CharSet = charset switch { 0 => CharSet.Ansi, 1 => CharSet.Unicode, _ => CharSet.None },
            ExactSpelling = arguments[44] != 0
        };
    }
}
