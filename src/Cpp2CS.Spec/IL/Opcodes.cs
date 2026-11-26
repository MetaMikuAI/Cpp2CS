using System.Collections.Frozen;

namespace Cpp2CS.Spec.IL;

/// <summary>指令的内联操作数。</summary>
public enum OperandKind : byte
{
    None, Int8, Int32, Int64, Float32, Float64, Variable8, Variable16, Branch8, Branch32, Switch,
    Method, Field, Type, String, Signature, Token,
}

/// <summary>指令之后的去向。</summary>
public enum FlowKind : byte { Next, Branch, ConditionalBranch, Switch, Return, Throw, Prefix }

/// <summary>
/// 一条 IL 指令的编码。Implied 是短形式里写在助记符中的操作数（ldarg.2 的 2、ldc.i4.m1 的 -1）；
/// Canonical 是不带短形式后缀的助记符，同一个 Canonical 的各形式语义相同。
/// </summary>
public sealed record OpcodeInfo(string Name, ushort Code, OperandKind Operand, FlowKind Flow, string Canonical, int? Implied)
{
    /// <summary>编码占的字节数：单字节，或以 0xFE 开头的双字节。</summary>
    public int Size => Code > 0xFF ? 2 : 1;
}

/// <summary>
/// IL 指令表。出处：ECMA-335 第 III 部分各指令的编码，以及第 VI 部分附录 C 的操作码表。
/// 每行：编码、助记符、内联操作数、去向。
/// </summary>
public static class Opcodes
{
    private const string Table = """
        00 nop - n|01 break - n|02 ldarg.0 - n|03 ldarg.1 - n|04 ldarg.2 - n|05 ldarg.3 - n|06 ldloc.0 - n|07 ldloc.1 - n
        08 ldloc.2 - n|09 ldloc.3 - n|0A stloc.0 - n|0B stloc.1 - n|0C stloc.2 - n|0D stloc.3 - n|0E ldarg.s v8 n|0F ldarga.s v8 n
        10 starg.s v8 n|11 ldloc.s v8 n|12 ldloca.s v8 n|13 stloc.s v8 n|14 ldnull - n|15 ldc.i4.m1 - n|16 ldc.i4.0 - n|17 ldc.i4.1 - n
        18 ldc.i4.2 - n|19 ldc.i4.3 - n|1A ldc.i4.4 - n|1B ldc.i4.5 - n|1C ldc.i4.6 - n|1D ldc.i4.7 - n|1E ldc.i4.8 - n|1F ldc.i4.s i8 n
        20 ldc.i4 i32 n|21 ldc.i8 i64 n|22 ldc.r4 r32 n|23 ldc.r8 r64 n|25 dup - n|26 pop - n|27 jmp method r|28 call method n
        29 calli sig n|2A ret - r|2B br.s b8 b|2C brfalse.s b8 c|2D brtrue.s b8 c|2E beq.s b8 c|2F bge.s b8 c|30 bgt.s b8 c
        31 ble.s b8 c|32 blt.s b8 c|33 bne.un.s b8 c|34 bge.un.s b8 c|35 bgt.un.s b8 c|36 ble.un.s b8 c|37 blt.un.s b8 c|38 br b32 b
        39 brfalse b32 c|3A brtrue b32 c|3B beq b32 c|3C bge b32 c|3D bgt b32 c|3E ble b32 c|3F blt b32 c|40 bne.un b32 c
        41 bge.un b32 c|42 bgt.un b32 c|43 ble.un b32 c|44 blt.un b32 c|45 switch switch s|46 ldind.i1 - n|47 ldind.u1 - n|48 ldind.i2 - n
        49 ldind.u2 - n|4A ldind.i4 - n|4B ldind.u4 - n|4C ldind.i8 - n|4D ldind.i - n|4E ldind.r4 - n|4F ldind.r8 - n|50 ldind.ref - n
        51 stind.ref - n|52 stind.i1 - n|53 stind.i2 - n|54 stind.i4 - n|55 stind.i8 - n|56 stind.r4 - n|57 stind.r8 - n|58 add - n
        59 sub - n|5A mul - n|5B div - n|5C div.un - n|5D rem - n|5E rem.un - n|5F and - n|60 or - n
        61 xor - n|62 shl - n|63 shr - n|64 shr.un - n|65 neg - n|66 not - n|67 conv.i1 - n|68 conv.i2 - n
        69 conv.i4 - n|6A conv.i8 - n|6B conv.r4 - n|6C conv.r8 - n|6D conv.u4 - n|6E conv.u8 - n|6F callvirt method n|70 cpobj type n
        71 ldobj type n|72 ldstr string n|73 newobj method n|74 castclass type n|75 isinst type n|76 conv.r.un - n|79 unbox type n|7A throw - t
        7B ldfld field n|7C ldflda field n|7D stfld field n|7E ldsfld field n|7F ldsflda field n|80 stsfld field n|81 stobj type n|82 conv.ovf.i1.un - n
        83 conv.ovf.i2.un - n|84 conv.ovf.i4.un - n|85 conv.ovf.i8.un - n|86 conv.ovf.u1.un - n|87 conv.ovf.u2.un - n|88 conv.ovf.u4.un - n|89 conv.ovf.u8.un - n|8A conv.ovf.i.un - n
        8B conv.ovf.u.un - n|8C box type n|8D newarr type n|8E ldlen - n|8F ldelema type n|90 ldelem.i1 - n|91 ldelem.u1 - n|92 ldelem.i2 - n
        93 ldelem.u2 - n|94 ldelem.i4 - n|95 ldelem.u4 - n|96 ldelem.i8 - n|97 ldelem.i - n|98 ldelem.r4 - n|99 ldelem.r8 - n|9A ldelem.ref - n
        9B stelem.i - n|9C stelem.i1 - n|9D stelem.i2 - n|9E stelem.i4 - n|9F stelem.i8 - n|A0 stelem.r4 - n|A1 stelem.r8 - n|A2 stelem.ref - n
        A3 ldelem type n|A4 stelem type n|A5 unbox.any type n|B3 conv.ovf.i1 - n|B4 conv.ovf.u1 - n|B5 conv.ovf.i2 - n|B6 conv.ovf.u2 - n|B7 conv.ovf.i4 - n
        B8 conv.ovf.u4 - n|B9 conv.ovf.i8 - n|BA conv.ovf.u8 - n|C2 refanyval type n|C3 ckfinite - n|C6 mkrefany type n|D0 ldtoken token n|D1 conv.u2 - n
        D2 conv.u1 - n|D3 conv.i - n|D4 conv.ovf.i - n|D5 conv.ovf.u - n|D6 add.ovf - n|D7 add.ovf.un - n|D8 mul.ovf - n|D9 mul.ovf.un - n
        DA sub.ovf - n|DB sub.ovf.un - n|DC endfinally - r|DD leave b32 b|DE leave.s b8 b|DF stind.i - n|E0 conv.u - n
        FE00 arglist - n|FE01 ceq - n|FE02 cgt - n|FE03 cgt.un - n|FE04 clt - n|FE05 clt.un - n|FE06 ldftn method n|FE07 ldvirtftn method n
        FE09 ldarg v16 n|FE0A ldarga v16 n|FE0B starg v16 n|FE0C ldloc v16 n|FE0D ldloca v16 n|FE0E stloc v16 n|FE0F localloc - n|FE11 endfilter - r
        FE12 unaligned. i8 p|FE13 volatile. - p|FE14 tail. - p|FE15 initobj type n|FE16 constrained. type p|FE17 cpblk - n|FE18 initblk - n|FE19 no. i8 p
        FE1A rethrow - t|FE1C sizeof type n|FE1D refanytype - n|FE1E readonly. - p
        """;

    private static readonly FrozenDictionary<ushort, OpcodeInfo> byCode = Parse().ToFrozenDictionary(o => o.Code);

    public static IEnumerable<OpcodeInfo> All => byCode.Values;

    /// <summary>按编码查指令；双字节指令的编码是 0xFE00 加第二个字节。</summary>
    public static OpcodeInfo? Find(ushort code) => byCode.GetValueOrDefault(code);

    private static IEnumerable<OpcodeInfo> Parse()
    {
        foreach (string item in Table.Split(['|', '\n'], StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
        {
            string[] field = item.Split(' ');
            var operand = field[2] switch
            {
                "-" => OperandKind.None, "i8" => OperandKind.Int8, "i32" => OperandKind.Int32, "i64" => OperandKind.Int64,
                "r32" => OperandKind.Float32, "r64" => OperandKind.Float64, "v8" => OperandKind.Variable8, "v16" => OperandKind.Variable16,
                "b8" => OperandKind.Branch8, "b32" => OperandKind.Branch32, "switch" => OperandKind.Switch, "method" => OperandKind.Method,
                "field" => OperandKind.Field, "type" => OperandKind.Type, "string" => OperandKind.String, "sig" => OperandKind.Signature,
                "token" => OperandKind.Token,
                _ => throw new InvalidOperationException($"指令表里的操作数种类无效：{item}"),
            };
            var flow = field[3] switch
            {
                "n" => FlowKind.Next, "b" => FlowKind.Branch, "c" => FlowKind.ConditionalBranch, "s" => FlowKind.Switch,
                "r" => FlowKind.Return, "t" => FlowKind.Throw, "p" => FlowKind.Prefix,
                _ => throw new InvalidOperationException($"指令表里的去向无效：{item}"),
            };
            string name = field[1], canonical = name;
            int? implied = null;
            // 短形式：ldarg.0 … ldarg.3、ldloc.N、stloc.N、ldc.i4.N、ldc.i4.m1，以及带 .s 后缀的各形式。
            int dot = name.LastIndexOf('.');
            if (dot > 0 && operand == OperandKind.None && name[..dot] is "ldarg" or "ldloc" or "stloc" or "ldc.i4"
                && name[(dot + 1)..] is { } tail && (tail == "m1" || (tail.Length == 1 && char.IsAsciiDigit(tail[0]))))
            {
                canonical = name[..dot];
                implied = tail == "m1" ? -1 : tail[0] - '0';
            }
            else if (name.EndsWith(".s", StringComparison.Ordinal))
                canonical = name[..^2];
            yield return new OpcodeInfo(name, Convert.ToUInt16(field[0], 16), operand, flow, canonical, implied);
        }
    }
}
