using System.Collections.Immutable;
using System.Text.Json;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Targets.X64.Abi;

namespace Cpp2CS.Tests;

internal static class AbiChecks
{
    public const string Command = "abi";
    private static readonly CType I = new CInteger(64), F = new CFloat(64), S = new CFloat(32);
    private static CAggregate A(int size, int align, params CField[] fields) => new(size, align, [.. fields]);
    private static readonly CType Pair = A(16, 8, new CField(0, I), new CField(8, I));
    private static readonly CType Mixed = A(16, 8, new CField(0, I), new CField(8, F));
    private static readonly CType Large = A(24, 8, new CField(0, new CArray(I, 3)));
    private static readonly CType Hfa = A(24, 8, new CField(0, new CArray(F, 3)));
    private sealed record Rule(string Basis, CType[] Args, CType Result, string Expected);
    private static CType[] Repeat(CType t, int n, params CType[] tail) => [.. Enumerable.Repeat(t, n), .. tail];
    private static string P(AbiPiece p) => $"{p.ValueOffset}:{p.Length}:{p.Slot.Kind}:{p.Slot.Position}:{p.SlotOffset}";
    private static string V(AbiValue v) => v.CopyAddress is { } address ? "&" + P(address) : string.Join(',', v.Pieces.Select(P));
    private static string R(AbiReturn r) => r.BufferAddress is { } address ? "&" + P(address)
        + (r.ReturnedAddress is { } echo ? "=" + P(echo) : "") : string.Join(',', r.Pieces.Select(P));
    private static string Integer(int index, int length = 8, int offset = 0) => $"{offset}:{length}:Integer:{index}:0";
    private static string Float(int index, int length = 8, int offset = 0) => $"{offset}:{length}:Floating:{index}:0";
    private static string Stack(int offset, int length) => $"0:{length}:ArgumentArea:{offset}:0";

    public static int Run()
    {
        var a = new Assertions();
        Rules(a, new Aapcs64(), ArmRules(), "AAPCS64");
        Rules(a, new SysV(), SysVRules(), "SysV");
        foreach (IAbiClassifier abi in new IAbiClassifier[] { new Aapcs64(), new SysV() })
        {
            foreach (var invalid in new CSignature[] {
                new([new CVoid()], new CVoid()), new([new CFloat(128)], new CVoid()),
                new([new CInteger(24)], new CVoid()), new([new CPointer(32)], new CVoid()),
                new([new CArray(I,2)], new CVoid()), new([A(8,8,new CField(1,I))], new CVoid()),
                new([A(16,8,new CField(0,I),new CField(4,I))], new CVoid()), new([],new CVoid(),true) })
                a.True(abi.Classify(invalid) is { Success: false, Problem.Length: > 0 }, "不支持的输入给出原因");
            var narrow = abi.Classify(new([new CInteger(8)],new CInteger(8))).Assignment!;
            a.True(narrow.Parameters[0].UnusedBits == UnusedBitRule.Unspecified
                && narrow.Return.UnusedBits == UnusedBitRule.Unspecified, "窄值外的高位未规定");
        }
        a.True(new Aapcs64().Classify(new([A(16,16,new CField(0,I),new CField(8,I))],new CVoid()))
            is {Success:false,Problem.Length:>0}, "提高聚合对齐而缺少修饰信息时失败");
        Aapcs64Reference.Check(a);
        Evidence(a);
        return a.Finish("ABI 分类");
    }

    // 每条仅比较最后一个实参和返回值；耗尽前缀仍参与分配，避免手写重复预期。
    private static void Rules(Assertions a, IAbiClassifier abi, Rule[] rules, string name)
    {
        foreach (var rule in rules)
        {
            var classified = abi.Classify(new([.. rule.Args], rule.Result));
            a.True(classified.Success, $"{name} {rule.Basis}: {classified.Problem}");
            if (classified.Assignment is not { } result) continue;
            var actual = (result.Parameters.Length == 0 ? "" : V(result.Parameters[^1])) + "/" + R(result.Return) + "/" + result.StackSize;
            a.True(actual == rule.Expected, $"{name} {rule.Basis}: {actual} != {rule.Expected}");
            a.True(result.StackAlignment == 16, name + " 栈区对齐");
        }
        Console.WriteLine($"{name} 规则表：{rules.Length} 条");
    }

    private static Rule[] ArmRules() =>
    [
        new("C.9/6.9 整数", [I], I, Integer(0)+"/"+Integer(0)+"/0"),
        new("C.9 窄整数", [new CInteger(8)],new CVoid(),Integer(0,1)+"//0"),
        new("C.9 指针", [new CPointer(64)],new CVoid(),Integer(0)+"//0"),
        new("C.1/6.9 浮点", [S],S,Float(0,4)+"/"+Float(0,4)+"/0"),
        new("C.12 小聚合", [Pair],Pair,Integer(0)+","+Integer(1,8,8)+"/"+Integer(0)+","+Integer(1,8,8)+"/0"),
        new("C.2 HFA",[Hfa],Hfa,Float(0)+","+Float(1,8,8)+","+Float(2,8,16)+"/"+Float(0)+","+Float(1,8,8)+","+Float(2,8,16)+"/0"),
        new("B.4/6.9 大聚合",[Large],Large,"&"+Integer(0)+"/&0:8:IndirectResult:0:0/0"),
        new("C.13–17 整数耗尽",Repeat(I,8,I),new CVoid(),Stack(0,8)+"//16"),
        new("C.5–6 浮点耗尽",Repeat(F,8,S),new CVoid(),Stack(0,4)+"//16"),
        new("C.12–13 整体回退",Repeat(I,7,Pair),new CVoid(),Stack(0,16)+"//16"),
        new("C.13 回退后关闭整数池",Repeat(I,7,Pair,I),new CVoid(),Stack(16,8)+"//32"),
        new("C.3 HFA 回退",Repeat(F,7,Hfa),new CVoid(),Stack(0,24)+"//32"),
        new("C.3 后续浮点入栈",Repeat(F,7,Hfa,F),new CVoid(),Stack(24,8)+"//32"),
        new("C.3 不消耗整数",Repeat(F,7,Hfa,I),new CVoid(),Integer(0)+"//32"),
        new("B.4 副本地址入栈",Repeat(I,8,Large),new CVoid(),"&"+Stack(0,8)+"//16"),
        new("C.10 偶数槽",[I,new CInteger(128)],new CVoid(),Integer(2)+","+Integer(3,8,8)+"//0"),
        new("C.16 栈对齐",Repeat(I,9,new CInteger(128)),new CVoid(),Stack(16,16)+"//32"),
        new("5.10.5 嵌套 HFA",[A(16,8,new CField(0,A(16,8,new CField(0,F),new CField(8,F))))],new CVoid(),Float(0)+","+Float(1,8,8)+"//0"),
        new("5.10.5 数组 HFA",[A(12,4,new CField(0,new CArray(S,3)))],new CVoid(),Float(0,4)+","+Float(1,4,4)+","+Float(2,4,8)+"//0"),
        new("C.12 填充",[A(16,8,new CField(0,new CInteger(8)),new CField(8,I))],new CVoid(),Integer(0)+","+Integer(1,8,8)+"//0"),
        new("语言映射 零大小空聚合",[A(0,1)],A(0,1),"//0"),
        new("语言映射 单字节空聚合",[A(1,1)],A(1,1),Integer(0,1)+"/"+Integer(0,1)+"/0"),
        new("6.9 间接返回不占整数池",[I],Large,Integer(0)+"/&0:8:IndirectResult:0:0/0"),
        new("6.9 void",[],new CVoid(),"//0"),
        new("C.12 混合聚合",[Mixed],new CVoid(),Integer(0)+","+Integer(1,8,8)+"//0"),
    ];

    private static Rule[] SysVRules() =>
    [
        new("3.2.3 INTEGER",[I],I,Integer(0)+"/"+Integer(0)+"/0"),
        new("3.2.3 窄整数",[new CInteger(8)],new CVoid(),Integer(0,1)+"//0"),
        new("3.2.3 指针",[new CPointer(64)],new CVoid(),Integer(0)+"//0"),
        new("3.2.3 SSE",[S],S,Float(0,4)+"/"+Float(0,4)+"/0"),
        new("3.2.3 两八字节",[Pair],Pair,Integer(0)+","+Integer(1,8,8)+"/"+Integer(0)+","+Integer(1,8,8)+"/0"),
        new("3.2.3 混合类",[Mixed],Mixed,Integer(0)+","+Float(0,8,8)+"/"+Integer(0)+","+Float(0,8,8)+"/0"),
        new("3.2.3 合并 INTEGER 优先",[A(8,4,new CField(0,S),new CField(4,new CInteger(32)))],new CVoid(),Integer(0)+"//0"),
        new("3.2.3 MEMORY 返回",[Large],Large,Stack(0,24)+"/&"+Integer(0)+"="+Integer(0)+"/32"),
        new("3.2.3 大浮点聚合入栈",[Hfa],new CVoid(),Stack(0,24)+"//32"),
        new("3.2.3 整数耗尽",Repeat(I,6,I),new CVoid(),Stack(0,8)+"//16"),
        new("3.2.3 SSE 耗尽",Repeat(F,8,S),new CVoid(),Stack(0,4)+"//16"),
        new("3.2.3 回滚整个实参",Repeat(I,5,Pair),new CVoid(),Stack(0,16)+"//16"),
        new("3.2.3 回滚后余槽可用",Repeat(I,5,Pair,I),new CVoid(),Integer(5)+"//16"),
        new("3.2.3 混合回退不占浮点槽",Repeat(I,6,Mixed,F),new CVoid(),Float(0)+"//16"),
        new("3.2.3 浮点不足不占整数槽",Repeat(F,8,Mixed,I),new CVoid(),Integer(0)+"//16"),
        new("3.2.3 栈 16 对齐",Repeat(I,7,new CInteger(128)),new CVoid(),Stack(16,16)+"//32"),
        new("3.2.3 整数对无需偶数槽",[I,new CInteger(128)],new CVoid(),Integer(1)+","+Integer(2,8,8)+"//0"),
        new("3.2.3 未对齐字段",[A(9,1,new CField(0,new CInteger(8)),new CField(1,F))],new CVoid(),Stack(0,9)+"//16"),
        new("3.2.3 嵌套",[A(16,8,new CField(0,Mixed))],new CVoid(),Integer(0)+","+Float(0,8,8)+"//0"),
        new("3.2.3 数组",[A(12,4,new CField(0,new CArray(S,3)))],new CVoid(),Float(0)+","+Float(1,4,8)+"//0"),
        new("3.2.3 填充 NO_CLASS",[A(16,8,new CField(0,new CInteger(8)))],new CVoid(),Integer(0)+"//0"),
        new("3.2.3 空聚合",[A(0,1)],A(0,1),"//0"),
        new("3.2.3 空对象无成员",[A(1,1)],A(1,1),"//0"),
        new("3.2.3 间接返回占整数零槽",[I],Large,Integer(1)+"/&"+Integer(0)+"="+Integer(0)+"/0"),
        new("3.2.3 void",[],new CVoid(),"//0"),
    ];

    private static void Evidence(Assertions a)
    {
        var path = Path.Combine(ArchitectureChecks.FindRoot(), "tests", "Cpp2CS.Tests", "AbiEvidence", "sysv.json");
        using var document = JsonDocument.Parse(File.ReadAllText(path));
        var root = document.RootElement;
        var descriptions = root.GetProperty("types").EnumerateArray().ToArray();
        CType Type(int id)
        {
            var t = descriptions[id];
            var size = t.GetProperty("size").GetInt32();
            return t.GetProperty("kind").GetString() switch
            {
                "integer" => new CInteger(size * 8), "pointer" => new CPointer(size * 8), "float" => new CFloat(size * 8),
                _ => A(size,t.GetProperty("alignment").GetInt32(), t.GetProperty("fields").EnumerateArray().Select(f =>
                {
                    CType member = Type(f.GetProperty("type").GetInt32());
                    var count = f.GetProperty("count").GetInt32();
                    return new CField(f.GetProperty("offset").GetInt32(), count == 1 ? member : new CArray(member,count));
                }).ToArray()),
            };
        }
        var cases = root.GetProperty("cases").EnumerateArray().ToArray();
        a.True(cases.Length >= 300, "真实签名不少于 300");
        a.True(cases.Select(c => c.GetProperty("parameters").GetRawText()+"/"+c.GetProperty("result").GetRawText())
            .Distinct().Count() >= 300, "去重后真实签名不少于 300");
        var bytes = 0;
        for (var index = 0; index < cases.Length; index++)
        {
            var c = cases[index];
            var signature = new CSignature([.. c.GetProperty("parameters").EnumerateArray().Select(p => Type(p.GetInt32()))],Type(c.GetProperty("result").GetInt32()));
            var classified = new SysV().Classify(signature);
            a.True(classified.Success, $"证据 {index} 支持：{classified.Problem}");
            if (classified.Assignment is not { } assigned) continue;
            var snapshots = Convert.FromBase64String(c.GetProperty("snapshots").GetString()!);
            int Location(AbiPiece p, int valueByte, bool returned) => p.Slot.Kind switch
            {
                SlotKind.Integer => (int)p.Slot.Position*8+p.SlotOffset+valueByte-p.ValueOffset,
                SlotKind.Floating => (returned ? 16 : 48)+(int)p.Slot.Position*16+p.SlotOffset+valueByte-p.ValueOffset,
                SlotKind.ArgumentArea => 176+(int)p.Slot.Position+p.SlotOffset+valueByte-p.ValueOffset,
                _ => throw new InvalidOperationException("证据中未知位置"),
            };
            void Compare(JsonElement observations, CType type, ImmutableArray<AbiPiece> pieces, int tokenBase, bool returned, bool indirect)
            {
                var expectedBytes = CTypes.Leaves(type).SelectMany(f => Enumerable.Range(f.Offset,f.Type.Size)).ToArray();
                a.True(observations.EnumerateArray().Select(o=>o[0].GetInt32()).SequenceEqual(expectedBytes),
                    $"证据 {index} 必须覆盖全部字段字节");
                foreach (var observation in observations.EnumerateArray())
                {
                    var valueByte = observation[0].GetInt32();
                    var piece = pieces.FirstOrDefault(p => p.ValueOffset <= valueByte && valueByte < p.ValueOffset+p.Length);
                    a.True(indirect || piece is not null, $"证据 {index} 字节 {valueByte} 缺少片段");
                    if (!indirect && piece is null) continue;
                    var location = indirect ? 48+valueByte : Location(piece!,valueByte,returned);
                    a.True(observation[1].EnumerateArray().Any(v => v.GetInt32() == location), $"证据 {index} {(returned ? "返回" : "参数")} {tokenBase/1024} 字节 {valueByte} 位置 {location}");
                    for (var trial = 0; trial < 4; trial++)
                    {
                        var marker = (byte)(unchecked((uint)(tokenBase+valueByte+1)*2654435761u) >> (trial*8));
                        a.True(snapshots[trial*2529+(returned ? 2224 : 0)+location] == marker, $"证据 {index} 原始字节不符");
                    }
                    bytes++;
                }
            }
            var arguments = c.GetProperty("arguments").EnumerateArray().ToArray();
            for (var j = 0; j < arguments.Length; j++) Compare(arguments[j],signature.Parameters[j],assigned.Parameters[j].Pieces,j*1024,false,false);
            Compare(c.GetProperty("returns"),signature.ReturnType,assigned.Return.Pieces,32768,true,assigned.Return.BufferAddress is not null);
            if (assigned.Return.BufferAddress is not null)
                a.True(c.GetProperty("echo").GetBoolean() && assigned.Return.ReturnedAddress?.Slot == new AbstractSlot(SlotKind.Integer), $"证据 {index} 返回缓冲区地址回传");
        }
        Console.WriteLine($"SysV gcc 证据：{cases.Length} 个签名，{bytes} 个字段字节，四轮快照");
    }
}
