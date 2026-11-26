using System.Collections.Immutable;

namespace Cpp2CS.Spec.Independence;

/// <summary>独立关系里效果的种类（设计 7.5、7.6）。</summary>
public enum EffectClass : byte { Read, Write, Call, NewObject, ClassInitialize, ConditionalThrow, Unnamed }

/// <summary>一行成立的条件。条件只许是语义条件，由内核按事实求值；这里没有控制流形态。</summary>
public enum IndependenceCondition : byte
{
    /// <summary>总是独立。</summary>
    Always,
    /// <summary>两个位置已证明不重叠（别名判定）。</summary>
    LocationsDisjoint,
    /// <summary>两者抛出的异常相同（同种类、同操作数）且去向相同。</summary>
    SameException,
}

/// <summary>
/// 独立关系的一行：两种效果相邻时交换次序不改变可观察行为的条件。Basis 是语义依据，Case 是用到它的语料用例。
/// 表里没有的一对效果不能证明独立。
/// </summary>
public sealed record IndependenceRow(string Id, EffectClass First, EffectClass Second, IndependenceCondition Condition, string Basis, string Case);

/// <summary>
/// 独立关系表（设计 7.6）。表是数据，内核里只有查询。首批只收语料用得到的行；
/// 缺一行只会多洞，多写一行不成立的独立才会写错。
/// </summary>
public static class IndependenceTable
{
    private static readonly ImmutableArray<IndependenceRow> rows =
    [
        new("read-read", EffectClass.Read, EffectClass.Read, IndependenceCondition.Always,
            "读取不是事件（设计 6.1）：两次读取都不改变内存，先后不可观察",
            "checks/ArrayBounds：两次元素读取，前一次的声明越过后一次"),
        new("throw-read", EffectClass.ConditionalThrow, EffectClass.Read, IndependenceCondition.Always,
            "读取不是事件（设计 6.1）；条件抛出成立时读取的结果无人使用，可弃（设计 6.2）",
            "checks/ArrayBounds：后一次访问的越界检查位于前一次访问的检查与读取之间"),
        new("throw-throw", EffectClass.ConditionalThrow, EffectClass.ConditionalThrow, IndependenceCondition.SameException,
            "两个检查同时成立时抛出的是同一种运行时异常，分不出先后；运行时构造的同种异常彼此不可区分（设计 16.2）",
            "checks/ArrayBounds：两次越界检查共用一个只抛出尾"),
        new("read-write", EffectClass.Read, EffectClass.Write, IndependenceCondition.LocationsDisjoint,
            "位置不重叠时写入不改变读取的结果（设计 7.4 的别名判定）；ECMA-335 I.12.6.4：对不同位置的访问互不影响",
            "fields/WriteArray 一类：同一对象上常量偏移不同的两个位置"),
        new("write-write", EffectClass.Write, EffectClass.Write, IndependenceCondition.LocationsDisjoint,
            "位置不重叠时两次写入的结果与次序无关（设计 7.4 的别名判定）",
            "inlining/PushOnce 一类：计数字段与数组元素的两次写入"),
    ];

    public static ImmutableArray<IndependenceRow> Rows => rows;

    /// <summary>查一对效果的行；关系是对称的。没有登记时为空。</summary>
    public static IndependenceRow? Find(EffectClass a, EffectClass b)
    {
        foreach (var row in rows)
            if ((row.First == a && row.Second == b) || (row.First == b && row.Second == a)) return row;
        return null;
    }
}
