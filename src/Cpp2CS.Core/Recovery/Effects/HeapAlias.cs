using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Effects;

/// <summary>
/// 堆字段的别名关系：托管类型安全保证不同字段定义的位置互不重叠，同一字段定义只有在所在类型可能是同一个运行时类型时才可能共享存储。
/// 内存足迹、可用字段事实与内联证明共用这一判定。
/// </summary>
internal static class HeapAlias
{
    /// <summary>两个字段访问可能指向同一存储：同一字段定义，且所在类型可能是同一个运行时类型。</summary>
    public static bool MayShare(FieldRef a, FieldRef b) => ReferenceEquals(a.Field, b.Field) && MaySameType(a.DeclaringType, b.DeclaringType);

    /// <summary>
    /// 两个类型引用可能指同一个运行时类型：相同、含类型形参，或一方是 object 而另一方是引用类型
    /// （取自共享实例的方法体以 object 代替引用类型实参）；同一定义的实例逐个比较实参。
    /// 对象只有一个运行时类型，两个确定不同的实例化（如 List&lt;int&gt; 与 List&lt;float&gt;）不会是同一对象。
    /// </summary>
    public static bool MaySameType(TypeRef x, TypeRef y) => x.Equals(y) || x.ContainsGenericParameter() || y.ContainsGenericParameter()
        || IsObject(x) && ManagedTypes.IsReferenceType(y) || IsObject(y) && ManagedTypes.IsReferenceType(x)
        || x is DefinitionRef dx && y is DefinitionRef dy && ReferenceEquals(dx.Definition, dy.Definition) && dx.Arguments.Count == dy.Arguments.Count
            && dx.Arguments.Zip(dy.Arguments).All(p => MaySameType(p.First, p.Second));

    private static bool IsObject(TypeRef type) => type is DefinitionRef { Definition.FullName: "System.Object" };
}
