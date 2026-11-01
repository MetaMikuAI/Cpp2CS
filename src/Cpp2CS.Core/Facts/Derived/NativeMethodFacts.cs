using Cpp2CS.Ir;
using Cpp2CS.Idioms;
using Cpp2CS.Machine.Lifting;

namespace Cpp2CS.Facts.Derived;

/// <summary>原生函数形状与身份的派生事实；缓存仅在单个恢复器实例内复用。</summary>
internal sealed partial class NativeMethodFacts(ProgramFacts facts, FunctionLifter lifter, IdiomRewriter rewriter)
{
    internal readonly Dictionary<(DefinitionRef, ulong), MethodDef?> forwarding = new();

    /// <summary>
    /// type 自己的无参构造函数是否只把 this 转给 target（基类的构造函数）：原生代码中只有这一个调用（尾调用或调用后返回），
    /// 首个实参是入口的 x0，没有分支、没有其他调用、没有栈帧之外的写入。clang 把这样的构造函数内联后，调用者分配对象后直接调用基类构造。
    /// </summary>
    internal MethodDef? ForwardingConstructor(DefinitionRef type, ulong target)
    {
        if (forwarding.TryGetValue((type, target), out var known)) return known;
        MethodDef? result = null;
        if (type.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 0).ToArray() is [var constructor]
            && ConstructorEntry(new(constructor, type.Arguments, [])) is > 0 and var entry
            && facts.Code.RegionOf(entry) == CodeRegion.Managed && lifter.Lift(entry) is { Succeeded: true } lifted)
        {
            var statements = lifted.Function.Blocks.SelectMany(b => b.Statements).ToArray();
            var calls = statements.OfType<Call>().ToArray();
            static bool OnFrame(Expr address) => address is FrameAddress || address is Binary { Op: BinOp.Add, Left: FrameAddress, Right: Const };
            if (calls is [{ Target: Const called, Kind: CallKind.Tail or CallKind.Direct } call] && called.Value == target
                && call.Arguments.FirstOrDefault() is Use { Variable: { Version: 0 } self } && self.Storage == Storage.Gpr(0)
                && statements.All(s => s is Define or Phi or Nop or Jump or Return or Call || s is Store store && OnFrame(store.Target)))
                result = constructor;
        }
        return forwarding[(type, target)] = result;
    }

    internal ILookup<MethodDef, CodeEntry>? constructorEntries;

    internal ulong ConstructorEntry(MethodRef method)
    {
        if (method.Method.Address != 0) return method.Method.Address;
        constructorEntries ??= facts.Registrations.Entries.Where(e => e.Kind == EntryKind.GenericMethod && e.Method?.Method.Name == ".ctor")
            .ToLookup(e => e.Method!.Method);
        var entries = constructorEntries[method.Method].ToArray();
        if (entries.FirstOrDefault(e => e.Method!.Equals(method)) is { } exact) return exact.Address;
        if (!method.TypeArguments.Concat(method.MethodArguments).All(ManagedTypes.IsReferenceType)) return 0;
        var shared = entries.Where(e => e.Method!.TypeArguments.Concat(e.Method.MethodArguments)
            .All(t => ManagedTypes.IsReferenceType(t) && !FieldLayouts.IsFullyShared(t))).Select(e => e.Address).Distinct().ToArray();
        return shared is [var address] ? address : 0;
    }

}
