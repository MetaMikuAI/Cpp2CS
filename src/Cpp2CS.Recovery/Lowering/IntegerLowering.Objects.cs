using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    /// <summary>一次对象分配；与紧随其后的构造函数调用合成 newobj，对象的值是构造完成后的局部。</summary>
    private sealed class ObjectDefinition(TypeRef type, Term result)
    {
        public TypeRef Type { get; } = type;
        public Term Result { get; } = result;
        public LocalValue? Local { get; set; }
    }
    private readonly Dictionary<CallIdentity, ObjectDefinition> allocations = [];
    private readonly Dictionary<Term, ObjectDefinition> objects = [];
    private readonly Dictionary<CallIdentity, ObjectDefinition> constructions = [];
    private ObjectDefinition? constructing;
    private ValueNamingQuery? valueNames;

    /// <summary>分配的类取自已命名的元数据实体；说不出类的分配是洞。</summary>
    private void PrepareAllocation(Call call, ClassifiedCall c)
    {
        var input = c.Operation!.Inputs.FirstOrDefault(i => i.Kind == RuntimeValueKind.Class);
        if (valueNames is null || input is null || c.Inputs?.GetValueOrDefault(input.Name)?.Source is not TermSource klass
            || c.Result?.Source is not TermSource result)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "对象分配的类或结果没有绑定", code: "lowering.Allocation.Binding"); return; }
        var named = context.Get(valueNames, klass.Term);
        if (!named.IsSuccess || named.Value.Name is not EntityName { Entity: ClassEntity { Type: var type } } || !ManagedTypes.IsReferenceType(type))
        {
            Fail<object>(LoweringFailureKind.RuntimeCall, "对象分配的类没有实体凭据", named.IsSuccess ? named.Value.Why : named.Why, "lowering.Allocation.Class");
            return;
        }
        var definition = new ObjectDefinition(type, result.Term);
        allocations.Add(call.Identity, definition);
        objects[result.Term] = definition;
    }

    /// <summary>
    /// 分配之后的第一个事件必须是对这个对象的同类构造函数调用。IL 的 newobj 在实参求值之后才初始化类、分配并构造；
    /// 其间若有别的事件或托管内存访问，它们与类初始化的次序就和原生代码不同。帧访问与运行时私有数据的读取不受影响。
    /// </summary>
    private void PairConstructions()
    {
        foreach (var b in function.Blocks)
            for (int i = 0; i < b.Statements.Length; i++)
            {
                if (b.Statements[i] is not Call call || !allocations.TryGetValue(call.Identity, out var definition)) continue;
                position = call.Trace?.NativeAddress ?? b.Trace?.NativeAddress ?? 0;
                int j = i + 1;
                while (j < b.Statements.Length && b.Statements[j] is not Call && PrivateAccess(b.Statements[j])) j++;
                if (j < b.Statements.Length && b.Statements[j] is Call next && callDefinitions.TryGetValue(next.Identity, out var constructor)
                    && !constructor.Virtual && constructor.Receiver is null && constructor.Method.Method is { Name: ".ctor", IsStatic: false }
                    && Equals(constructor.Method.DeclaringType, definition.Type) && constructor.Binding.This is { } self
                    && BoundTerm(self.Source, new(b.Identity, j)) is { } receiver
                    && context.Get(state.Resolve, receiver) is { IsSuccess: true } actual
                    && context.Get(state.Resolve, definition.Result) is { IsSuccess: true } expected && actual.Value == expected.Value)
                {
                    constructions.Add(next.Identity, definition);
                    definition.Local = new(new(nextLocal++), definition.Type, types.PointerSize * 8);
                    continue;
                }
                Fail<object>(LoweringFailureKind.RuntimeCall, "对象分配之后的第一个事件不是对它的同类构造函数调用", code: "lowering.Allocation.Constructor");
                return;
            }
    }

    private bool PrivateAccess(Statement statement)
    {
        var (address, width, read) = statement switch
        {
            MemoryRead r => (r.Address, r.Width, true),
            MemoryWrite w => (w.Address, w.Width, false),
            _ => (null, 0, false),
        };
        if (address is null) return false;
        var resolved = context.Get(state.Resolve, address);
        if (!resolved.IsSuccess) return false;
        var location = context.Get(state.Locations, new(resolved.Value, width));
        if (!location.IsSuccess) return false;
        if (location.Value.Region == Region.Frame) return true;
        if (!read || locations is null) return false;
        var managed = context.Get(locations, new(address, width));
        return managed.IsSuccess && managed.Value.Kind == ManagedLocationKind.NotManaged;
    }

    private ManagedValue? ObjectValue(ObjectDefinition definition) =>
        definition == constructing ? Fail<ManagedValue>(LoweringFailureKind.RuntimeCall, "对象在自己的构造函数实参里被使用", code: "lowering.Allocation.Escape")
        : definition.Local ?? Fail<ManagedValue>(LoweringFailureKind.RuntimeCall, "对象分配没有配对的构造函数调用", code: "lowering.Allocation.Constructor");

    /// <summary>
    /// 引用类型的实例构造函数恰有一次对 this 的基类或本类构造函数调用（base(...) 或 this(...)）。
    /// 找不到说明那次调用被内联或省略，没有逆变换的证明。
    /// </summary>
    private bool ConstructorChained(IEnumerable<ManagedBlock> blocks)
    {
        var owner = method.DeclaringType;
        var parent = owner is DefinitionRef d ? d.Definition.BaseType?.Substitute(d.Arguments, []) : null;
        return blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Count(c => !c.Invocation.Virtual
            && c.Invocation.Method.Method is { Name: ".ctor", IsStatic: false } && c.Invocation.Receiver is ArgumentValue { Index: -1 }
            && (Equals(c.Invocation.Method.DeclaringType, owner) || Equals(c.Invocation.Method.DeclaringType, parent))) == 1;
    }
}
