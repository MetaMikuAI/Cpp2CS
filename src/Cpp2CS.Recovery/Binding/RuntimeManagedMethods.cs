using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Model;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Binding;

/// <summary>运行时操作的托管写法：位置提供类型实参，元数据提供唯一的方法定义。</summary>
public static class RuntimeManagedMethods
{
    public static Outcome<ImmutableArray<TypeRef>> TypeArguments(QueryContext context, ClassifiedCall call,
        ManagedLocationQuery locations, RuntimeManagedMethod registration)
    {
        var arguments = ImmutableArray.CreateBuilder<TypeRef>();
        foreach (var source in registration.TypeArguments)
        {
            if (source.Source != RuntimeMethodTypeSource.ReferenceLocationElement)
                throw new InvalidOperationException("未登记的运行时方法类型实参来源。");
            if (call.Inputs?.GetValueOrDefault(source.Input)?.Source is not TermSource pointer)
                return No("位置实参没有完整绑定。");
            // 用一次完整指针槽访问查询声明位置；保留地址、位置种类和原有内存版本。
            var located = context.Get(locations, new(pointer.Term, context.Snapshot.AddressWidth));
            if (!located.IsSuccess) return No("位置查询失败。", located.Why);
            if (located.Value == ManagedLocationQuery.Pending)
                return Outcome<ImmutableArray<TypeRef>>.Failure(new("runtime.managed-method.pending", "位置类型尚未收敛。"));
            var views = located.Value.Views.Where(v => v.Offset == 0 && v.Kind is ManagedLocationKind.InstanceField
                or ManagedLocationKind.StaticField or ManagedLocationKind.ArrayElement or ManagedLocationKind.FrameLocal or ManagedLocationKind.Indirect).ToArray();
            if (views is not [var view] || !ManagedTypes.IsReferenceType(view.Type))
                return No("实参不是唯一引用类型托管位置的地址。", located.Value.Why);
            arguments.Add(view.Type);
        }
        return Outcome<ImmutableArray<TypeRef>>.Success(arguments.ToImmutable());
        static Outcome<ImmutableArray<TypeRef>> No(string message, Cpp2CS.Native.Terms.Reason? cause = null) =>
            Outcome<ImmutableArray<TypeRef>>.Failure(new("runtime.managed-method.location", message, cause));
    }

    public static TypeRef? Type(RuntimeManagedType shape, IReadOnlyList<TypeRef> arguments, ProgramModel? model)
    {
        TypeRef? element = shape.MethodParameter is { } index ? arguments.ElementAtOrDefault(index)
            : model?.Types.Where(t => t.FullName == shape.Name).ToArray() is [var definition]
                ? new DefinitionRef(definition, []) : null;
        return element is null ? null : shape.ByRef ? new ByRefRef(element) : element;
    }

    public static MethodRef? Find(ProgramModel model, RuntimeManagedMethod registration, ImmutableArray<TypeRef> arguments)
    {
        var owners = model.Types.Where(t => t.FullName == registration.DeclaringType).ToArray();
        if (owners is not [var owner]) return null;
        bool Matches(TypeRef type, RuntimeManagedType shape)
        {
            if (shape.ByRef)
            {
                if (type is not ByRefRef byref) return false;
                type = byref.Element;
            }
            return shape.MethodParameter is { } index
                ? type is GenericParameterRef { IsMethod: true } parameter && parameter.Position == index
                : type is DefinitionRef definition && definition.Definition.FullName == shape.Name
                    && definition.Definition.Assembly == owner.Assembly;
        }
        var methods = owner.Methods.Where(m => m.IsStatic && m.Name == registration.Name
            && m.GenericParameters.Count == registration.TypeArguments.Length && m.Parameters.Count == registration.Parameters.Length
            && m.Parameters.Select((p, i) => Matches(p.Type, registration.Parameters[i])).All(v => v)
            && Matches(m.ReturnType, registration.Result)).ToArray();
        return methods is [var method] ? new(method, [], arguments) : null;
    }
}
