using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Tools.ForwardCheck;

internal sealed partial class SrmMetadata
{
    /// <summary>
    /// IL 对照展开调用时用的被调方法：真实方法体按目录展开的效果图，建在给定的项池里。
    /// 只给非泛型的方法定义。调用的含义不全在方法体里的方法不给：没有 IL 方法体的（内部调用、P/Invoke、由运行时实现、抽象方法），
    /// 以及同步方法（调用还带加锁）。
    /// </summary>
    public Func<EntityRef, int, FlowGraph<TemplateEffect>?> Callees(TermPool terms, int pointerBits) => (method, graph) =>
    {
        var model = Facts.Model;
        if (method.Kind != EntityKind.Method || method.Key < 0 || method.Key >= model.Methods.Count) return null;
        var definition = model.Methods[(int)method.Key];
        const MethodImplAttributes outside = MethodImplAttributes.CodeTypeMask | MethodImplAttributes.ManagedMask
            | MethodImplAttributes.InternalCall | MethodImplAttributes.Synchronized;
        if ((definition.ImplFlags & outside) != 0) return null;
        if (definition.GenericParameters.Count > 0 || model.Types[definition.Owner].GenericParameters.Count > 0) return null;
        var (module, _) = Definition(definition.Owner);
        int token = (int)definition.Token;
        if (module.Md.GetMethodDefinition((MethodDefinitionHandle)MetadataTokens.EntityHandle(token)).RelativeVirtualAddress == 0) return null;
        return IlExpander.Expand(Body(module, token), Facts, Tokens(module, method), terms, graph, pointerBits).Graph;
    };
}
