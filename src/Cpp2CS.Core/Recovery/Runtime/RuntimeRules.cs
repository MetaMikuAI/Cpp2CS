using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class RuntimeRules
{
    internal static bool PrepareTypeChecks(this RecoveryScope ctx)
    {
        ctx.PrepareExceptionTypeChecks();
        foreach (var call in ctx.blocks.SelectMany(b => b.Statements).OfType<Call>())
            if (call is { Op: { Kind: OpKind.TypeCheck, Operand: DefinitionRef { Definition: { IsValueType: false, IsInterface: false } } }, Arguments: [var argument] }
                && (argument is Use use ? ctx.values.GetValueOrDefault(use.Variable) : argument) is Load { Width: 64, Address: Use obj }
                && ctx.TypeOfValue(obj) is { } type && ManagedTypes.IsReferenceType(type))
            {
                if (argument is Use klass)
                {
                    ctx.State.Runtime.objectClasses[klass.Variable] = obj;
                    ctx.State.Runtime.runtime.Add(klass.Variable);
                }
                ctx.State.Runtime.typeChecks[call] = obj;
                ctx.State.Calls.callBindings.InvalidateTypes();
            }

        return ctx.PrepareSealedChecks() | ctx.State.Runtime.typeChecks.Count > 0;
    }

    internal static bool PrepareSealedChecks(this RecoveryScope ctx)
    {
        var found = false;
        var compares = ctx.blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Compare>().ToArray();
        var uses = ctx.blocks.SelectMany(b => b.Statements).SelectMany(s => s is Phi phi ? phi.Sources.Select(v => new Use(v, v.Width)) : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>()).GroupBy(u => u.Variable).ToDictionary(g => g.Key, g => g.Count());
        foreach (var (variable, value) in ctx.values)
        {
            if (ctx.State.Runtime.runtime.Contains(variable) || value is not Load { Width: 64, Address: Use obj } || ctx.TypeOfValue(obj) is not { } type || !ManagedTypes.IsReferenceType(type))
                continue;
            var sealedCompares = compares.Count(c => c.Cond is Cond.Eq or Cond.Ne && RuntimeRules.SealedOperands(c) is var (klass, _) && klass == variable);
            if (sealedCompares == 0 || uses.GetValueOrDefault(variable) != sealedCompares)
                continue;
            ctx.State.Runtime.objectClasses[variable] = obj;
            ctx.State.Runtime.runtime.Add(variable);
            ctx.State.Calls.callBindings.InvalidateTypes();
            found = true;
        }

        return found;
    }

    /// <summary>比较的两侧是类指针与无派生类型的 Class 符号时返回二者；Nullable 的装箱类型不同。</summary>
    internal static (Variable Klass, DefinitionRef Type)? SealedOperands(Compare c)
    {
        static bool Sealed(Expr e, out DefinitionRef type)
        {
            type = null!;
            if (e is not Symbol { Kind: SymbolKind.Class, Value: DefinitionRef d } || d.Definition.IsInterface || d.Definition.FullName == "System.Nullable"
                || !d.Definition.IsValueType && (d.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) == 0)
                return false;
            type = d;
            return true;
        }

        if (c.Left is Use { Width: 64 } l && Sealed(c.Right, out var right))
            return (l.Variable, right);
        if (c.Right is Use { Width: 64 } r && Sealed(c.Left, out var left))
            return (r.Variable, left);
        return null;
    }

    internal static Definitions IndexDefinitions(this RecoveryScope ctx)
    {
        ctx.analyses.Refresh(ctx.blocks, ctx.State.Exceptions.exceptionPhis);
        return ctx.analyses.Get(Definitions.Analysis);
    }

    /// <summary>运行时引用：值是类、方法等运行时结构（不是托管值）的变量。只能出现在运行时操作的参数中。</summary>
    [Analysis("运行时引用", 40, After = ["帧区域", "异常值"])]
    internal static void MarkRuntime(this RecoveryScope ctx)
    {
        ctx.MarkVtableLoads();
        ctx.MarkGenericVirtualLoads();
        ctx.MarkVirtualDelegateLoads();
        bool changed;
        do
        {
            changed = false;
            foreach (var (variable, value) in ctx.values)
                if (!ctx.State.Runtime.runtime.Contains(variable) && (value is Symbol { Kind: not SymbolKind.String } or FrameAddress or TypedFrame || ctx.FrameAccess(value) is not null || value is Use u && ctx.State.Runtime.runtime.Contains(u.Variable) || ctx.IsInterfaceMetadataLoad(value)))
                    changed |= ctx.State.Runtime.runtime.Add(variable);
            foreach (var (variable, (call, _)) in ctx.results)
                if (!ctx.State.Runtime.runtime.Contains(variable) && call.Op?.Kind is OpKind.InitClass or OpKind.InitMethodRgctx or OpKind.InterfaceInvokeData or OpKind.ResolveGenericVirtual)
                    changed |= ctx.State.Runtime.runtime.Add(variable);
            foreach (var (variable, phi) in ctx.phis)
                if (!ctx.State.Runtime.runtime.Contains(variable) && phi.Sources.Any(ctx.State.Runtime.runtime.Contains))
                    changed |= ctx.State.Runtime.runtime.Add(variable);
        }
        while (changed);
        ctx.State.Calls.callBindings.InvalidateTypes();
    }

    internal static void MarkVtableLoads(this RecoveryScope ctx)
    {
        var calls = ctx.blocks.SelectMany(b => b.Statements).OfType<Call>().Where(c => c.Op?.Kind == OpKind.CallVirtual && c.Arguments.Length > 0).ToArray();
        if (calls.Length == 0)
            return;
        var users = new UseIndex(ctx.blocks.SelectMany(b => b.Statements));
        foreach (var call in calls)
        {
            // 目标：Load(klass + 常量)；klass：Load(接收者, 64)
            if (call.Target is not Use { Variable: var methodPointer } || !ctx.values.TryGetValue(methodPointer, out var target) || target is not Load { Width: 64 } entry)
                continue;
            var terms = new List<Expr>();
            void Add(Expr e)
            {
                if (e is Binary { Op: BinOp.Add } b)
                {
                    Add(b.Left);
                    Add(b.Right);
                }
                else
                    terms.Add(e);
            }

            Add(ctx.Expand(entry.Address));
            if (terms.OfType<Use>().ToArray() is not [{ Variable: var klass }] || terms.Count(t => t is not Const) != 1)
                continue;
            // 已通过同一引用的强制类型检查，isinst 结果与原对象身份相同。
            Expr Receiver(Expr expression)
            {
                var value = ctx.Expand(expression);
                var seen = new HashSet<Variable>();
                while (value is Use cast && seen.Add(cast.Variable) && ctx.results.TryGetValue(cast.Variable, out var castResult)
                    && castResult.Call is { Op.Kind: OpKind.IsInst, Op.Operand: TypeRef castType, Arguments: [Use original] }
                    && ctx.CheckedReference(original, castType, call.Address)) value = ctx.Expand(original);
                return value;
            }
            var receiverValue = Receiver(call.Arguments[0]);
            var joined = new List<Variable>();
            if (ctx.phis.TryGetValue(klass, out var klassPhi))
            {
                if (!klassPhi.Sources.All(v => users[v].All(s => s is Phi p && p.Target == klassPhi.Target)))
                    continue;
                var sameReceiver = klassPhi.Sources.All(v => ctx.values.GetValueOrDefault(v) is Load { Width: 64 } load && Receiver(load.Address) == receiverValue);
                var pairedReceivers = call.Arguments[0] is Use receiver && ctx.phis.TryGetValue(receiver.Variable, out var objectPhi) && ctx.blocks.Any(b => b.Statements.OfType<Phi>().Any(p => p.Target == klassPhi.Target) && b.Statements.OfType<Phi>().Any(p => p.Target == objectPhi.Target)) && klassPhi.Sources.Length == objectPhi.Sources.Length && klassPhi.Sources.Zip(objectPhi.Sources).All(pair => ctx.values.GetValueOrDefault(pair.First) is Load { Width: 64, Address: Use obj } && obj.Variable == pair.Second);
                if (!sameReceiver && !pairedReceivers)
                    continue;
                joined.AddRange(klassPhi.Sources);
            }
            else if (!ctx.values.TryGetValue(klass, out var klassValue) || klassValue is not Load { Width: 64, Address: var objectAddress } || Receiver(objectAddress) != receiverValue)
                continue;
            // 类指针的使用：虚表项的读取，或作为调用实参（保守约定）。
            var entries = ctx.values.Where(p => p.Value is Load { Width: 64 } l && ctx.ReadsKlass(l.Address, klass)).Select(p => p.Key).ToHashSet();
            if (users[klass].Any(s => s is not Call && !(s is Define d && entries.Contains(d.Target))))
                continue;
            ctx.State.Runtime.runtime.Add(klass);
            ctx.State.Runtime.runtime.UnionWith(joined);
            foreach (var e in entries)
                ctx.State.Runtime.runtime.Add(e);
        }
    }

    internal static bool ReadsKlass(this RecoveryScope ctx, Expr address, Variable klass)
    {
        var expanded = ctx.Expand(address);
        if (expanded is Use { Variable: var only } && only == klass)
            return true;
        return expanded is Binary { Op: BinOp.Add } b && (b.Left is Use { Variable: var l } && l == klass && b.Right is Const || b.Left is Binary inner && ctx.ReadsKlass(inner, klass) && b.Right is Const);
    }

    internal static bool IsInterfaceMetadataLoad(this RecoveryScope ctx, Expr value)
    {
        if (value is not Load { Width: 64 } load)
            return false;
        var address = ctx.Expand(load.Address);
        if (address is Binary { Op: BinOp.Add, Right: Const { Value: 0 or 8 } } add)
            address = ctx.Expand(add.Left);
        return address is Use u && ctx.results.TryGetValue(u.Variable, out var result) && result.Call.Op?.Kind == OpKind.InterfaceInvokeData;
    }
}
