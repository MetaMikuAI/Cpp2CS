using static Cpp2CS.Idioms.IdiomRewriter;

namespace Cpp2CS.Idioms;

internal static class NormalizePass
{
    internal static void Normalize(this IdiomState state)
    {
        state.Passes.Fixpoint("idioms.normalize", 32, () =>
        {
            state.defs = new Defs(state.function);
            if (state.owner.RecoverUnusedInputs)
                state.DiscardUnusedInputs();
            if (state.KnownMetadataGuards())
                state.Cleanup();
            // 类型检查先于抛异常检查：castclass / as 后判空的失败一侧是只抛异常的块
            var changed = state.SplitMetadataGuards();
            changed |= state.Guards();
            changed |= state.RetainMetadataPath();
            changed |= state.TypeChecks();
            changed |= state.Checks();
            changed |= state.CheckedTypeChains();
            return changed;
        }, state.Cleanup);
    }
}
