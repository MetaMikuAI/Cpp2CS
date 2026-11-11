using System.Runtime.CompilerServices;

namespace Corpus
{
    public static class Dispatch
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int RepeatedInterface(IValue a, int x) { return a.Evaluate(x) + a.Evaluate(x + 1); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int InterfaceBranchTail(IValue a, bool c, int x) { int r; if (c) r = a.Evaluate(x); else r = a.Evaluate(-x); return r + 1; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int InterfaceTwoReceivers(IValue a, IValue b, bool c, int x) { int r; if (c) r = a.Evaluate(x); else r = b.Evaluate(x); return r * 3; }

    }
}
