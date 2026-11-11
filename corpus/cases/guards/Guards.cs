using System.Runtime.CompilerServices;

namespace Corpus
{
    public static class Guards
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static System.Type MetadataOnBranches(bool c) { if (c) { Support.Opaque(1); return Support.TypeToken(); } Support.Opaque(2); return Support.TypeToken(); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int ClassInitOnBranches(bool c, int v) { if (c) return Initialized.Value + Support.Opaque(v); return Support.Opaque(v + 1) - Initialized.Value; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int GuardWithNull(Box a) { if (a == null) return Initialized.Value; return a.Value + Initialized.Value; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int GuardWithBounds(int[] a, int i) { if (i < 0) return Initialized.Value; return a[i] + Initialized.Value; }

    }
}
