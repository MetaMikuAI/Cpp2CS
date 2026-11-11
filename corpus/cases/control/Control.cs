using System.Runtime.CompilerServices;

namespace Corpus
{
    public static class Control
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int IfElse(int a, int b) { if (a > b) return Support.Opaque(a); else return Support.Opaque(b) + 1; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int Conditional(bool c, int a, int b) { return c ? a : b; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int While(int a) { int r = 0; while (a > 0) { r += a; a >>= 1; } return r; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int For(int n) { int r = 0; for (int i = 0; i < n; i++) r += Support.Opaque(i); return r; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int SmallSwitch(int n, int v) { switch(n) { case 0: return Support.Opaque(v); case 1: return v + 3; case 2: return v * 7; default: return -v; } }

    }
}
