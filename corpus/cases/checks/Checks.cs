using System.Runtime.CompilerServices;

namespace Corpus
{
    public static class Checks
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int NullCheck(Box a) { return a.Value + 1; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int ArrayBounds(int[] a, int i) { return a[i] + a[i + 1]; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int DivideByZero(int a, int b) { return a / b; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int RemainderByZero(int a, int b) { return a % b; }

    }
}
