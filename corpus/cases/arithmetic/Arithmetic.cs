using System.Runtime.CompilerServices;

namespace Corpus
{
    public static class Arithmetic
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int IntegerArithmetic(int a, int b) { return unchecked((a + b) * (a - b)); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static float FloatArithmetic(float a, float b) { return (a + b) / (a - b); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static double DoubleArithmetic(double a, double b) { return a * b + a / b; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static uint BitOperations(uint a, int n) { return ((a << n) ^ (a >> n)) & 0x7fffffff; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int SignedShift(int a, int n) { return a >> n; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static short NarrowInteger(long a) { return unchecked((short)a); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int FloatToInteger(float a) { return (int)a; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static double UnsignedToDouble(ulong a) { return a; }

    }
}
