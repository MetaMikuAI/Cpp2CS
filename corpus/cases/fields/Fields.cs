using System.Runtime.CompilerServices;

namespace Corpus
{
    public static class Fields
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int ReadInstance(Box a) { return a.Value; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static void WriteInstance(Box a, int v) { a.Value = v; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int ReadStatic() { return Initialized.Value; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static void WriteStatic(int v) { Initialized.Value = v; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int ReadStruct(Pair a) { return a.X; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static void WriteNested(ref Nested a, int v) { a.Inner.X = v; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int ReadNested(Nested a) { return a.Inner.Y; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int ReadArray(int[] a, int i) { return a[i]; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static void WriteArray(int[] a, int i, int v) { a[i] = v; }

    }
}
