using System.Runtime.CompilerServices;

namespace Corpus
{
    public static class Calls
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int DirectCall(int a) { return Support.Opaque(a); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int VirtualCall(Base a, int v) { return a.Evaluate(v); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int InterfaceCall(IValue a, int v) { return a.Evaluate(v); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int DelegateCall(System.Func<int,int> a, int v) { return a(v); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static string SharedGenericString(string a) { return Support.Identity<string>(a); }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static object SharedGenericObject(object a) { return Support.Identity<object>(a); }

    }
}
