using System.Runtime.CompilerServices;

namespace Corpus
{
    public static class TypeChecks
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int IsMerge(object a, object b, bool c) { bool r; if(c) r = a is Box; else r = b is Box; return r ? 7 : 9; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static Box AsMerge(object a, object b, bool c) { Box r; if(c) r = a as Box; else r = b as Box; return r; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        public static Box CastMerge(object a, object b, bool c) { Box r; if(c) r = (Box)a; else r = (Box)b; return r; }

    }
}
