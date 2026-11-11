using System;
using System.Runtime.CompilerServices;
namespace Corpus
{
    public struct Pair { public int X, Y; }
    public struct Nested { public Pair Inner; public int Z; }
    public sealed class Box { public int Value; }
    public interface IValue { int Evaluate(int x); }
    public class Base : IValue
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public virtual int Evaluate(int x) { return x + 1; }
    }
    public sealed class Derived : Base
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public override int Evaluate(int x) { return x * 3; }
    }
    public static class Initialized
    {
        public static int Value;
        static Initialized() { Value = Environment.ProcessorCount; }
    }
    public static class Support
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static int Opaque(int x) { return x ^ 0x5a; }
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static T Identity<T>(T x) where T : class { return x; }
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static Type TypeToken() { return typeof(Box); }
    }
}
