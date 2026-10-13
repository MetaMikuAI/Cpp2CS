using System.Numerics;

namespace Cpp2CS.Ir;

// Arm ComputePACQARMA 的 QARMA5 变体；不包含地址位布局、使能条件和认证失败策略。
public static class Qarma64
{
    private static readonly ulong[] RoundConstants =
        [0, 0x13198A2E03707344, 0xA4093822299F31D0, 0x082EFA98EC4E6C89, 0x452821E638D01377];
    private static readonly int[] Shuffle = [13, 6, 11, 0, 7, 12, 1, 10, 8, 3, 14, 5, 2, 9, 4, 15];
    private static readonly int[] InverseShuffle = [3, 6, 12, 9, 14, 11, 1, 4, 8, 13, 7, 2, 5, 0, 10, 15];
    private static readonly int[] Substitution = [11, 6, 8, 15, 12, 0, 9, 14, 3, 7, 4, 5, 13, 2, 1, 10];
    private static readonly int[] InverseSubstitution = [5, 14, 13, 8, 10, 11, 1, 9, 2, 6, 15, 0, 4, 12, 7, 3];
    private static readonly int[] Tweak = [4, 5, 6, 7, 11, 2, 3, 8, 12, 13, 14, 15, 0, 1, 10, 9];
    private static readonly int[] InverseTweak = [12, 13, 5, 6, 0, 1, 2, 3, 7, 15, 14, 4, 8, 9, 10, 11];

    public static ulong Evaluate(ulong data, ulong modifier, BigInteger key)
    {
        var keyHigh = (ulong)((key >> 64) & ulong.MaxValue);
        var keyLow = (ulong)(key & ulong.MaxValue);
        var modifiedKey = BitOperations.RotateRight(keyHigh, 1) ^ (keyHigh >> 63);
        var tweak = modifier;
        var value = data ^ keyHigh;
        for (var round = 0; round <= 4; round++)
        {
            value ^= keyLow ^ tweak ^ RoundConstants[round];
            if (round != 0) value = Mix(Permute(value, Shuffle));
            value = Substitute(value, Substitution);
            tweak = UpdateTweak(tweak, false);
        }
        value ^= modifiedKey ^ tweak;
        value = Substitute(Mix(Permute(value, Shuffle)), Substitution);
        value = Mix(Permute(value, Shuffle)) ^ keyLow;
        value = Substitute(Permute(value, InverseShuffle), InverseSubstitution);
        value = Permute(Mix(value), InverseShuffle) ^ keyHigh ^ tweak;
        for (var round = 0; round <= 4; round++)
        {
            value = Substitute(value, InverseSubstitution);
            if (round != 4) value = Permute(Mix(value), InverseShuffle);
            tweak = UpdateTweak(tweak, true);
            value ^= RoundConstants[4 - round] ^ keyLow ^ tweak ^ 0xC0AC29B7C97C50DD;
        }
        return value ^ modifiedKey;
    }

    private static int Cell(ulong value, int index) => (int)((value >> (index * 4)) & 15);
    private static int Rotate(int cell, int amount) => ((cell << amount) | (cell >> (4 - amount))) & 15;

    private static ulong Permute(ulong value, int[] source)
    {
        ulong result = 0;
        for (var cell = 0; cell < 16; cell++) result |= (ulong)Cell(value, source[cell]) << (cell * 4);
        return result;
    }

    private static ulong Substitute(ulong value, int[] table)
    {
        ulong result = 0;
        for (var cell = 0; cell < 16; cell++) result |= (ulong)table[Cell(value, cell)] << (cell * 4);
        return result;
    }

    private static ulong Mix(ulong value)
    {
        ulong result = 0;
        for (var column = 0; column < 4; column++)
        {
            var a = Cell(value, column);
            var b = Cell(value, column + 4);
            var c = Cell(value, column + 8);
            var d = Cell(value, column + 12);
            result |= (ulong)(Rotate(d, 1) ^ Rotate(c, 2) ^ Rotate(b, 1)) << (column * 4);
            result |= (ulong)(Rotate(d, 2) ^ Rotate(c, 1) ^ Rotate(a, 1)) << ((column + 4) * 4);
            result |= (ulong)(Rotate(d, 1) ^ Rotate(b, 1) ^ Rotate(a, 2)) << ((column + 8) * 4);
            result |= (ulong)(Rotate(c, 1) ^ Rotate(b, 2) ^ Rotate(a, 1)) << ((column + 12) * 4);
        }
        return result;
    }

    private static ulong UpdateTweak(ulong value, bool inverse)
    {
        var map = inverse ? InverseTweak : Tweak;
        ulong result = 0;
        for (var index = 0; index < 16; index++)
        {
            var cell = Cell(value, map[index]);
            if (inverse ? index is 0 or 6 or 8 or 9 or 10 or 11 or 15 : index is 2 or 4 or 7 or 11 or 12 or 14 or 15)
                cell = inverse ? ((cell << 1) & 15) | ((cell ^ (cell >> 3)) & 1)
                    : (cell >> 1) | (((cell ^ (cell >> 1)) & 1) << 3);
            result |= (ulong)cell << (index * 4);
        }
        return result;
    }
}
