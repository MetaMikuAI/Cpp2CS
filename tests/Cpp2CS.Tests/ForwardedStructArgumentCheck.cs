using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class ForwardedStructArgumentCheck
{
    [Command("forwarded-struct-argument", "静态转换候选的完整结构体实参", Gate = Gate.Unit)]
    public static int Run()
    {
        var definition = new TypeDef { Index = 0, Assembly = "Tests", Namespace = "Tests", Name = "Value", Token = 0,
            Attributes = TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false };
        var type = new DefinitionRef(definition, []);
        var root = new ArgumentValue(0, type, 0);
        var pieces = Enumerable.Range(0, 4).Select(i => new AbiPiece(Storage.Vec(i), 32, i * 4)).ToArray();
        var parameter = new AbiValue(type, Passing.Registers, pieces);
        var values = pieces.ToDictionary(p => p.Register, p => (Expr)new Use(new(p.Register, 0), 128));
        var a = new Assertions();
        foreach (var mode in new[] { "whole", "missing", "swapped", "other-root", "wrong-width", "indirect" })
        {
            var registers = new Dictionary<Storage, Expr>(values);
            if (mode == "missing") registers.Remove(pieces[3].Register);
            (ArgumentValue, AbiPiece)? Input(Expr value)
            {
                var index = ((Use)value).Variable.Storage.Index;
                var piece = pieces[index];
                if (index == 3 && mode == "swapped") piece = pieces[2];
                if (index == 3 && mode == "wrong-width") piece = piece with { Width = 64 };
                return (index == 3 && mode == "other-root" ? root with { Index = 1 } : root, piece);
            }
            a.Equal(mode == "whole", ForwardedStructArgument.Whole(mode == "indirect" ? parameter with { Passing = Passing.Indirect } : parameter,
                registers, Input), mode);
        }
        return a.Finish("forwarded-struct-argument");
    }
}
