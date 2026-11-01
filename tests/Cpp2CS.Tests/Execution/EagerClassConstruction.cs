using System.Text;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

/// <summary>Unity 2022.3 CodeGenModule 的 staticConstructorTypeIndices；独立于任何被测方法的指令。</summary>
[ShapeModel("类初始化", Basis = "ECMA-335 第 II 部分 10.5.3 节（beforefieldinit 与精确初始化时机）；IL2CPP 提前运行类构造的普查（classinit 命令）")]
internal static class EagerClassConstruction
{
    private const string Attribute = "Unity.IL2CPP.CompilerServices.Il2CppEagerStaticClassConstructionAttribute";

    public static HashSet<TypeDef> Read(ProgramFacts facts, TextWriter? report = null)
    {
        var image = facts.Model.Image;
        ulong Pointer(ulong address) => image.ReadPointer(address) ?? throw new InvalidDataException($"eager 注册表 0x{address:x} 不是指针");
        string Name(ulong address)
        {
            var bytes = new List<byte>();
            for (var i = 0; i < 256; i++)
            {
                var value = image.Read(address + (ulong)i, 1)[0];
                if (value == 0) return Encoding.UTF8.GetString(bytes.ToArray());
                bytes.Add(value);
            }
            throw new InvalidDataException("eager 模块名未终结");
        }
        var registration = facts.Registrations.CodeRegistration;
        var modules = Pointer(registration + 128);
        var result = new HashSet<TypeDef>();
        for (var i = 0; i < image.ReadU32(registration + 120); i++)
        {
            var module = Pointer(modules + (ulong)i * 8);
            var table = Pointer(module + 112);
            if (table == 0) continue;
            var name = Name(Pointer(module));
            for (var k = 0; k <= facts.Model.Types.Count; k++)
            {
                var index = image.ReadI32(table + (ulong)k * 4);
                if (index == 0) break;
                if (index < 0 || index >= facts.Model.Types.Count) throw new InvalidDataException($"eager {name} 0x{table:x}[{k}]={index}");
                var type = facts.Model.Types[index];
                if (type.Assembly != name || !result.Add(type)) throw new InvalidDataException($"eager {name} 类型身份不符：{type}");
                report?.WriteLine($"{name}\t0x{module:x}\t0x{table + (ulong)k * 4:x}\t{index}\t{type.FullName}");
            }
        }
        var attributes = facts.Model.Types.Where(t => t.CustomAttributes.Any(a => a.Constructor.Owner.FullName == Attribute)).ToHashSet();
        if (!result.SetEquals(attributes)) throw new InvalidDataException($"eager 注册表与特性不符：仅表 {string.Join(',', result.Except(attributes))}；仅特性 {string.Join(',', attributes.Except(result))}");
        report?.WriteLine($"全程序模块 {image.ReadU32(registration + 120)}；eager 类型 {result.Count}；特性交叉核对 {attributes.Count}；差异 0");
        return result;
    }

    [Command("struct-eager-census", "提前静态初始化的全程序注册表与特性核对", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        Read(FactsBuilder.Build(binary, metadata), Console.Out);
        return 0;
    }
}
