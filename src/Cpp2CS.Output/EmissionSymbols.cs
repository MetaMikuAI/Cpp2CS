using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

/// <summary>程序集级符号缓存和原生认回证据，不保存当前方法的局部变量或跳转标签。</summary>
internal sealed class EmissionSymbols
{
    public Dictionary<ModuleDefinition, (MethodReference At, MethodReference Fail, MethodDefinition Value)> Unrecovered { get; } = new();
    public Dictionary<ModuleDefinition, (MethodDefinition Of, MethodDefinition Do, MethodDefinition Result, MethodDefinition Completed, MethodDefinition CompletedVoid)> Awaits { get; } = new();
    public HashSet<Instruction> ExplicitInitializations { get; } = [];
    public Dictionary<Instruction, FieldAccessor> AccessorCalls { get; } = [];
    public Dictionary<Instruction, MethodRef> InlineCalls { get; } = [];
}
