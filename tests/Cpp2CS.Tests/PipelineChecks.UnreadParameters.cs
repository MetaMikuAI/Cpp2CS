using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using R = System.Reflection;

namespace Cpp2CS.Tests;

internal static partial class PipelineChecks
{
    private static void ParameterReadsChecks(Assertions checks, GlobalFacts basis)
    {
        var owner = new TypeDef { Index = basis.Model.Types.Count, Assembly = "ParameterFacts.dll", Namespace = "", Name = "Facts",
            Token = 0x02000001, Attributes = R.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var integer = new DefinitionRef(basis.Model.Types.Single(type => type.Name == "Int32"), []);
        var methods = new[] { "Unused", "Read", "LiftFailure", "Abort" }.Select((name, i) => new MethodDef { Index = i, Owner = owner,
            Name = name, Token = (uint)(0x06000001 + i), Attributes = R.MethodAttributes.Public | R.MethodAttributes.Static,
            ImplAttributes = 0, Slot = -1, ReturnType = integer, Parameters = [new("value", integer, 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var model = new ProgramModel { MetadataVersion = 31, Types = basis.Model.Types.Append(owner).ToArray(), Methods = methods,
            Fields = [], RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [], Assemblies = basis.Model.Assemblies
                .Append(new AssemblyDef { Name = owner.Assembly, AssemblyName = "ParameterFacts", Version = new(1, 0), Culture = "", PublicKey = [], Types = [owner] }).ToArray() };
        var entries = methods.Select((method, i) => new CodeEntry((ulong)(16 + i * 4), EntryKind.Method, MethodRef.Open(method), i, null)).ToArray();
        var map = new Registrations { CodeRegistration = 0, MetadataRegistration = 0, Entries = entries,
            ByAddress = entries.ToDictionary(entry => entry.Address, entry => ImmutableArray.Create(entry)),
            Rgctx = new Dictionary<(string, uint), ImmutableArray<RgctxEntry>>(), MetadataUsageSlots = [], TypePointers = new Dictionary<ulong, int>(),
            InvokerOf = new Dictionary<MethodDef, int>(), UsageEntities = new Dictionary<ulong, Usage>() };
        var facts = new GlobalFacts(new EmptyImage(), model, map, basis.Spec, "arm64");
        var frontend = new ParameterFactsFrontend(); var source = ParameterReadsAssembly.Get(facts, frontend);
        for (int round = 0; round < 2; round++)
        foreach (int i in new[] { 0, 1, 2 })
        {
            var result = source.Get(entries[i].Address, entries[i].Method!);
            checks.True(i == 2 ? !result.IsSuccess : result.IsSuccess && result.Value.Parameters[0].IsRead == (i == 1),
                "按运行形参读取摘要 " + methods[i].Name + "：" + result.Why);
        }
        Parallel.For(0, 16, _ => source.Get(entries[0].Address, entries[0].Method!));
        checks.True(new[] { 0, 1, 2 }.All(i => frontend.Lifts.GetValueOrDefault(methods[i].Name) == 1), "成功、读取及提升失败均按入口与方法缓存");
        bool aborted = false;
        try { source.Get(entries[3].Address, entries[3].Method!); }
        catch (TimeoutException) { aborted = true; }
        finally { WorkAbort.Reset(); }
        var retried = source.Get(entries[3].Address, entries[3].Method!);
        checks.True(aborted && retried is { IsSuccess: true, Value.Parameters: [{ IsRead: false }] }
            && frontend.Lifts["Abort"] == 2, "中止后换新上下文并重新提升未完成的形参摘要");
        var changedMethod = new MethodDef { Index = 99, Owner = owner, Name = "OtherDeclaration", Token = 0x06000099,
            Attributes = R.MethodAttributes.Public | R.MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = integer };
        checks.True(!source.Get(entries[0].Address, MethodRef.Open(changedMethod)).IsSuccess, "相同原生入口的不同托管声明不共用事实");
    }
    private sealed class ParameterFactsFrontend : IMethodStage<CodeEntry, NativeFunction>
    {
        public Dictionary<string, int> Lifts { get; } = [];
        public string Name => "前端";
        public StageResult<NativeFunction> Run(CodeEntry input, MethodContext context)
        {
            var name = context.Method.Name; Lifts[name] = Lifts.GetValueOrDefault(name) + 1;
            if (name == "LiftFailure") return new Missing<NativeFunction>(new(Name, input.Address, "提升", new("test.parameter-reads", "提升失败")));
            if (name == "Abort" && Lifts[name] == 1) { WorkAbort.Request(); WorkAbort.Check(); }
            var terms = new TermTable(); var entry = new BlockIdentity();
            var builder = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var value = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64); builder.Inputs.Add(new(new(SlotKind.Integer), value));
            // 隐藏的方法信息槽不参与托管参数摘要。
            builder.Inputs.Add(new(new(SlotKind.Integer, 1), terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64)));
            builder.Blocks.Add(new(entry, [], [], new Return([new(new(SlotKind.Integer), name == "Read" ? value : terms.Constant(7, 64))])));
            return new Completed<NativeFunction>(builder.Freeze());
        }
    }
}
