using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

internal static class BindingChecks
{
    public const string Command = "binding";
    public static int Run()
    {
        var a = new Assertions();
        var terms = new TermTable();
        var binder = new MethodBinder(new(new NoLayouts()), new Aapcs64());
        var method = Method(false);
        var entry = binder.Entry(method, BindingEntryKind.Ordinary).Value!;
        var inputs = Enumerable.Range(0, 8).Select(i => new EntryInput(new(SlotKind.Integer, i), terms.Constant(0x100UL + (ulong)i, 64)))
            .Concat(Enumerable.Range(0, 8).Select(i => new EntryInput(new(SlotKind.Floating, i), terms.Constant(0x200UL + (ulong)i, 128)))).ToImmutableArray();
        var values = inputs.Select(i => new SlotValue(i.Slot, i.Value)).ToImmutableArray();
        var area = terms.Constant(0x1000, 64);
        var integer = binder.Parameter(entry, entry.Managed!.ParameterIndices[0], terms, inputs).Value!;
        var pointer = binder.Parameter(entry, entry.Managed.ParameterIndices[1], terms, inputs).Value!;
        a.True(integer.Source is TermSource { Term.Width: 32, Term.ConstantValue: var n } && n == 0x101
            && pointer.Source is TermSource { Term.Width: 64 } && integer.UnusedBits == UnusedBitRule.Unspecified,
            "整数与指针参数切片，高位不假定为零");
        var floating = binder.Parameter(entry, entry.Managed.ParameterIndices[2], terms, inputs).Value!;
        a.True(floating.Source is TermSource { Term.Width: 64, Term.ConstantValue: var f } && f == 0x200, "浮点参数切片");
        a.True(entry.This is { Pieces: [{ Slot.Kind: SlotKind.Integer, Slot.Position: 0 }] }
            && binder.Parameter(entry, entry.Managed.ThisIndex!.Value, terms, inputs).Value!.Source is TermSource { Term.ConstantValue: var self }
            && self == 0x100 && entry.MethodInformation!.Pieces[0].Slot.Position == 3, "实例 this 与隐藏信息");
        CAggregate Aggregate(int count) => new(count * 8, 8, Enumerable.Range(0, count).Select(i => new CField(i * 8, new CInteger(64))).ToImmutableArray());
        SignatureBinding Signature(CType type, int leading = 0) => binder.Classify(new([
            .. Enumerable.Repeat<CType>(new CInteger(64), leading), type], type)).Value!;
        var small = Signature(Aggregate(2));
        var split = binder.Parameter(small, 0, terms, inputs).Value!;
        a.True(small.Parameters[0].Pieces.Length == 2 && split.Source is TermSource { Term.Width: 128, Term.ConstantValue: var bits }
            && bits == ((System.Numerics.BigInteger)0x101 << 64 | 0x100), "小聚合按值偏移拼接两个槽");
        var hfa = Signature(new CAggregate(16, 4, [.. Enumerable.Range(0, 4).Select(i => new CField(i * 4, new CFloat(32)))]));
        a.True(hfa.Parameters[0].CopyAddress is null && hfa.Parameters[0].Pieces.Length == 4
            && hfa.Parameters[0].Pieces.All(p => p.Slot.Kind == SlotKind.Floating), "四个 float 的 HFA 不走间接传递");
        var large = Signature(Aggregate(3));
        a.True(binder.Parameter(large, 0, terms, inputs).Value!.Source is IndirectSource { Length: 24, Address: TermSource }, "大聚合传副本地址");
        var stack = Signature(new CInteger(32), 8);
        a.True(binder.Parameter(stack, 8, terms, inputs, area).Value!.Source is PiecesSource
            { Pieces: [{ ValueOffset: 0, Length: 4, Source: StackSource { Offset: 0, Length: 4 } }] }, "栈参数只返回偏移与长度");
        var stackPointer = Signature(Aggregate(3), 8);
        a.True(binder.Parameter(stackPointer, 8, terms, inputs, area).Value!.Source is IndirectSource
            { Address: StackSource { Offset: 0, Length: 8 }, Length: 24 }, "栈上的副本地址不读内存");
        var buffer = new SlotValue(new(SlotKind.IndirectResult), area);
        a.True(binder.Return(new([]), large, terms, [buffer]).Value!.Source is IndirectSource { Address: TermSource { Term: var address }, Length: 24 }
            && ReferenceEquals(address, area), "间接结果缓冲区从输入槽取得");
        a.True(binder.Return(new(values), small, terms).Value!.Source is TermSource { Term: var returned }
            && ReferenceEquals(returned, ((TermSource)split.Source!).Term), "返回槽与入口槽使用同一拼接");
        var target = new ImageFunction(1);
        var call = new Call(new(), target, values, values, OutgoingArgumentArea: area);
        var map = new Map([new(method, BindingEntryKind.Ordinary), new(Method(true), BindingEntryKind.Ordinary)]);
        var candidates = binder.Call(call, target, map, terms);
        a.True(candidates is { Failure.Kind: BindingFailureKind.AmbiguousCandidates, Candidates.Length: 2 }
            && candidates.Candidates.All(c => c.Binding.Success)
            && candidates.Candidates[0].Binding.Value!.This is not null
            && candidates.Candidates[1].Binding.Value!.This is null, "共享入口保留全部候选及各自绑定");
        a.True(binder.Call(call, target, new Map([new(method, BindingEntryKind.Ordinary)]), terms)
            is { Failure: null, Candidates: [{ Binding.Success: true }] }, "唯一映像目标绑定");
        a.True(binder.Call(call with { Target = new ComputedTarget(area) }, entry, terms).Success
            && binder.Call(call, small.Signature, terms).Success, "已解析的间接目标和 C 签名入口");
        a.True(binder.Parameter(entry, 0, terms, []).Failure?.Kind == BindingFailureKind.MissingSlot
            && binder.Parameter(stack, 8, terms, inputs).Failure?.Kind == BindingFailureKind.MissingSlot
            && binder.Return(new([]), large, terms).Failure?.Kind == BindingFailureKind.MissingSlot, "槽与实参区缺失都有原因");
        var generic = Method(true).Method;
        generic.GenericParameters = [new() { Name = "T", Position = 0, Attributes = 0 }];
        var canonical = new MethodRef(generic, [], [method.Method.Parameters[0].Type]);
        a.True(binder.Entry(canonical, BindingEntryKind.SharedGeneric).Success,
            "封闭规范实例走普通 C 层签名推导");
        var fullyShared = new DefinitionRef(new TypeDef {
            Index = 10, Assembly = "mscorlib.dll", Namespace = "Unity.IL2CPP.Metadata", Name = "__Il2CppFullySharedGenericType",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false }, []);
        a.True(binder.Entry(canonical with { MethodArguments = [fullyShared] }, BindingEntryKind.SharedGeneric).Failure is
            { Kind: BindingFailureKind.SignatureUnavailable, Detail: "完全共享实例的签名尚未支持" }, "完全共享实例单列签名失败");
        a.True(binder.Entry(canonical with { MethodArguments = [new ArrayRef(fullyShared, 1)] }, BindingEntryKind.SharedGeneric).Failure?.Detail
            == "完全共享实例的签名尚未支持", "嵌套完全共享类型也不推导");
        a.True(binder.Entry(MethodRef.Open(generic), BindingEntryKind.SharedGeneric).Failure?.Detail == "泛型实参未完整封闭",
            "开放定义不能作为规范实例");
        a.True(binder.Entry(method, BindingEntryKind.AdjustorThunk).Failure is { Kind: BindingFailureKind.SignatureUnavailable, Detail.Length: > 0 }
            && binder.Classify(new([], new CInteger(24))).Failure is { Kind: BindingFailureKind.ClassificationFailed, Detail.Length: > 0 }
            && binder.Call(call, target, new Map([]), terms).Failure is { Kind: BindingFailureKind.EntryNotMapped, Detail.Length: > 0 }, "失败种类有限且不猜签名");
        return a.Finish("形参与调用绑定");
    }

    private sealed class Map(ImmutableArray<BindingEntry> entries) : IBindingCodeMap
    {
        public ImmutableArray<BindingEntry> At(ulong entryOffset) => entries;
    }
    private static MethodRef Method(bool isStatic)
    {
        TypeDef Type(string name, bool value) => new()
        {
            Index = 0, Assembly = "mscorlib.dll", Namespace = "System", Name = name, Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = value, IsEnum = false,
        };
        var integer = new DefinitionRef(Type("Int32", true), []);
        return new(new MethodDef
        {
            Index = 0, Owner = Type("Owner", false), Name = "Apply", Token = 0,
            Attributes = isStatic ? MethodAttributes.Static : MethodAttributes.Public, ImplAttributes = 0, Slot = -1,
            ReturnType = integer, Parameters = [new("number", integer, 0, null, false),
                new("pointer", new PointerRef(integer), 0, null, false),
                new("floating", new DefinitionRef(Type("Double", true), []), 0, null, false)],
        }, [], []);
    }
    private sealed class NoLayouts : ITypeLayouts
    {
        public TypeLayout? Of(DefinitionRef type) => null;
        public (int Size, int Alignment)? TrySizeAndAlignment(TypeRef type) => null;
        public (int Size, int Alignment) SizeAndAlignment(TypeRef type) => throw new InvalidOperationException("测试不读取布局");
    }
}
