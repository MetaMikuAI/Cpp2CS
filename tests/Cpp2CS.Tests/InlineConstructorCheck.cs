using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class InlineConstructorCheck
{
    [Command("inline-constructors", "内联构造的尾部写屏障与字段实参匹配", Gate = Gate.Unit)]
    public static int Run()
    {
        var type = new TypeDef { Index = -1, Assembly = "Constructors.Tests.dll", Namespace = "Tests", Name = "Subject",
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var reference = new DefinitionRef(type, []);
        var method = new MethodRef(new MethodDef { Index = -1, Owner = type, Name = ".ctor", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        var self = new Use(new(Storage.Gpr(0), 0), 64);
        var argument = new Use(new(Storage.Gpr(1), 0), 64);
        var signature = new AbiSignature(new(reference, Passing.Registers, [new(Storage.Gpr(0), 64, 0)]),
            [new(reference, Passing.Registers, [new(Storage.Gpr(1), 64, 0)])], null, null);
        Call Base(Expr receiver) => new(4, CallKind.Direct, Expr.C(200, 64))
            { Sources = [Storage.Gpr(0)], Arguments = [receiver] };
        Store Field(Expr receiver, Expr value) => new(8, new Binary(BinOp.Add, receiver, Expr.C(16, 64), 64), value);
        MachineFunction Function(params Stmt[] statements) => new() { Entry = 0,
            Range = new(0, 32, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [new(0) { Statements = statements.ToList() }] };
        var tail = new Call(12, CallKind.Tail, Expr.C(300, 64)) { Op = new(OpKind.WriteBarrier, null) };
        var pattern = InlineConstructors.Create(method, signature, Function(Base(self), Field(self, argument), tail));
        var a = new Assertions();
        a.True(pattern is { Effects.Count: 2 }, "尾部写屏障结束构造模板，不重复要求普通调用形态");
        var created = new Variable(Storage.Gpr(0), 1);
        var value = Expr.C(64, 64);
        var caller = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Base(new Use(created, 64)), Field(new Use(created, 64), value), tail);
        var match = InlineConstructors.Find(pattern!, caller, caller.EntryBlock, 0, created);
        a.True(match is { Statements.Count: 2 } && match.Arguments.SequenceEqual([value]), "字段值绑定成构造实参");
        a.True(!match!.Statements.Contains(tail), "调用点的尾部屏障保留返回语义");
        var ordinaryTail = InlineConstructors.Create(method, signature, Function(Base(self), Field(self, argument), tail with { Op = null }));
        a.True(ordinaryTail is { Effects.Count: 3 } && ordinaryTail.Effects[^1] is Call { Kind: CallKind.Direct, Op: null },
            "普通尾调用保留为必须匹配的副作用");
        a.True(InlineConstructors.Find(ordinaryTail!, caller, caller.EntryBlock, 0, created) is null,
            "不能用写屏障冒充普通尾调用");
        a.True(InlineConstructors.Create(method, signature, Function(Base(self), Field(self, argument))) is null,
            "缺少已证明终结点时不生成模板");
        caller.EntryBlock.Statements[2] = Field(new Use(created, 64), new Load(value, 64));
        a.True(InlineConstructors.Find(pattern!, caller, caller.EntryBlock, 0, created) is null,
            "不能把有访存的实参提前到对象分配点");
        var guarded = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Base(new Use(created, 64)), new Jump(8, 16));
        var writes = new Block(16) { Statements = [Field(new Use(created, 64), value), new Return(20)] };
        var handler = new Block(24) { IsLandingPad = true, Statements = [new Return(28)] };
        MachineFunction.AddEdge(guarded.EntryBlock, writes);
        MachineFunction.AddEdge(guarded.EntryBlock, handler);
        guarded.EntryBlock.Handler = handler;
        guarded.Blocks.AddRange([writes, handler]);
        guarded.Renumber();
        a.True(InlineConstructors.Find(pattern!, guarded, guarded.EntryBlock, 0, created) is not null,
            "新对象直接字段写入可位于保护调用之后的无异常边块");
        guarded.EntryBlock.Statements.RemoveAt(1);
        writes.Statements.Insert(0, Base(new Use(created, 64)));
        a.True(InlineConstructors.Find(pattern!, guarded, guarded.EntryBlock, 0, created) is null,
            "基类调用不能跨越分配的异常去向");
        var fieldsFirst = InlineConstructors.Create(method, signature, Function(Field(self, argument), Base(self) with { Kind = CallKind.Tail }));
        var initialized = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Field(new Use(created, 64), value), Base(new Use(created, 64)), new Return(20));
        a.True(fieldsFirst is { Effects.Count: 2 }
            && InlineConstructors.Find(fieldsFirst, initialized, initialized.EntryBlock, 0, created) is { } fieldsMatch
            && fieldsMatch.Arguments.SequenceEqual([value]), "字段初始化后尾调用基类可认回完整构造");
        initialized.EntryBlock.Statements[2] = Base(new Use(created, 64)) with { Target = Expr.C(201, 64) };
        a.True(InlineConstructors.Find(fieldsFirst!, initialized, initialized.EntryBlock, 0, created) is null,
            "基类调用目标必须相同");
        Store NextField(Expr receiver, Expr value) => new(9, new Binary(BinOp.Add, receiver, Expr.C(24, 64), 64), value);
        var beforeBase = InlineConstructors.Create(method, signature,
            Function(Field(self, argument), NextField(self, Expr.C(7, 64)), Base(self) with { Kind = CallKind.Tail }));
        var reversedBeforeBase = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), NextField(new Use(created, 64), Expr.C(7, 64)),
            Field(new Use(created, 64), value), Base(new Use(created, 64)), new Return(20));
        a.True(beforeBase is not null && InlineConstructors.Find(beforeBase, reversedBeforeBase, reversedBeforeBase.EntryBlock, 0, created)
            is { } beforeMatch && beforeMatch.Arguments.SequenceEqual([value]), "首次调用前的新对象独立字段可交换");
        var beforeAndAfter = InlineConstructors.Create(method, signature,
            Function(Field(self, argument), Base(self), NextField(self, Expr.C(1, 8)), new Return(20)));
        var surrounding = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Field(new Use(created, 64), value),
            Base(new Use(created, 64)), NextField(new Use(created, 64), Expr.C(1, 8)), new Return(20));
        a.True(beforeAndAfter is { Effects.Count: 3 } && InlineConstructors.Find(beforeAndAfter, surrounding,
            surrounding.EntryBlock, 0, created) is { } surroundingMatch && surroundingMatch.Arguments.SequenceEqual([value]),
            "基类调用前后的字段初始化均完整匹配");
        var ordered = InlineConstructors.Create(method, signature,
            Function(Base(self), Field(self, argument), NextField(self, Expr.C(7, 64)), tail))!;
        var swapped = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Base(new Use(created, 64)),
            NextField(new Use(created, 64), Expr.C(7, 64)), Field(new Use(created, 64), value), tail);
        a.True(InlineConstructors.Find(ordered, swapped, swapped.EntryBlock, 0, created) is null,
            "未证明对象尚未发布时保留字段顺序");
        a.True(InlineConstructors.Find(ordered with { ReorderStores = true }, swapped, swapped.EntryBlock, 0, created)
            is { } reordered && reordered.Arguments.SequenceEqual([value]), "独立字段交换仍绑定相同构造实参");
        var overlap = ordered with { ReorderStores = true, Effects = [ordered.Effects[0], ordered.Effects[1],
            Field(self, Expr.C(7, 64))] };
        a.True(InlineConstructors.Find(overlap, swapped, swapped.EntryBlock, 0, created) is null,
            "重叠字段不能交换写入顺序");
        var floating = new PrimitiveRef("Single");
        var floatSignature = signature with { Parameters = [
            new(floating, Passing.Registers, [new(Storage.Vec(0), 32, 0)]),
            new(floating, Passing.Registers, [new(Storage.Vec(1), 32, 0)])] };
        Store At(Expr receiver, int offset, Expr source) => new(8,
            new Binary(BinOp.Add, receiver, Expr.C((ulong)offset, 64), 64), source);
        var save = new Store(0, new FrameAddress(-16), new Use(new(Storage.Vec(8), 0), 64));
        var floats = InlineConstructors.Create(method, floatSignature, Function(save, Base(self),
            At(self, 16, new Use(new(Storage.Vec(0), 0), 32)),
            At(self, 20, new Use(new(Storage.Vec(1), 0), 32)), new Return(20)));
        a.True(floats is not null, "浮点参数和向量寄存器低 64 位保存可生成构造模板");
        var packed = new Use(new(Storage.Vec(8), 1), 64);
        var combined = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Base(new Use(created, 64)),
            At(new Use(created, 64), 16, packed), new Return(20));
        var floatPattern = floats! with { ReorderStores = true };
        a.True(InlineConstructors.Find(floatPattern, combined, combined.EntryBlock, 0, created) is { } floatMatch
            && floatMatch.Arguments.SequenceEqual([new Use(packed.Variable, 32), new Extract(packed, 32, 32)]),
            "合并写入按字段偏移拆回两个浮点参数，保持位型和顺序");
        var gap = floatPattern with { Effects = [floats!.Effects[0], floats.Effects[1],
            At(self, 24, new Use(new(Storage.Vec(1), 0), 32))] };
        a.True(InlineConstructors.Find(gap, combined, combined.EntryBlock, 0, created) is null,
            "宽写入不能覆盖构造模板没有写入的间隙");
        combined.EntryBlock.Statements[2] = At(new Use(created, 64), 16, new Use(packed.Variable, 128));
        a.True(InlineConstructors.Find(floatPattern, combined, combined.EntryBlock, 0, created) is null,
            "宽写入不能超出构造字段范围");
        combined.EntryBlock.Statements[2] = At(new Use(new(Storage.Gpr(9), 1), 64), 16, packed);
        a.True(InlineConstructors.Find(floatPattern, combined, combined.EntryBlock, 0, created) is null,
            "合并写入必须仍然指向本次分配的对象");
        a.True(InlineConstructors.Create(method, floatSignature, Function(save with {
            Value = new Use(new(Storage.Vec(8), 0), 128) }, Base(self), floats.Effects[1], floats.Effects[2], new Return(20))) is null,
            "向量高 64 位不属于 ABI 保存范围，不能当作序言忽略");
        var boolSignature = signature with { Parameters = [new(new PrimitiveRef("Boolean"), Passing.Registers, [new(Storage.Gpr(1), 8, 0)])] };
        var mask = Fold.Convert(ConvKind.Truncate, new Binary(BinOp.And,
            new Use(new(Storage.Gpr(1), 0), 32), Expr.C(1, 32), 32), 8);
        var boolPattern = InlineConstructors.Create(method, boolSignature, Function(Base(self), Field(self, mask), new Return(20)))!;
        foreach (var bit in new[] { 0UL, 1UL, 2UL })
        {
            var boolCaller = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)), Base(new Use(created, 64)),
                Field(new Use(created, 64), Expr.C(bit, 8)), new Return(20));
            var boolMatch = InlineConstructors.Find(boolPattern, boolCaller, boolCaller.EntryBlock, 0, created);
            a.True(bit < 2 ? boolMatch is not null && boolMatch.Arguments.SequenceEqual([Expr.C(bit, 8)]) : boolMatch is null,
                "布尔掩码只接受可由低一位生成的常量");
        }
        var vector = new Variable(Storage.Vec(1), 1);
        var duplicate = new Intrinsic("vdup.32", [Expr.C(0x3f800000, 32)], 128);
        var vectorPattern = InlineConstructors.Create(method, signature with { Parameters = [] }, Function(
            new Define(4, vector, duplicate), Field(self, new Use(vector, 128)), Base(self) with { Kind = CallKind.Tail }));
        var vectorCaller = Function(new Call(0, CallKind.Direct, Expr.C(100, 64)),
            Field(new Use(created, 64), ScalarVectorNarrowing.RepeatedConstant(duplicate)!), Base(new Use(created, 64)), new Return(20));
        a.True(vectorPattern is not null && InlineConstructors.Find(vectorPattern, vectorCaller, vectorCaller.EntryBlock, 0, created) is not null,
            "构造模板与调用点使用相同的向量复制位片");
        vectorCaller.EntryBlock.Statements[1] = Field(new Use(created, 64), Expr.C(0, 128));
        a.True(vectorPattern is not null && InlineConstructors.Find(vectorPattern, vectorCaller, vectorCaller.EntryBlock, 0, created) is null,
            "向量初始化的位型必须匹配");
        return a.Finish("inline-constructors");
    }
}
