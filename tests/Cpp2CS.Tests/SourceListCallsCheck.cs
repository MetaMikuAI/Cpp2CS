using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class SourceListCallsCheck
{
    [Command("source-list-calls", "List 添加的旧长度与异常状态边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var list = types.CorlibDefinition("System.Collections.Generic.List")!;
        var owner = new DefinitionRef(list, [types.Object]);
        var subject = new TypeDef { Index = -1, Assembly = "Tests.dll", Namespace = "Tests", Name = "Subject", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var method = new MethodRef(new MethodDef { Index = -1, Owner = subject, Name = "Append", Token = 0,
            Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1 }, [], []);
        var receiver = new ArgumentValue(0, owner, 64);
        var item = new ArgumentValue(1, types.Object, 64);
        LocalValue Local(int id, TypeRef type, int width) => new(new(Storage.Temp(id), 1), type, width);
        var count = Local(0, types.Int32, 32); var array = Local(1, new ArrayRef(types.Object, 1), 64);
        var state = Local(2, types.Object, 64);
        var other = new ArgumentValue(2, new DefinitionRef(subject, []), 64);
        var otherField = new FieldValue(other, new(new FieldDef { Index = -1, Owner = subject, Name = "Count",
            Type = types.Int32, Attributes = FieldAttributes.Public, Offset = 16 }, other.Type), types.Int32, 32);
        FieldValue Field(string name) => new(receiver, new(list.Fields.Single(f => f.Name == name), owner),
            name == "_items" ? array.Type : types.Int32, name == "_items" ? 64 : 32);
        ManagedValue Increment(ManagedValue value) => new BinaryValue(BinOp.Add, value, new ConstantValue(1, types.Int32, 32), types.Int32, 32);
        ManagedAssignment State(ulong address, ulong bits = 0) => new(address, state, new ConstantValue(bits, types.Object, 64));
        var resize = new MethodRef(list.Methods.Single(m => m.Name == "AddWithResize"), owner.Arguments, []);
        var a = new Assertions();
        foreach (var mode in new[] { "valid", "mutated-count", "changed-state", "late-state", "different-handler" })
        {
            var prefix = new List<ManagedStatement> { new ManagedAssignment(0, count, Field("_size")),
                new ManagedStore(1, otherField, count) };
            if (mode == "mutated-count") prefix.Add(new ManagedStore(2, Field("_size"), new ConstantValue(0, types.Int32, 32)));
            prefix.Add(new ManagedAssignment(3, array, Field("_items")));
            prefix.Add(new ManagedStore(4, Field("_version"), Increment(Field("_version"))));
            if (mode != "late-state") prefix.Add(State(5));
            prefix.Add(new ManagedBranch(6, new ComparisonValue(Cond.Ult, count, new ArrayLengthValue(array, types.Int32, 32), types.Boolean), new(16, []), new(32, [])));
            var original = new ManagedBody(method, [new(0, prefix), new(16, [
                new ManagedStore(16, Field("_size"), Increment(count)), new ManagedStore(17, new ArrayElementValue(array, count, types.Object, 64), item),
                State(18), new ManagedJump(19, new(48, []))]), new(32, [State(32, mode == "changed-state" ? 1UL : 0UL),
                new ManagedCall(33, new(resize, receiver, [item], false), null, false), new ManagedJump(34, new(48, []))]),
                new(48, [new ManagedReturn(48, null)]), new(64, [new ManagedReturn(64, state)])])
            { Regions = [new(mode == "different-handler" ? [0, 16] : [0, 16, 32], 64, [64], null, ManagedRegionKind.Catch)] };
            var rewritten = SourceListCalls.Rewrite(original, types, (_, _) => { });
            var calls = rewritten.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Where(c => c.Invocation.Method.Method.Name == "Add").ToArray();
            a.Equal(mode == "valid" ? 1 : 0, calls.Length, mode);
            if (mode != "valid") continue;
            var statements = rewritten.Blocks[0].Statements;
            a.True(statements.OfType<ManagedAssignment>().Any(s => s.Target == count) && statements.Contains(prefix[1]), "旧长度及其他对象的写入保留");
            a.True(statements.TakeWhile(s => s != calls[0]).OfType<ManagedAssignment>().Any(s => s.Target == state), "异常状态先于添加调用写入");
            a.True(rewritten.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Count(s => s.Target == state) == 2,
                "保留正常路径状态拷贝，未执行的慢分支被删除");
        }
        return a.Finish("source-list-calls");
    }
}
