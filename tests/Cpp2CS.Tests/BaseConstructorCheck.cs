using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class BaseConstructorCheck
{
    [Command("base-constructors", "内联基类构造的参数、初始化顺序与副作用边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var index = 0;
        TypeDef Type(string name) => new() { Index = index++, Assembly = "Constructor.Tests.dll", Namespace = "Tests", Name = name,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false };
        var nothing = new PrimitiveRef("Void"); var integer = new PrimitiveRef("I4");
        MethodDef Constructor(TypeDef owner, params ParameterDef[] parameters) => new() { Index = index++, Owner = owner, Name = ".ctor",
            Token = 0, Attributes = MethodAttributes.Public, ImplAttributes = 0, Slot = -1, ReturnType = nothing, Parameters = parameters };
        var root = Type("Root"); var parent = Type("Parent"); var child = Type("Child");
        var rootType = new DefinitionRef(root, []); var parentType = new DefinitionRef(parent, []); var childType = new DefinitionRef(child, []);
        parent.BaseType = rootType; child.BaseType = parentType;
        var rootConstructor = new MethodRef(Constructor(root), [], []);
        var baseConstructor = new MethodRef(Constructor(parent, new ParameterDef("value", integer, 0, null, false)), [], []);
        var childConstructor = new MethodRef(Constructor(child, new ParameterDef("value", integer, 0, null, false)), [], []);
        var baseField = new FieldDef { Index = index++, Owner = parent, Name = "value", Type = integer, Offset = 16, Attributes = FieldAttributes.Family };
        var ownField = new FieldDef { Index = index++, Owner = child, Name = "own", Type = integer, Offset = 20, Attributes = FieldAttributes.Public };
        var self = new ArgumentValue(-1, childType, 64); var baseSelf = new ArgumentValue(-1, parentType, 64);
        var argument = new ArgumentValue(0, integer, 32); var one = new ConstantValue(1, integer, 32);
        ManagedStore Store(ManagedValue receiver, FieldDef field, ManagedValue value) => new(1,
            new FieldValue(receiver, new(field, new DefinitionRef(field.Owner, [])), integer, 32), value);
        ManagedCall Call(ManagedValue receiver, bool tail = false) => new(2, new(rootConstructor, receiver, [], false), null, tail);
        ManagedBody Body(MethodRef method, params ManagedStatement[] statements) => new(method, [new(0, statements)]);
        var pattern = Body(baseConstructor, Call(baseSelf), Store(baseSelf, baseField, argument), new ManagedReturn(3, null));
        var before = Body(childConstructor, Store(self, ownField, one), Call(self), Store(self, baseField, argument), new ManagedReturn(3, null));
        var after = BaseConstructorCalls.Rewrite(before, [pattern]);
        var statements = after.Blocks[0].Statements;
        var a = new Assertions();
        a.True(!ReferenceEquals(before, after), "完整基类方法体被认回");
        a.True(statements[0] is ManagedStore store && store.Target is FieldValue field && field.Field.Field == ownField,
            "本类初始化仍在基类调用前");
        a.True(statements[1] is ManagedCall { Inlined: true } call && call.Invocation.Method == baseConstructor
            && call.Invocation.Receiver == self && call.Invocation.Arguments.SequenceEqual([argument]), "保留 this 与实际参数，标记透明执行");
        var changedValue = Body(childConstructor, Call(self), Store(self, baseField, one), new ManagedReturn(3, null));
        a.True(BaseConstructorCalls.Rewrite(changedValue, [pattern]).Blocks[0].Statements[0] is ManagedCall constantCall
            && constantCall.Invocation.Arguments.SequenceEqual([one]), "常量实参同样按数据绑定");
        var sideEffect = Body(childConstructor, Call(self), Store(self, ownField, one), Store(self, baseField, argument), new ManagedReturn(3, null));
        a.True(ReferenceEquals(sideEffect, BaseConstructorCalls.Rewrite(sideEffect, [pattern])), "不跨过额外字段写入拼接基类方法体");
        var incomplete = Body(childConstructor, Call(self), new ManagedReturn(3, null));
        a.True(ReferenceEquals(incomplete, BaseConstructorCalls.Rewrite(incomplete, [pattern])), "缺少基类字段写入时不补造构造调用");
        var defaultBase = new MethodRef(Constructor(parent), [], []);
        var tailPattern = Body(defaultBase, Store(baseSelf, baseField, one), Call(baseSelf, true));
        var tailCaller = Body(childConstructor, Store(self, ownField, one), Store(self, baseField, one), Call(self, true));
        var tailResult = BaseConstructorCalls.Rewrite(tailCaller, [tailPattern]);
        a.True(tailResult.Blocks[0].Statements is [ManagedStore, ManagedCall { Inlined: true, Tail: false }, ManagedReturn],
            "尾调用基类构造恢复成普通 base 调用后返回");
        var different = Body(defaultBase, Store(baseSelf, baseField, new ConstantValue(2, integer, 32)), Call(baseSelf, true));
        a.True(ReferenceEquals(tailCaller, BaseConstructorCalls.Rewrite(tailCaller, [different])), "字段常量不同不能视为同一基类构造");
        a.True(before.Blocks[0].Statements.Count == 4, "输入方法体保持不变");
        return a.Finish("base-constructors");
    }
}
