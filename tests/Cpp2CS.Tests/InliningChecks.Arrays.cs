using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Pipeline;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class InliningChecks
{
    private sealed class ArrayRuntimeMap(RuntimeFunctionCatalog catalog) : IRuntimeFunctionMap
    {
        public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 20 }
            ? catalog.Functions.First(f => f.Operation.Name == "ThrowNullReference") : null;
    }
    private static void ArrayEventAccessorChecks(Assertions checks)
    {
        foreach (bool reference in new[] { false, true })
        foreach (var mode in new[] { "Normal", "Reversed", "PrivateContextRead", "LoweredBoolean", "ImpliedItemCheck", "MissingItemCheck", "ExtraCheck", "DifferentCheckedValue", "DifferentCheckPosition", "DifferentArray", "DifferentIndex", "DifferentValue", "OutsideAccess", "BusinessThrow", "OtherUse" })
        {
            if (!reference && (mode is "ImpliedItemCheck" or "MissingItemCheck")) continue;
            bool itemCheck = mode is "ImpliedItemCheck" or "MissingItemCheck";
            var f = new Fixture();
            var elementType = reference ? (TypeRef)f.Types.Object : f.Integer;
            var arrayType = new ArrayRef(elementType, 1);
            var countDef = new FieldDef { Index = 2, Owner = f.Owner, Name = "Count", Type = f.Integer, Attributes = FieldAttributes.Private, Offset = 32, Token = 0x04000003 };
            var itemsDef = new FieldDef { Index = 3, Owner = f.Owner, Name = "Items", Type = arrayType, Attributes = FieldAttributes.Private, Offset = 24, Token = 0x04000004 };
            f.Owner.Fields = [.. f.Owner.Fields, countDef, itemsDef];
            ((List<FieldDef>)f.Program.Fields).AddRange([countDef, itemsDef]);
            var count = new FieldRef(countDef, f.OwnerType); var items = new FieldRef(itemsDef, f.OwnerType);
            var exceptionType = new TypeDef { Index = f.Program.Types.Count, Assembly = "mscorlib.dll", Namespace = "System", Name = "NullReferenceException", Token = 0x02000040,
                Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, Size = 24, BaseType = f.Types.Object };
            ((List<TypeDef>)f.Program.Types).Add(exceptionType);
            var corlib = f.Program.Assemblies.Single(a => a.Name == "mscorlib.dll"); corlib.Types = [.. corlib.Types, exceptionType];
            var exception = f.Method(exceptionType, ".ctor", true, false, []);
            var types = new ManagedTypes(f.Program, f.Types.Layouts, 8);
            var outer = f.Method(f.Owner, "Append", true, false, [elementType]);
            var slow = f.Method(f.Owner, "Grow", true, false, [elementType]);
            var caller = f.Method(f.Caller, "UseArray", mode != "OtherUse", true, [f.OwnerType, elementType, arrayType]);
            var self = new ArgumentValue(-1, f.OwnerType, 64); var item = new ArgumentValue(0, elementType, reference ? 64 : 32);
            var version = new FieldValue(self, f.Field, f.Integer, 32); var size = new FieldValue(self, count, f.Integer, 32);
            var array = new FieldValue(self, items, arrayType, 64);
            var oldVersion = new LocalValue(new(0), f.Integer, 32); var oldArray = new LocalValue(new(1), arrayType, 64); var oldSize = new LocalValue(new(2), f.Integer, 32);
            var length = new LocalValue(new(3), f.Integer, 32);
            var nullCondition = new ComparisonValue(ComparisonKind.Equal, oldArray, new ConstantValue(0, arrayType, 64), f.Types.Boolean);
            var thrown = new ManagedThrow(4, new NewObjectValue(MethodRef.Open(exception), [], 64))
            { CheckOrigins = mode == "BusinessThrow" ? [] : [new("ThrowNullReference", nullCondition, [new("value", mode == "DifferentCheckedValue" ? item : oldArray)])] };
            var itemNull = new ComparisonValue(ComparisonKind.Equal, item, new ConstantValue(0, elementType, item.Width), f.Types.Boolean);
            if (itemCheck) thrown = thrown with { CheckOrigins = [.. thrown.CheckOrigins, new("ThrowNullReference", itemNull, [new("value", item)])] };
            ManagedValue Increment(ManagedValue value) => new BinaryValue(BinaryOperator.Add, value, new ConstantValue(1, f.Integer, 32), f.Integer, 32);
            var within = new ComparisonValue(ComparisonKind.UnsignedLess, oldSize, length, f.Types.Boolean);
            ManagedValue capacityTest = mode == "LoweredBoolean" ? new BinaryValue(BinaryOperator.And,
                new UnaryValue(UnaryOperator.Not, within, f.Integer, 32), new ConstantValue(1, f.Integer, 32), f.Integer, 32) : within;
            var template = new ManagedBody(MethodRef.Open(outer), [
                new(0, [new ManagedAssignment(0, oldVersion, version), new ManagedAssignment(0, oldArray, array), new ManagedStore(1, version, Increment(oldVersion)),
                    new ManagedBranch(2, nullCondition, new(4, []), new(itemCheck ? 5UL : 1UL, []))]),
                new(1, [new ManagedAssignment(2, oldSize, size), new ManagedAssignment(2, length, new ArrayLengthValue(oldArray, f.Integer, 32)),
                    new ManagedBranch(3, capacityTest, new(mode == "LoweredBoolean" ? 3UL : 2UL, []), new(mode == "LoweredBoolean" ? 2UL : 3UL, []))]),
                new(2, [new ManagedStore(3, size, Increment(oldSize)), new ManagedStore(3, new ArrayElementValue(oldArray,
                    new ConversionValue(ConversionKind.SignExtend, oldSize, f.Types.Integer(64, true), 64), elementType, item.Width), item), new ManagedReturn(3, null)]),
                new(3, [new ManagedCall(3, new(MethodRef.Open(slow), self, [item], false), null), new ManagedReturn(3, null)]), new(4, [thrown])]);
            if (itemCheck) template = template with { Blocks = [.. template.Blocks, new(5, [new ManagedBranch(2, itemNull, new(4, []), new(1, []))])] };
            var summary = AccessorTemplates.Read(template);
            checks.True(mode == "BusinessThrow" ? summary.Template is null : summary.Template?.Events?.Paths.Count == 2,
                $"数组和检查事件提取 {reference}/{mode}: {summary.Failure}");
            if (reference && mode == "Normal")
            {
                var checkedTemplate = template with { Blocks = template.Blocks.Select(block => block with
                {
                    Statements = block.Statements.Select(statement => statement is ManagedStore { Target: ArrayElementValue } store
                        ? store with { AccessChecks = [new("CheckArrayElementType", [new("array", oldArray), new("value", item)])] } : statement).ToArray(),
                }).ToArray() };
                checks.True(AccessorTemplates.Read(checkedTemplate) is { Status: AccessorTemplateStatus.NotTemplate, Failure.Message: var reason }
                    && reason.Contains("吸收检查", StringComparison.Ordinal), "带吸收类型检查的来源不能当作无检查模板");
            }
            var t = new TermTable(); var entry = new BlockIdentity(); var capacity = new BlockIdentity(); var fast = new BlockIdentity(); var slowBlock = new BlockIdentity();
            var bad = new BlockIdentity(); var join = new BlockIdentity(); var extra = new BlockIdentity(); var afterSize = new BlockIdentity(); var final = new BlockIdentity();
            var functionEntry = mode == "ImpliedItemCheck" ? new BlockIdentity() : entry;
            var b = new FunctionBuilder(t, functionEntry, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var receiver = t.Atom(new EntryAtom(new(SlotKind.Integer)), 64); var argument = t.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64); var other = t.Atom(new EntryAtom(new(SlotKind.Integer, 2)), 64);
            b.Inputs.Add(new(new(SlotKind.Integer), receiver)); b.Inputs.Add(new(new(SlotKind.Integer, 1), argument)); b.Inputs.Add(new(new(SlotKind.Integer, 2), other));
            Term Add(Term root, int n) => t.Apply(new CoreOperator(CoreOperation.Add), root.Width, root, t.Constant(n, root.Width));
            MemoryRead Load(Term root, int offset, int width) { var id = new ReadIdentity(); return new(id, Add(root, offset), width, t.Atom(new ResultAtom(id), width)); }
            var vr = Load(receiver, 16, 32); var ar = Load(receiver, 24, 64); var sr = Load(receiver, 32, 32); var lr = Load(ar.Result, (int)f.Spec.Layout.Field("Il2CppArray", "max_length").ByteOffset, 32);
            var image = t.Atom(new RootAtom(AddressRoot.Image), 64); b.ImageBase = image;
            var information = Load(image, 128, 64);
            var ownerClass = Load(information.Result, (int)f.Spec.Layout.Field("MethodInfo", "klass").ByteOffset, 64);
            var facts = mode == "PrivateContextRead" ? NamingFacts.Empty with
                { Slots = NamingFacts.Empty.Slots.Add(128, Cpp2CS.Kernel.Queries.Outcome<MetadataEntity>.Success(new MethodEntity(MethodRef.Open(outer)))) } : NamingFacts.Empty;
            var increment = new MemoryWrite(new(), Add(receiver, 16), 32, Add(vr.Result, 1));
            Term IsNull(Term value) => t.Apply(new CoreOperator(CoreOperation.Equal), 1, value, t.Constant(0, value.Width));
            bool wrongPosition = mode == "DifferentCheckPosition";
            b.Blocks.Add(new(entry, [], mode == "PrivateContextRead" ? [vr, ar, information, increment] : [vr, ar, increment], wrongPosition ? new Jump(capacity) : new Branch(IsNull(ar.Result), bad, mode == "ExtraCheck" ? extra : capacity)));
            if (mode == "ExtraCheck") b.Blocks.Add(new(extra, [], [], new Branch(IsNull(other), bad, capacity)));
            var condition = t.Apply(new CoreOperator(CoreOperation.UnsignedLess), 1, sr.Result, lr.Result);
            bool reverse = mode == "Reversed"; if (reverse) condition = t.Apply(new CoreOperator(CoreOperation.Not), 1, condition);
            b.Blocks.Add(new(capacity, [], [sr, lr], new Branch(condition, reverse ? slowBlock : fast, reverse ? fast : slowBlock)));
            var sizeWrite = new MemoryWrite(new(), Add(receiver, 32), 32, Add(sr.Result, 1));
            var index = t.Apply(new CoreOperator(CoreOperation.SignExtend), 64, sr.Result); if (mode == "DifferentIndex") index = Add(index, 1);
            var destination = Add(t.Apply(new CoreOperator(CoreOperation.Add), 64, mode == "DifferentArray" ? other : ar.Result,
                t.Apply(new CoreOperator(CoreOperation.Multiply), 64, index, t.Constant(reference ? 8 : 4, 64))), (int)f.Spec.Layout.ArrayDataStart);
            var value = mode == "DifferentValue" ? t.Constant(0, item.Width) : t.Slice(argument, 0, item.Width);
            var store = new MemoryWrite(new(), destination, item.Width, value);
            b.Blocks.Add(new(fast, [], wrongPosition ? [sizeWrite] : [sizeWrite, store], wrongPosition ? new Branch(IsNull(ar.Result), bad, afterSize)
                : mode == "OutsideAccess" ? new Branch(IsNull(other), bad, join) : new Jump(join)));
            if (wrongPosition) b.Blocks.Add(new(afterSize, [], [store], new Jump(join)));
            var invocation = new Call(new(), new ImageFunction(10), [new(new(SlotKind.Integer), receiver), new(new(SlotKind.Integer, 1), argument), new(new(SlotKind.Integer, 2), t.Constant(0, 64))], []);
            b.Blocks.Add(new(slowBlock, [], mode == "PrivateContextRead" ? [ownerClass, invocation] : [invocation], new Jump(join)));
            b.Blocks.Add(new(bad, [], [new Call(new(), new ImageFunction(20), [], [], true)], new Unreachable()));
            b.Blocks.Add(new(join, [], mode == "OutsideAccess" ? [Load(other, (int)f.Spec.Layout.Field("Il2CppArray", "max_length").ByteOffset, 32)] : [], new Jump(final)));
            b.Blocks.Add(new(final, [], [], new Return(mode == "OtherUse" ? [new(new(SlotKind.Integer), t.Concat(sr.Result, t.Constant(0, 32)))] : [])));
            if (mode == "ImpliedItemCheck")
            {
                b.Blocks.Insert(0, new(functionEntry, [], [], new Branch(IsNull(argument), final, entry)));
            }
            var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
            var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([new(MethodRef.Open(slow), BindingEntryKind.Ordinary)]), new ArrayRuntimeMap(catalog), catalog);
            var result = new IntegerLowering(b.Freeze(), MethodRef.Open(caller), f.Binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: f.Spec, names: facts,
                accessors: new(types, new CachedAccessorTemplates(m => m == outer ? template : null))).Run();
            bool positive = mode is "Normal" or "Reversed" or "PrivateContextRead" or "LoweredBoolean" or "ImpliedItemCheck";
            checks.True(positive ? result.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Count(c => c.Inlined && c.Invocation.Method.Method == outer) == 1 : result.Body is null && result.Failure?.Reason.Code.StartsWith("inline.Accessor", StringComparison.Ordinal) == true,
                $"数组写入检查匹配 {reference}/{mode}: {result.Failure}");
            if (positive && result.Body is { } body)
            {
                using var emission = new EmissionFixture(f);
                checks.True(emission.Emitter.Emit([template, body]).Count == 0, $"数组事件输出 CIL {reference}/{mode}");
                string element = reference ? "object" : "int";
                string oldItem = reference ? "new object()" : "13";
                string newItem = reference ? "new object()" : "29";
                using var source = new CompiledSource($$"""
                    public class Owner {
                        private int Value;
                        private int Count;
                        private {{element}}[] Items;
                        public void Append({{element}} item) {
                            Value++; var a = Items; int n = Count;
                            if ((uint)n < (uint)a.Length) { Count = n + 1; a[n] = item; } else Grow(item);
                        }
                        public void Grow({{element}} item) {
                            var next = new {{element}}[Count + 2];
                            for (int i = 0; i < Count; i++) next[i] = Items[i];
                            next[Count] = item; Items = next; Count++;
                        }
                        public static void Expanded(Owner owner, {{element}} item) {
                            owner.Value++; var a = owner.Items; int n = owner.Count;
                            if ((uint)n < (uint)a.Length) { owner.Count = n + 1; a[n] = item; } else owner.Grow(item);
                        }
                        private static int Case(bool enough, bool output) {
                            var old = {{oldItem}}; var item = {{newItem}};
                            var owner = new Owner { Value = 7, Count = 1, Items = new {{element}}[enough ? 3 : 1] };
                            owner.Items[0] = old;
                            if (output) Caller.UseArray(owner, item, null); else Expanded(owner, item);
                            int contents = 0;
                            for (int i = 0; i < owner.Items.Length; i++) {
                                int mark = owner.Items[i] == old ? 3 : owner.Items[i] == item ? 5 : 0;
                                contents = contents * 11 + mark;
                            }
                            return owner.Value * 100000 + owner.Count * 10000 + owner.Items.Length * 1000 + contents;
                        }
                        public static int EnoughReference() => Case(true, false);
                        public static int EnoughOutput() => Case(true, true);
                        public static int GrowReference() => Case(false, false);
                        public static int GrowOutput() => Case(false, true);
                    }
                    public static class Caller { public static void UseArray(Owner value, {{element}} item, {{element}}[] other) { value.Append(item); } }
                    """);
                var output = source.Method("Caller", "UseArray"); output.Body = emission.Method(caller).Body;
                var core = source.Module.TypeSystem.Object.Resolve().Module;
                Mono.Cecil.TypeReference MapType(Mono.Cecil.TypeReference type) => type is Mono.Cecil.ArrayType array
                    ? new Mono.Cecil.ArrayType(MapType(array.ElementType), array.Rank)
                    : source.Module.ImportReference(source.Module.GetType(type.FullName) ?? core.GetType(type.FullName));
                foreach (var local in output.Body.Variables) local.VariableType = MapType(local.VariableType);
                foreach (var instruction in output.Body.Instructions) instruction.Operand = instruction.Operand switch
                {
                    Mono.Cecil.MethodReference method => source.Module.ImportReference((source.Module.GetType(method.DeclaringType.FullName) ?? core.GetType(method.DeclaringType.FullName)).Methods.Single(m => m.FullName == method.FullName)),
                    Mono.Cecil.TypeReference type => MapType(type), Mono.Cecil.ParameterDefinition parameter => output.Parameters[parameter.Index], _ => instruction.Operand,
                };
                foreach (var capacityCase in new[] { "Enough", "Grow" })
                {
                    var comparison = CilComparison.Compare(source.Method("Owner", capacityCase + "Reference"), source.Method("Owner", capacityCase + "Output"), cases: 1);
                    checks.True(comparison.Status == CilComparisonStatus.Match && comparison.CompletedCases == 1,
                        $"数组执行对照版本、大小与全部元素 {reference}/{mode}/{capacityCase}: {comparison}");
                }
            }
        }
    }
}
