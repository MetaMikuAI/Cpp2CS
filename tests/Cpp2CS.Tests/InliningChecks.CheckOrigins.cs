using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Pipeline;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Tests;
internal static partial class InliningChecks
{
    private sealed class OriginRuntimeMap(RuntimeFunction function) : IRuntimeFunctionMap
    { public RuntimeFunction? Find(CallTarget target) => target is ImageFunction { EntryOffset: 20 } ? function : null; }
    private static void CheckOriginChecks(Assertions checks)
    {
        foreach (var operation in new[] { "ThrowNullReference", "ThrowBounds", "ThrowDivideByZero", "ThrowArrayTypeMismatch", "ThrowManaged" })
        {
            var f = new Fixture();
            var catalog = RuntimeFunctionCatalog.Select(f.Spec.Layout.UnityVersion, f.Spec.Layout.Triple, f.Spec.Layout.DataModel);
            // 固定数组类型不符抛出有语义登记，当前函数目录只登记异常工厂加 ThrowManaged。
            var runtime = operation == "ThrowArrayTypeMismatch"
                ? catalog.Functions.First(r => r.Operation.Name == "ThrowNullReference") with { Operation = RuntimeOperations.Get(operation) }
                : catalog.Functions.First(r => r.Operation.Name == operation);
            if (runtime.Operation.FixedThrownException is { } name)
            {
                var exception = new TypeDef { Index = f.Program.Types.Count, Assembly = "mscorlib.dll", Namespace = "System", Name = name[7..], Token = 0x02000040,
                    Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false, Size = 24, BaseType = f.Types.Object };
                ((List<TypeDef>)f.Program.Types).Add(exception);
                var corlib = f.Program.Assemblies.Single(a => a.Name == "mscorlib.dll"); corlib.Types = [.. corlib.Types, exception];
                f.Method(exception, ".ctor", true, false, []);
            }
            var types = new ManagedTypes(f.Program, f.Types.Layouts, 8);
            var array = new ArrayRef(f.Types.Object, 1);
            bool bounds = operation == "ThrowBounds", divide = operation == "ThrowDivideByZero", business = operation == "ThrowManaged";
            var method = f.Method(f.Caller, "CheckOrigin", true, true, bounds ? [array, f.Integer] : [divide ? f.Integer : f.Types.Object]);
            var terms = new TermTable(); var entry = new BlockIdentity(); var pass = new BlockIdentity(); var fail = new BlockIdentity();
            var b = new FunctionBuilder(terms, entry, 64, new(terms.Atom(new RootAtom(AddressRoot.Frame), 64)));
            var value = terms.Atom(new EntryAtom(new(SlotKind.Integer)), 64); var index = terms.Atom(new EntryAtom(new(SlotKind.Integer, 1)), 64);
            b.Inputs.Add(new(new(SlotKind.Integer), value)); if (bounds) b.Inputs.Add(new(new(SlotKind.Integer, 1), index));
            var input = divide ? terms.Slice(value, 0, 32) : value;
            Term condition = terms.Apply(new CoreOperator(CoreOperation.Equal), 1, input, terms.Constant(0, input.Width));
            var statements = new List<Statement>();
            if (bounds)
            {
                var id = new ReadIdentity(); var length = terms.Atom(new ResultAtom(id), 32);
                var address = terms.Apply(new CoreOperator(CoreOperation.Add), 64, value, terms.Constant(f.Spec.Layout.Field("Il2CppArray", "max_length").ByteOffset, 64));
                statements.Add(new MemoryRead(id, address, 32, length));
                condition = terms.Apply(new CoreOperator(CoreOperation.UnsignedLess), 1, terms.Slice(index, 0, 32), length);
            }
            if (business)
            {
                b.Blocks.Add(new(entry, [], [new Call(new(), new ImageFunction(20), [new(new(SlotKind.Integer), value), new(new(SlotKind.Integer, 1), terms.Constant(0, 64))], [], true)], new Unreachable()));
            }
            else
            {
                b.Blocks.Add(new(entry, [], statements.ToImmutableArray(), new Branch(condition, bounds ? pass : fail, bounds ? fail : pass)));
                b.Blocks.Add(new(pass, [], [], new Return([])));
                b.Blocks.Add(new(fail, [], [new Call(new(), new ImageFunction(20), [], [], true)], new Unreachable()));
            }
            var calls = new CallNamingQuery(f.Binder, new NamingChecks.Map([]), new OriginRuntimeMap(runtime), catalog);
            var result = new IntegerLowering(b.Freeze(), MethodRef.Open(method), f.Binder, types, calls: calls, effects: new ManagedCallEffects(calls), spec: f.Spec).Run();
            var thrown = result.Body?.Blocks.SelectMany(b => b.Statements).OfType<ManagedThrow>().SingleOrDefault();
            checks.True(thrown is not null && (business ? thrown.CheckOrigins.Count == 0 : thrown.CheckOrigins is [{ Kind: var kind }] && kind == operation),
                "目录抛出保留种类，业务抛出无标记：" + operation + " " + result.Failure);
            if (!business && thrown is not null)
                checks.True(operation == "ThrowArrayTypeMismatch" ? thrown.CheckOrigins[0].Inputs.Count == 0 : thrown.CheckOrigins[0].Inputs.Count > 0,
                    "被检查值来自公共查询，未知时不补造：" + operation);
        }
        var source = new ArgumentValue(42, new Fixture().Types.Object, 64);
        var marker = new ManagedThrow(0, source) { CheckOrigins = [new("registered-check", source, [new("value", source)])] };
        int visited = 0;
        var ordinary = (ManagedThrow)ManagedValues.Map(marker, v => { visited++; return v; });
        checks.True(visited == 1 && ReferenceEquals(ordinary.CheckOrigins, marker.CheckOrigins), "默认语句映射只处理 IL 求值，检查来源不参与物化");
        var mapped = (ManagedThrow)ManagedValues.Map(marker, v => v == source ? new ConstantValue(1, v.Type, v.Width) : v, includeChecks: true);
        checks.True(mapped.CheckOrigins[0].FailureCondition is ConstantValue { Bits: 1 } && mapped.CheckOrigins[0].Inputs[0].Value is ConstantValue { Bits: 1 }, "语句映射保留并更新检查来源");
    }
}
