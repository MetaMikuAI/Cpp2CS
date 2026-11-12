using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Output;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Lowering;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Tests.Execution;

namespace Cpp2CS.Tests;

internal static partial class LoweringChecks
{
    private static void StateChecks(Assertions checks, ProgramModel primitives)
    {
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var layouts = new FieldLayouts(spec, 8, 8);
        var binder = new MethodBinder(new(layouts), new Aapcs64());
        var definitions = primitives.Types.Where(t => t.Assembly == "mscorlib.dll" && t.Name != "BitConverter").ToList();
        TypeRef Primitive(string name) => new DefinitionRef(definitions.Single(t => t.Name == name), []);
        var owner = new TypeDef { Index = definitions.Count, Assembly = "ReadState.dll", Namespace = "", Name = "ReadState",
            Token = 0x02000001, Attributes = TypeAttributes.Public | TypeAttributes.BeforeFieldInit, IsValueType = false, IsEnum = false,
            Size = 32, PackingSize = 0, ClassSizeIsDefault = true };
        definitions.Add(owner);
        var self = new DefinitionRef(owner, []); var integer = Primitive("Int32");
        var field = new FieldDef { Index = 0, Owner = owner, Name = "Value", Type = integer,
            Offset = (int)spec.Layout.ObjectHeaderSize, Attributes = FieldAttributes.Public, Token = 0x04000001 };
        owner.Fields = [field];
        var methods = new[] { "Join", "Reload", "Bits", "Siblings", "Stack", "StackMissing" }.Select((name, i) => new MethodDef {
            Index = i, Owner = owner, Name = name, Token = (uint)(0x06000001 + i),
            Attributes = MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, ImplAttributes = 0, Slot = -1, ReturnType = integer,
            Parameters = name.StartsWith("Stack", StringComparison.Ordinal)
                ? Enumerable.Range(0, 9).Select(p => new ParameterDef("p" + p, integer, 0, null, false)).ToArray()
                : [new("p", self, 0, null, false), new("c", integer, 0, null, false)] }).ToArray();
        owner.Methods = methods;
        var model = new ProgramModel { MetadataVersion = 0, Types = definitions, Methods = methods, Fields = [field],
            RuntimeTypes = [], MethodSpecs = [], FieldRefs = [], StringLiterals = [],
            Assemblies = definitions.GroupBy(t => t.Assembly).Select(g => new AssemblyDef { Name = g.Key,
                AssemblyName = Path.GetFileNameWithoutExtension(g.Key), Version = new(1, 0), Culture = "", PublicKey = [], Types = g.ToArray() }).ToArray() };
        var types = new ManagedTypes(model, layouts, 8); var skeleton = new Skeleton(model, 16); var emitter = new BodyEmitter(skeleton, types);
        var catalog = RuntimeFunctionCatalog.Select(spec.Layout.UnityVersion, spec.Layout.Triple, spec.Layout.DataModel);
        var calls = new CallNamingQuery(binder, new NamingChecks.Map([]), new NamingChecks.RuntimeMap(), catalog);
        const string text = """
            public class ReadState {
                public int Value;
                public static int Join(ReadState p, int c) { if (c != 0) p.Value = 7; return p.Value; }
                public static int Bits(ReadState p, int c) { if (c != 0) p.Value = 7; return p.Value & 15; }
                public static int Reload(ReadState p, int c) { int old = p.Value; if (c != 0) p.Value = 7; return old + p.Value; }
                public static int Siblings(ReadState p, int c) { if (c != 0) p.Value = 7; if (c != 0) return p.Value; return p.Value; }
                public static int Stack(int p0, int p1, int p2, int p3, int p4, int p5, int p6, int p7, int p8) => p8;
            }
            """;
        using var source = new CompiledSource(text);
        using var tested = new CompiledSource(text);
        foreach (var method in methods)
        {
            var terms = new TermTable(); var entry = new BlockIdentity(); var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
            var builder = new FunctionBuilder(terms, entry, 64, new(frame)) { IncomingArgumentArea = frame };
            Term Input(int slot)
            {
                var value = terms.Atom(new EntryAtom(new(SlotKind.Integer, slot)), 64);
                builder.Inputs.Add(new(new(SlotKind.Integer, slot), value)); return value;
            }
            MemoryRead Read(Term address)
            {
                var id = new ReadIdentity(); return new(id, address, 32, terms.Atom(new ResultAtom(id), 32));
            }
            Return Return(Term value) => new([new(new(SlotKind.Integer), terms.Concat(value, terms.Constant(0, 32)))]);
            if (method.Name.StartsWith("Stack", StringComparison.Ordinal))
            {
                for (int i = 0; i < 8; i++) Input(i);
                var address = method.Name == "Stack" ? frame : terms.Apply(new CoreOperator(CoreOperation.Add), 64, frame, terms.Constant(8, 64));
                var read = Read(address); builder.Blocks.Add(new(entry, [], [read], Return(read.Result)));
            }
            else
            {
                var pointer = Input(0); var condition = terms.Slice(Input(1), 0, 32);
                var address = terms.Apply(new CoreOperator(CoreOperation.Add), 64, pointer, terms.Constant(field.Offset, 64));
                var old = Read(address); var last = Read(address);
                var write = new BlockIdentity(); var skip = new BlockIdentity(); var join = new BlockIdentity();
                builder.Blocks.Add(new(entry, [], method.Name == "Reload" ? [old] : [], new Branch(condition, write, skip)));
                builder.Blocks.Add(new(write, [], [new MemoryWrite(new(), address, 32, terms.Constant(7, 32))], new Jump(join)));
                builder.Blocks.Add(new(skip, [], [], new Jump(join)));
                if (method.Name == "Siblings")
                {
                    var left = new BlockIdentity(); var right = new BlockIdentity(); var other = Read(address);
                    builder.Blocks.Add(new(join, [], [], new Branch(condition, left, right)));
                    builder.Blocks.Add(new(left, [], [last], Return(last.Result)));
                    builder.Blocks.Add(new(right, [], [other], Return(other.Result)));
                }
                else builder.Blocks.Add(new(join, [], [last], Return(method.Name == "Reload"
                    ? terms.Apply(new CoreOperator(CoreOperation.Add), 32, old.Result, last.Result)
                    : method.Name == "Bits" ? terms.Concat(terms.Slice(last.Result, 0, 4), terms.Constant(0, 28)) : last.Result)));
            }
            var result = new IntegerLowering(builder.Freeze(), MethodRef.Open(method), binder, types, calls: calls, spec: spec).Run();
            if (method.Name == "StackMissing")
            {
                var expected = "lowering.State.FrameEntry";
                checks.True(result.Failure?.Reason.Code == expected, method.Name + " 保留未绑定的入口读取：" + result.Failure);
                continue;
            }
            checks.True(result.Body is not null, method.Name + " 状态下降：" + result.Failure);
            if (result.Body is not { } body) continue;
            var problems = emitter.Emit([body]);
            checks.True(problems.Count == 0, method.Name + " 状态 CIL 校验：" + string.Join(';', problems.Values));
            if (problems.Count != 0) continue;
            var emitted = skeleton.Method(method);
            // 编译模块承载写出体；字段与局部类型映回同模块，执行对照只检验方法体。
            var rewritten = tested.Method("ReadState", method.Name); rewritten.Body = emitted.Body;
            foreach (var local in rewritten.Body.Variables) local.VariableType = tested.Module.TypeSystem.Int32;
            foreach (var instruction in rewritten.Body.Instructions)
                if (instruction.Operand is Mono.Cecil.FieldReference member && member.DeclaringType.FullName == "ReadState")
                    instruction.Operand = tested.Module.GetType("ReadState").Fields.Single(f => f.Name == member.Name);
            var comparison = CilComparison.Compare(source.Method("ReadState", method.Name), rewritten);
            checks.True(comparison.Status == CilComparisonStatus.Match, method.Name + " 状态执行对照：" + comparison);
            if (method.Name == "Reload") checks.True(body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
                .Count(a => a.Value is FieldValue) == 2, "写入前后的读取分别在原读取处保存，不共用局部");
            if (method.Name == "Siblings")
            {
                var reads = body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>().Where(a => a.Value is FieldValue).ToArray();
                checks.True(reads.Length == 2 && reads[0].Target == reads[1].Target, "同身份的读取在两条路径各自的原读取点赋值，不在汇合入口补读");
            }
        }
        foreach (var assembly in skeleton.Assemblies) assembly.Dispose();
    }
}
