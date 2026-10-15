using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class StackRecoveryCheck
{
    public struct Pair { public int A; public int B; }
    public static void Mutate(ref int first, ref int second) { first = unchecked(first + 1); second = unchecked(second * 2); }
    public static void MutatePair(ref Pair pair, ref int member) { pair.A = unchecked(pair.A + 1); member = unchecked(member + pair.A); }

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        var pairDefinition = new TypeDef { Index = -1, Assembly = "Synthetic.dll", Namespace = "Synthetic", Name = "Pair", Token = 0,
            Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false, Size = 8 };
        var pair = new DefinitionRef(pairDefinition, []);
        FieldDef Field(string name, int offset) => new() { Index = -1, Owner = pairDefinition, Name = name, Type = types.Int32,
            Offset = offset, Attributes = SR.FieldAttributes.Public, Token = 0 };
        var fieldA = Field("A", 0); var fieldB = Field("B", 4);
        pairDefinition.Fields = [fieldA, fieldB];
        var frame = new FrameAddress(-16);
        var memberFrame = new FrameAddress(-12);
        AbiSignature Shape(params TypeRef[] elements) => new(null,
            elements.Select((type, i) => new AbiValue(new ByRefRef(type), Passing.Registers, [new AbiPiece(Storage.Gpr(i), 64, 0)])).ToArray(), null, null);
        Call Call(ulong address, params Expr[] arguments) => new(address, CallKind.Direct, Expr.C(0x8000, 64))
            { Sources = arguments.Select((_, i) => Storage.Gpr(i)).ToArray(), Arguments = arguments };
        Store Write(long offset, int width = 32) => new(0x1000, new FrameAddress(offset), Expr.C(1, width));
        StackObjects Check(MachineFunction function, Func<Call, AbiSignature?> shape, bool accepted)
        {
            var stack = new StackObjects(function, types, shape);
            Require((stack.Problems.Count == 0) == accepted, string.Join("; ", stack.Problems));
            return stack;
        }
        MachineFunction Single(params Stmt[] statements) => Graph(new Block(0x1000) { Statements = [.. statements, new Return(0x1100)] });
        var scalar = Check(Single(Write(-16), Call(0x1004, frame, frame)), _ => Shape(types.Int32, types.Int32), true);
        Require(scalar.Objects.Count == 1 && scalar.Address(-16, types.Int32)!.Target == scalar.Location(-16, 32), "同地址参数共享一个局部存储");
        Check(Single(Call(0x1004, frame)), _ => Shape(types.Int32), false);
        Check(Single(Write(-16, 16), Call(0x1004, frame)), _ => Shape(types.Int32), false);
        Check(Single(new Store(0x1000, frame, new Load(frame, 32)), Call(0x1004, frame)), _ => Shape(types.Int32), false);
        Check(Single(Write(-16), Call(0x1004, frame), Call(0x1008, frame)), c => c.Address == 0x1004 ? Shape(types.Int32) : Shape(types.Single), false);
        Check(Single(Write(-16, 64), Call(0x1004, frame, memberFrame)), _ => Shape(types.Int64, types.Int32), false);
        Check(Single(Write(-16), Call(0x1004, frame), new Return(0x1008) { Value = frame }), _ => Shape(types.Int32), false);
        Check(Single(Write(-16), Call(0x1004, frame), Call(0x1008, frame)), c => c.Address == 0x1004 ? Shape(types.Int32) : null, false);
        Check(Single(Write(-16), Call(0x1004, frame)), _ => Shape(types.Int32) with
            { Return = new AbiValue(new ByRefRef(types.Int32), Passing.Registers, [new AbiPiece(Storage.Gpr(0), 64, 0)]) }, false);
        var composite = Check(Single(Write(-16), Write(-12), Call(0x1008, frame, memberFrame)), _ => Shape(pair, types.Int32), true);
        Require(composite.Objects.Count == 1 && composite.Address(-12, types.Int32)!.Target is FieldValue { Field.Field: var f } && f == fieldB,
            "结构体整体与内部字段引用共享存储");
        Check(Single(Write(-16), Call(0x1004, frame)), _ => Shape(pair), false);

        MachineFunction Branch(bool initializeBoth) => Graph(
            new Block(0x1000) { Statements = [new Branch(0x1000, new Compare(Cond.Ne, new Use(new Variable(Storage.Gpr(0), 0), 32), Expr.C(0, 32)), 0x2000, 0x3000)] },
            new Block(0x2000) { Statements = [Write(-16), new Jump(0x2004, 0x4000)] },
            new Block(0x3000) { Statements = initializeBoth ? [Write(-16), new Jump(0x3004, 0x4000)] : [new Jump(0x3004, 0x4000)] },
            new Block(0x4000) { Statements = [Call(0x4000, frame), new Return(0x4004)] });
        Check(Branch(true), _ => Shape(types.Int32), true);
        Check(Branch(false), _ => Shape(types.Int32), false);
        Check(Graph(new Block(0x1000) { Statements = [new Jump(0x1000, 0x2000)] },
            new Block(0x2000) { Statements = [Call(0x2000, frame), Write(-16), new Branch(0x2004, Expr.C(1, 1), 0x2000, 0x3000)] },
            new Block(0x3000) { Statements = [new Return(0x3000)] }), _ => Shape(types.Int32), false);

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("StackChecks", new Version(1, 0)), "StackChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var harness = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(harness);
        var owner = new TypeDef { Index = -2, Assembly = "Synthetic.dll", Namespace = "Synthetic", Name = "Harness", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        MethodRef Method(string name, TypeRef result, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result,
            Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
        }, [], []);
        TypeReference Reference(TypeRef type) => type == pair ? module.ImportReference(typeof(Pair)) : type is ByRefRef reference
            ? new ByReferenceType(Reference(reference.Element)) : module.ImportReference(Type.GetType("System." + ManagedTypes.PrimitiveName(type), true)!);
        var mutate = Method(nameof(Mutate), types.Void, new ByRefRef(types.Int32), new ByRefRef(types.Int32));
        var mutatePair = Method(nameof(MutatePair), types.Void, new ByRefRef(pair), new ByRefRef(types.Int32));
        var methods = new Dictionary<MethodDef, MethodReference>
        {
            [mutate.Method] = module.ImportReference(typeof(StackRecoveryCheck).GetMethod(nameof(Mutate))),
            [mutatePair.Method] = module.ImportReference(typeof(StackRecoveryCheck).GetMethod(nameof(MutatePair))),
        };
        var emitter = new BodyEmitter(types, Reference, f => module.ImportReference(typeof(Pair).GetField(f.Field.Name)), m => methods[m.Method]);
        void Emit(string name, params ManagedStatement[] statements)
        {
            var definition = Method(name, types.Int32, types.Int32);
            var actual = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Int32);
            actual.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32)); harness.Methods.Add(actual);
            Require(emitter.Emit(new ManagedBody(definition, [new ManagedBlock(0x1000, statements)]), actual) is null, name + " 的输出");
        }
        var input = new ArgumentValue(0, "value", types.Int32, 32);
        Emit("ScalarAlias", new ManagedStore(0x1000, scalar.Location(-16, 32)!, input),
            new ManagedCall(0x1004, new(mutate, null, [scalar.Address(-16)!, scalar.Address(-16)!]), null, false),
            new ManagedReturn(0x1008, scalar.Location(-16, 32)!));
        Emit("StructAlias", new ManagedStore(0x1000, composite.Location(-16, 32)!, input),
            new ManagedStore(0x1004, composite.Location(-12, 32)!, new ConstantValue(3, types.Int32, 32)),
            new ManagedCall(0x1008, new(mutatePair, null, [composite.Address(-16)!, composite.Address(-12, types.Int32)!]), null, false),
            new ManagedReturn(0x100c, composite.Location(-12, 32)!));
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
        foreach (var value in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            Require((int)runtime.GetMethod("ScalarAlias")!.Invoke(null, [value])! == unchecked((value + 1) * 2), "同地址引用参数不能变成两个副本");
            Require((int)runtime.GetMethod("StructAlias")!.Invoke(null, [value])! == unchecked(value + 4), "结构体与字段别名共同更新原局部存储");
        }
        Console.WriteLine("栈对象检查通过：签名约束、标量/结构体别名执行、字段引用、分支初始化、循环首轮、类型冲突和地址逃逸拒绝");
        StackNativeCheck.Run(session);
        return 0;
    }

    private static MachineFunction Graph(params Block[] blocks)
    {
        foreach (var block in blocks)
        {
            ulong[] targets = block.Statements.Last() switch { Branch b => [b.Target, b.Fallthrough], Jump j => [j.Target], _ => [] };
            foreach (var target in targets)
            {
                var next = blocks.Single(b => b.Start == target);
                block.Successors.Add(next); next.Predecessors.Add(block);
            }
        }
        var result = new MachineFunction { Entry = blocks[0].Start, Range = new FunctionRange(0x1000, 0x5000, BoundaryEvidence.SymbolCandidate, "栈对象合成检查"), Blocks = [.. blocks] };
        result.Renumber();
        return result;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
