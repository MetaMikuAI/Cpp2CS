using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Mono.Cecil;
using SR = System.Reflection;

namespace Cpp2CS.Tests;

public static class BufferRecoveryCheck
{
    public struct Large { public long A; public long B; public long C; }
    public struct ReferenceLarge { public object? A; public object? B; public object? C; }
    public struct BoundsValue { public float A; public float B; public float C; public float D; public float E; public float F; }
    public sealed class Source
    {
        public int Calls;
        public BoundsValue Read() { Calls++; return new() { A = Calls, B = -Calls, C = 3, D = 4, E = 5, F = 6 }; }
    }

    public static int Run(string binary, string metadata)
    {
        var session = new RecoverySession(ModelCheck.Load(binary, metadata));
        var types = session.Types;
        var owner = new TypeDef { Index = -1, Assembly = "BufferChecks.dll", Namespace = "Checks", Name = "Harness", Token = 0,
            Attributes = SR.TypeAttributes.Public, IsValueType = false, IsEnum = false };
        DefinitionRef Structure(string name, TypeRef element)
        {
            var definition = new TypeDef { Index = -1, Assembly = "BufferChecks.dll", Namespace = "Checks", Name = name, Token = 0,
                Attributes = SR.TypeAttributes.Public | SR.TypeAttributes.SequentialLayout, IsValueType = true, IsEnum = false, Size = 24 };
            definition.Fields = new[] { "A", "B", "C" }.Select((n, i) => new FieldDef { Index = -1, Owner = definition, Name = n,
                Type = element, Offset = i * 8, Attributes = SR.FieldAttributes.Public, Token = 0 }).ToArray();
            return new(definition, []);
        }
        var large = Structure(nameof(Large), types.Int64);
        var references = Structure(nameof(ReferenceLarge), types.Object);
        MethodRef Method(string name, TypeRef result, params TypeRef[] parameters) => new(new MethodDef
        {
            Index = -1, Owner = owner, Name = name, Token = 0, Slot = -1, Attributes = SR.MethodAttributes.Public | SR.MethodAttributes.Static,
            ImplAttributes = SR.MethodImplAttributes.IL, ReturnType = result,
            Parameters = parameters.Select((t, i) => new ParameterDef("p" + i, t, 0, null, false)).ToArray(),
        }, [], []);
        var input = new Use(new Variable(Storage.Gpr(0), 0), 64);
        var output = new Use(new Variable(Storage.Gpr(8), 0), 64);
        Expr Add(Expr address, int offset) => address is FrameAddress frame ? new FrameAddress(frame.Offset + offset)
            : offset == 0 ? address : new Binary(BinOp.Add, address, Expr.C((ulong)offset, 64), 64);
        Stmt[] Copy(Expr source, Expr destination, bool overlap = false) =>
        [
            new Define(0x1004, new Variable(Storage.Vec(0), 1), new Load(source, 128)),
            new Define(0x1008, new Variable(Storage.Gpr(2), 1), new Load(Add(source, 16), 64)),
            new Store(0x100c, Add(destination, overlap ? 8 : 16), new Use(new Variable(Storage.Gpr(2), 1), 64)),
            new Store(0x1010, destination, new Use(new Variable(Storage.Vec(0), 1), 128)),
        ];
        PreparedMethod Prepare(MethodRef method, params Stmt[] statements)
        {
            var function = Graph(new Block(0x1000) { Statements = [.. statements] });
            return new(method, session.Abi.ClassifyReturn(method.Method.ReturnType, out _), function, null, []);
        }
        var echo = Method("Echo", large, large);
        var complete = Prepare(echo, [.. Copy(input, output), new Return(0x1014) { Buffer = output }]);
        Require(BufferInitialization.Check(complete.Function, complete.Return, types, _ => null).Count == 0, "完整写回");
        var missing = Prepare(echo, new Store(0x1000, output, Expr.C(0, 64)), new Return(0x1004) { Buffer = output });
        Require(BufferInitialization.Check(missing.Function, missing.Return, types, _ => null).Count > 0, "不能用 InitLocals 补齐漏写");
        var outside = Prepare(echo, [.. Copy(input, output), new Store(0x1014, Add(output, 24), Expr.C(0, 64)), new Return(0x1018) { Buffer = output }]);
        Require(BufferInitialization.Check(outside.Function, outside.Return, types, _ => null).Count > 0, "返回缓冲区越界写入必须拒绝");
        var earlyRead = Prepare(echo, [new Define(0x1000, new Variable(Storage.Temp(0), 1), new Load(output, 64)),
            .. Copy(input, output), new Return(0x1014) { Buffer = output }]);
        Require(BufferInitialization.Check(earlyRead.Function, earlyRead.Return, types, _ => null).Count > 0, "先读后写不能通过");
        var escaped = Prepare(echo, [new Call(0x1000, CallKind.Direct, Expr.C(0x8000, 64)) { Sources = [Storage.Gpr(0)], Arguments = [output] },
            .. Copy(input, output), new Return(0x1014) { Buffer = output }]);
        Require(BufferInitialization.Check(escaped.Function, escaped.Return, types, _ => null).Count > 0, "未知调用不能取得返回缓冲区地址");
        var overlapping = Prepare(echo, [.. Copy(input, output, true), new Return(0x1014) { Buffer = output }]);
        Require(TypedCopies.Recover(overlapping.Function, new ValueRecovery(session, overlapping), types).Count == 0, "重叠写入不能当作整值复制");
        var interleaved = Copy(input, output).ToList();
        interleaved.Insert(2, new Call(0x100a, CallKind.Direct, Expr.C(0x8000, 64)));
        var interrupted = Prepare(echo, [.. interleaved, new Return(0x1014) { Buffer = output }]);
        Require(TypedCopies.Recover(interrupted.Function, new ValueRecovery(session, interrupted), types).Count == 0, "未知副作用不能跨越复制区间");
        var readAfterWrite = Copy(input, output);
        var reordered = Prepare(echo, readAfterWrite[0], readAfterWrite[3], readAfterWrite[1], readAfterWrite[2], new Return(0x1014) { Buffer = output });
        Require(TypedCopies.Recover(reordered.Function, new ValueRecovery(session, reordered), types).Count == 0, "交错读写不能改成先读完再写");

        MachineFunction Branch(bool both) => Graph(
            new Block(0x1000) { Statements = [new Branch(0x1000, Expr.C(1, 1), 0x2000, 0x3000)] },
            new Block(0x2000) { Statements = [new Store(0x2000, output, Expr.C(0, 128)), new Store(0x2004, Add(output, 16), Expr.C(0, 64)), new Jump(0x2008, 0x4000)] },
            new Block(0x3000) { Statements = both ? [new Store(0x3000, output, Expr.C(0, 128)), new Store(0x3004, Add(output, 16), Expr.C(0, 64)), new Jump(0x3008, 0x4000)] : [new Jump(0x3008, 0x4000)] },
            new Block(0x4000) { Statements = [new Return(0x4000) { Buffer = output }] });
        Require(BufferInitialization.Check(Branch(true), complete.Return, types, _ => null).Count == 0, "两条路径都写满");
        Require(BufferInitialization.Check(Branch(false), complete.Return, types, _ => null).Count > 0, "单边写入不能覆盖汇合");
        var loop = Graph(new Block(0x1000) { Statements = [new Jump(0x1000, 0x2000)] },
            new Block(0x2000) { Statements = [new Define(0x2000, new Variable(Storage.Temp(0), 1), new Load(output, 64)),
                new Store(0x2004, output, Expr.C(0, 128)), new Store(0x2008, Add(output, 16), Expr.C(0, 64)), new Branch(0x200c, Expr.C(1, 1), 0x2000, 0x3000)] },
            new Block(0x3000) { Statements = [new Return(0x3000) { Buffer = output }] });
        Require(BufferInitialization.Check(loop, complete.Return, types, _ => null).Count > 0, "回边写入不能掩盖首轮未初始化读取");

        var nativeGetter = session.Model.Code[0x56cb728].Single().Method;
        var bounds = nativeGetter.Method.ReturnType;
        var nativeOwner = nativeGetter.DeclaringType;
        var nativeShape = session.Abi.Classify(nativeGetter, out _)!;
        Require(nativeShape.Return is { Passing: Passing.Indirect } && types.Size(bounds) == 24, "真实 Bounds 返回约定");
        var frame = new FrameAddress(-32);
        var call = new Call(0x1000, CallKind.Direct, Expr.C(0x56cb728, 64)) { Sources = [Storage.Gpr(0), Storage.Gpr(8)], Arguments = [input, frame] };
        var secondCall = call with { Address = 0x1014 };
        var caller = Prepare(Method("Called", bounds, nativeOwner), [call, .. Copy(frame, output), secondCall, new Return(0x1018) { Buffer = output }]);
        var directCall = call with { Arguments = [input, output] };
        var direct = Prepare(Method("DirectCalled", bounds, nativeOwner), directCall, new Return(0x1004) { Buffer = output });
        var tailCall = directCall with { Kind = CallKind.Tail };
        var tail = Prepare(Method("TailCalled", bounds, nativeOwner), tailCall);
        var wrongTail = Prepare(Method("WrongTail", bounds, nativeOwner), call with { Kind = CallKind.Tail });
        Require(BufferInitialization.Check(wrongTail.Function, wrongTail.Return, types, _ => nativeShape).Count > 0, "尾调用必须转交入口返回缓冲区");
        var aliased = call with { Sources = [Storage.Gpr(0), Storage.Gpr(8)], Arguments = [frame, frame] };
        var aliasedShape = new AbiSignature(null, [new AbiValue(bounds, Passing.Indirect, [new AbiPiece(Storage.Gpr(0), 64, 0)])], null, nativeShape.Return);
        Require(new StackObjects(Graph(new Block(0x1000) { Statements = [aliased] }), types, _ => aliasedShape).Problems.Count > 0,
            "同一调用中的输入先读取，返回写入不能补齐未初始化输入");

        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("BufferChecks", new Version(1, 0)), "BufferChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Harness", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(host);
        TypeReference Reference(TypeRef type) => module.ImportReference(type == large ? typeof(Large) : type == references ? typeof(ReferenceLarge)
            : type == bounds ? typeof(BoundsValue) : type == nativeOwner ? typeof(Source) : throw new NotSupportedException(type.ToString()));
        var emitter = new BodyEmitter(types, Reference, f => throw new NotSupportedException(f.ToString()),
            m => m == nativeGetter ? module.ImportReference(typeof(Source).GetMethod(nameof(Source.Read))) : throw new NotSupportedException(m.ToString()));
        void Emit(PreparedMethod prepared)
        {
            var recovered = BodyRecovery.Recover(session, prepared);
            Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
            var method = new MethodDefinition(prepared.Method.Method.Name, MethodAttributes.Public | MethodAttributes.Static, Reference(prepared.Method.Method.ReturnType));
            foreach (var parameter in prepared.Method.Method.Parameters) method.Parameters.Add(new ParameterDefinition(Reference(parameter.Type)));
            host.Methods.Add(method);
            var problem = emitter.Emit(recovered.Body!, method);
            Require(problem is null, problem ?? "CIL 输出");
        }
        Emit(complete);
        Emit(Prepare(Method("ReferenceEcho", references, references), [.. Copy(input, output), new Return(0x1014) { Buffer = output }]));
        Emit(caller);
        Emit(direct);
        Emit(tail);
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Harness", true)!;
        foreach (var a in new[] { long.MinValue, -1L, 0L, 1L, long.MaxValue })
        {
            var value = new Large { A = a, B = ~a, C = 0x1122334455667788 };
            var actual = (Large)runtime.GetMethod("Echo")!.Invoke(null, [value])!;
            Require(actual.A == value.A && actual.B == value.B && actual.C == value.C, "间接参数和返回的三字段复制");
        }
        var shared = new object();
        var referenceResult = (ReferenceLarge)runtime.GetMethod("ReferenceEcho")!.Invoke(null, [new ReferenceLarge { A = shared, B = null, C = shared }])!;
        Require(ReferenceEquals(referenceResult.A, shared) && referenceResult.B is null && ReferenceEquals(referenceResult.C, shared), "结构体复制保留引用身份");
        var source = new Source();
        var snapshot = (BoundsValue)runtime.GetMethod("Called")!.Invoke(null, [source])!;
        Require(source.Calls == 2 && snapshot.A == 1 && snapshot.B == -1 && snapshot.F == 6, "后续调用覆盖栈缓冲区不能改变已经复制的返回值");
        foreach (var name in new[] { "DirectCalled", "TailCalled" })
        {
            var single = new Source();
            var value = (BoundsValue)runtime.GetMethod(name)!.Invoke(null, [single])!;
            Require(single.Calls == 1 && value.A == 1 && value.F == 6, "直接和尾调用的返回缓冲区转交");
        }
        Console.WriteLine("缓冲区检查通过：间接参数与返回、引用复制、重复调用后的快照、分支和循环初始化，以及漏写、重叠、交错读写、未知用途拒绝");
        Native(session);
        return 0;
    }

    private static void Native(RecoverySession session)
    {
        var getter = session.Model.Code[0x56cb728].Single().Method;
        var setter = session.Model.Code[0x56cb73c].Single().Method;
        Require(getter.ToString() == "Sekai.Mysekai.FieldCameraModel.get_LookAtBounds" && setter.ToString() == "Sekai.Mysekai.FieldCameraModel.set_LookAtBounds", "真实方法身份");
        var bounds = getter.Method.ReturnType;
        var path = session.Types.FieldPath(getter.DeclaringType, 0x58, 24)!;
        Require(path.Count == 1 && path[0].Type == bounds, "Bounds 字段布局");
        using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("NativeBufferChecks", new Version(1, 0)), "NativeBufferChecks", ModuleKind.Dll);
        var module = assembly.MainModule;
        var host = new TypeDefinition("Checks", "Camera", TypeAttributes.Public, module.TypeSystem.Object);
        module.Types.Add(host);
        var field = new FieldDefinition("Data", FieldAttributes.Public, module.ImportReference(typeof(BoundsValue)));
        host.Fields.Add(field);
        TypeReference Reference(TypeRef type) => type == getter.DeclaringType ? host : type == bounds ? module.ImportReference(typeof(BoundsValue))
            : ManagedTypes.IsVoid(type) ? module.TypeSystem.Void : throw new NotSupportedException(type.ToString());
        var emitter = new BodyEmitter(session.Types, Reference, f => f.Field == path[0].Field.Field ? field : throw new NotSupportedException(f.ToString()), m => throw new NotSupportedException(m.ToString()));
        foreach (var (address, method) in new[] { (0x56cb728UL, getter), (0x56cb73cUL, setter) })
        {
            var prepared = session.Analyze(method, address);
            var recovered = BodyRecovery.Recover(session, prepared);
            Require(recovered.Body is not null, string.Join("; ", recovered.Problems));
            var destination = new MethodDefinition(method.Method.Name, MethodAttributes.Public, Reference(method.Method.ReturnType));
            foreach (var parameter in method.Method.Parameters) destination.Parameters.Add(new ParameterDefinition(Reference(parameter.Type)));
            host.Methods.Add(destination);
            var problem = emitter.Emit(recovered.Body!, destination);
            Require(problem is null, problem ?? "真实 CIL");
        }
        using var stream = new MemoryStream(); assembly.Write(stream);
        var runtime = SR.Assembly.Load(stream.ToArray()).GetType("Checks.Camera", true)!;
        var instance = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(runtime);
        foreach (var bits in new[] { 0, int.MinValue, 1, 0x7f800000, unchecked((int)0xff800000), 0x7fc12345 })
        {
            var input = new BoundsValue { A = BitConverter.Int32BitsToSingle(bits), B = 2, C = 3, D = 4, E = 5, F = BitConverter.Int32BitsToSingle(~bits) };
            runtime.GetMethod(setter.Method.Name)!.Invoke(instance, [input]);
            var output = (BoundsValue)runtime.GetMethod(getter.Method.Name)!.Invoke(instance, null)!;
            Require(BitConverter.SingleToInt32Bits(output.A) == bits && BitConverter.SingleToInt32Bits(output.F) == ~bits
                && output.B == 2 && output.C == 3 && output.D == 4 && output.E == 5, "真实 Bounds getter/setter 保留全部字段和浮点位型");
        }
        Console.WriteLine("真实 FieldCameraModel.LookAtBounds getter/setter 恢复方法体执行通过：24 字节整体复制、间接参数与返回、浮点边界；替代布局，无外部业务实现，未验证 Unity 运行时");
    }

    private static MachineFunction Graph(params Block[] blocks)
    {
        foreach (var block in blocks)
        {
            ulong[] targets = block.Statements.LastOrDefault() switch { Branch b => [b.Target, b.Fallthrough], Jump j => [j.Target], _ => [] };
            foreach (var target in targets)
            {
                var next = blocks.Single(b => b.Start == target);
                block.Successors.Add(next); next.Predecessors.Add(block);
            }
        }
        var function = new MachineFunction { Entry = blocks[0].Start, Range = new FunctionRange(0x1000, 0x5000, BoundaryEvidence.SymbolCandidate, "缓冲区检查"), Blocks = [.. blocks] };
        function.Renumber();
        return function;
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
