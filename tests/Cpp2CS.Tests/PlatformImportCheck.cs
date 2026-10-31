using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Idioms;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class PlatformImportCheck
{
    [Command("platform-import", "导入包装实参、缓存和副作用边界检查", Arguments = "<binary> <metadata> <入口地址…>")]
    public static int Run(string binary, string metadata, string[] entries)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new MethodRecovery(facts, types);
        var abi = new ManagedAbi(facts.Layouts);
        var lifter = new FunctionLifter(facts);
        var rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false, RecoverUnusedInputs = true };
        var skeleton = new Skeleton(facts.Model);
        var a = new Assertions();
        a.True(entries.Length > 0, "指定真实包装入口");
        foreach (var text in entries)
        {
            var entry = System.Convert.ToUInt64(text, 16);
            var method = MethodRef.Open(facts.Model.Methods.Single(m => m.Address == entry));
            Console.WriteLine($"0x{entry:x} {method.Method.Attributes} / {method.Method.ImplAttributes}");
            var result = recovery.Recover(method, entry);
            a.True(result.Declaration == RuntimeDeclarationKind.PlatformInvoke && result.Body is null && result.Holes.Count == 0, "导入与 CIL 方法体分开计数");
            if (result.PlatformImport is not { } imported) continue;
            skeleton.ApplyDeclarations([result]);
            var declaration = skeleton.Method(method.Method);
            a.True(declaration.IsPInvokeImpl && !declaration.HasBody && declaration.IsPreserveSig, "保持 extern PreserveSig");
            a.Equal(imported.Library, declaration.PInvokeInfo.Module.Name, "写出真实库名");
            a.Equal(imported.EntryPoint, declaration.PInvokeInfo.EntryPoint, "写出真实入口");
            var signature = abi.Classify(method, out _)!;
            MachineFunction Function()
            {
                var read = signature.Return is { } ret ? new Read(ret.Pieces[0].Register, ret.Pieces[0].Width) : null;
                var function = lifter.Lift(entry, read).Function;
                rewriter.Run(function);
                return function;
            }
            string? Name(ulong address, ulong length) => length is > 0 and < 1024
                ? System.Text.Encoding.ASCII.GetString(facts.Model.Image.Read(address, (int)length)) : null;
            bool EmptyCache(ulong address) => facts.Model.Image.ReadPointer(address) == 0;
            a.Equal(imported, PlatformImportPattern.Match(Function(), signature, Name, EmptyCache)!, "完整包装复现相同声明");
            a.True(PlatformImportPattern.Match(Function(), signature, Name, _ => false) is null, "缓存必须初始为零");
            void Reject(Action<MachineFunction> mutate, string reason)
            {
                var function = Function();
                mutate(function);
                a.True(PlatformImportPattern.Match(function, signature, Name, EmptyCache) is null, reason);
            }
            Reject(f => f.EntryBlock.Statements.Insert(0, new Store(entry, Expr.C(1, 64), Expr.C(1, 64))), "额外外部写入不能吞掉");
            Reject(f => f.Blocks.Select(b => b.Statements).First(s => s.OfType<Store>().Any(t => t.Value is Const)).RemoveAll(s => s is Store { Value: Const }), "参数结构缺失不能推测");
            Reject(f =>
            {
                var block = f.Blocks.Single(b => b.Statements.OfType<Store>().Any(s => s.Target is Const));
                var index = block.Statements.FindIndex(s => s is Store { Target: Const });
                block.Statements[index] = ((Store)block.Statements[index]) with { Target = Expr.C(1, 64) };
            }, "缓存读取与写回必须同址");
            Reject(f =>
            {
                var block = f.Blocks.Single(b => b.Statements.OfType<Call>().Any(c => c.Kind == CallKind.Indirect));
                var index = block.Statements.FindIndex(s => s is Call);
                block.Statements[index] = ((Call)block.Statements[index]) with { Target = Expr.C(1, 64) };
            }, "调用必须使用缓存与解析结果合流");
            if (signature.Parameters.Length > 0)
                Reject(f =>
                {
                    var block = f.Blocks.Single(b => b.Statements.OfType<Call>().Any(c => c.Kind == CallKind.Indirect));
                    var index = block.Statements.FindIndex(s => s is Call);
                    var call = (Call)block.Statements[index];
                    var arguments = call.Arguments.ToArray();
                    arguments[Array.IndexOf(call.Sources, signature.Parameters[0].Pieces[0].Register)] = Expr.C(0, 64);
                    block.Statements[index] = call with { Arguments = arguments };
                }, "封送或改写参数不能当作原样转调");
            Console.WriteLine($"0x{entry:x} {imported}");
        }
        return a.Finish("platform-import");
    }
}
