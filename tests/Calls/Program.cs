using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Metadata;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Cpp2CS.Semantics;

var root = Path.GetFullPath(args[1]);
var catalog = JsonSerializer.Deserialize<Catalog>(File.ReadAllText(Path.Combine(root, "artifacts/first/metadata.json")), Catalog.Json)!;
var stamina = catalog.Type("Sekai.Mysekai.StaminaData");
var ctor = stamina.Methods.Single(m => m.Name == ".ctor");
var sum = stamina.Methods.Single(m => m.Name == "get_SumStamina");
var wrapper = new Method("Execute", "0x6000001", "0x1000", "System.Int32", true, null,
    [new("value", stamina.Name, null), new("a", "System.Int32", null), new("b", "System.Int32", null), new("c", "System.Int32", null)],
    "test-prototype");
var wrapperType = new TypeModel("CallTests.Entry", "CallTests_Entry_o", true, true, [], [wrapper]);
catalog = catalog with { Types = [..catalog.Types, wrapperType] };
var targets = new CallTargets(catalog);
if (targets.Resolve(ctor.Address).Method.Token != ctor.Token) throw new Exception("direct call identity");
var duplicate = new TypeModel("CallTests.Other", "Other_o", true, true, [], [sum with { Token = "0x6000020" }]);
var ambiguous = new CallTargets(catalog with { Types = [..catalog.Types, duplicate] });
if (ambiguous.Resolve(sum.Address, new(catalog.Assembly, stamina.Name, sum.Token)).Owner != stamina)
    throw new Exception("explicit identity");
if (args[0] == "ambiguous") { ambiguous.Resolve(sum.Address); throw new Exception("accepted ambiguous call"); }

var aggregate = new NativeType(stamina.NativeName, 12, "aggregate", false, null);
var integer = new NativeType("int32_t", 4, "integer", true, null);
var pointer = new NativeType(stamina.NativeName + " *", 8, "pointer", false, stamina.NativeName);
var info = new NativeType("const MethodInfo *", 8, "pointer", false, "const MethodInfo");
var variables = new[] { new Variable(0,"value",aggregate,true), new(1,"a",integer,true), new(2,"b",integer,true), new(3,"c",integer,true), new(4,"method",info,true),new(5,"i",integer,false),new(6,"total",integer,false) };
var nodes = new List<Dictionary<string,object?>>();
int Add(string op, NativeType? type = null, params (string Key,object? Value)[] fields)
{
    int id = nodes.Count;
    var n = new Dictionary<string,object?> { ["id"]=id,["op"]=op,["ea"]="0x1000",["label"]=-1 };
    if (type is not null) n["nativeType"] = type;
    foreach (var f in fields) n[f.Key]=f.Value;
    nodes.Add(n);
    return id;
}
int Variable(int i) => Add("var",variables[i].NativeType,("variable",i));
int NullInfo() => Add("num",info,("number","0"));
int Receiver() => Add("ref",pointer,("x",Variable(0)));
int ctorTarget = Add("obj",null,("object",ctor.Address));
int call = Add("call",new("void",0,"void",false,null),("x",ctorTarget),
    ("arguments",new[] { Receiver(),Variable(1),Variable(2),Variable(3),NullInfo() }));
if (args[0] == "bad-arity") nodes[call]["arguments"] = new[] { Receiver(),NullInfo() };
int statement = Add("expr",null,("expression",call));
int sumTarget = Add("obj",null,("object",sum.Address));
int get = Add("call",integer,("x",sumTarget),("arguments",new[] { Receiver(),NullInfo() }));
int ret = Add("return",null,("expression",get));
int block = Add("block",null,("items",new[] { statement,ret }));
var output = Path.Combine(root,"artifacts/calls");
Directory.CreateDirectory(output);
var input = Path.Combine(output,"1000.json");
File.WriteAllText(input,JsonSerializer.Serialize(new
{
    decompiled=true,input_sha256=catalog.BinarySha256,address=wrapper.Address,prototype_applied=wrapper.NativePrototype,
    warnings=Array.Empty<object>(),structured=new { schema=1,root=block,nodes,variables,arguments=new[] {0,1,2,3,4} }
},Catalog.Json));
var wrapperBody = new Recover(catalog,wrapperType,wrapper,new Ctree(input,catalog,wrapper)).Run();
var dependencies = Dependencies.In(wrapperBody);
if (dependencies.Length != 2) throw new Exception("constructor and getter dependencies");
var bodies = catalog.Types.Where(t => t != wrapperType).ToDictionary(t=>t.Name,t=>t.Methods.Select(m=>
    new Recover(catalog,t,m,new Ctree(Path.Combine(args[2],m.Address[2..]+".json"),catalog,m)).Run()).ToArray());
bodies.Add(wrapperType.Name,[wrapperBody]);
int Number(int n) => Add("num",integer,("number",unchecked((ulong)(long)n).ToString()));
int Expression(int n) => Add("expr",null,("expression",n));
int Assign(int variable,int source) => Expression(Add("asg",integer,("x",Variable(variable)),("y",source)));
int Increment() => Expression(Add("postinc",integer,("x",Variable(5))));
int Is(int n) => Add("eq",new("bool",1,"bool",false,null),("x",Variable(5)),("y",Number(n)));
int skip = Add("if",null,("condition",Is(3)),("then",Add("block",null,("items",new[] {Increment(),Add("continue")}))),("else",null));
int add = Expression(Add("asgadd",integer,("x",Variable(6)),("y",Variable(5))));
int stop = Add("if",null,("condition",Is(8)),("then",Add("break")),("else",null));
int limit = Add("band",integer,("x",Variable(1)),("y",Number(31)));
int test = Add("slt",new("bool",1,"bool",false,null),("x",Variable(5)),("y",limit));
int loop = Add("while",null,("condition",test),("body",Add("block",null,("items",new[] {skip,add,stop,Increment()}))));
int flowReturn = Add("return",null,("expression",Add("add",integer,("x",get),("y",Variable(6)))));
nodes[flowReturn]["label"] = 7;
int jump = Add("goto",null,("target",7));
int unreachableGuard = Add("if",null,("condition",Number(0)),("then",flowReturn),("else",null));
int flowRoot = Add("block",null,("items",new[] {statement,Assign(5,Number(0)),Assign(6,Number(0)),loop,jump,unreachableGuard}));
var flowMethod = wrapper with { Name="ExecuteFlow",Token="0x6000002",Address="0x1004" };
wrapperType = wrapperType with { Methods=[wrapper,flowMethod] };
catalog = catalog with { Types=catalog.Types.Select(t=>t.Name==wrapperType.Name?wrapperType:t).ToArray() };
var flowInput = Path.Combine(output,"1004.json");
File.WriteAllText(flowInput,JsonSerializer.Serialize(new
{
    decompiled=true,input_sha256=catalog.BinarySha256,address=flowMethod.Address,prototype_applied=flowMethod.NativePrototype,
    warnings=Array.Empty<object>(),structured=new { schema=1,root=flowRoot,nodes,variables,arguments=new[] {0,1,2,3,4} }
},Catalog.Json));
bodies[wrapperType.Name] = [wrapperBody,new Recover(catalog,wrapperType,flowMethod,new Ctree(flowInput,catalog,flowMethod)).Run()];
void AddFlow(string name,string token,string address,int node)
{
    var method = wrapper with { Name=name,Token=token,Address=address };
    wrapperType = wrapperType with { Methods=[..wrapperType.Methods,method] };
    catalog = catalog with { Types=catalog.Types.Select(t=>t.Name==wrapperType.Name?wrapperType:t).ToArray() };
    var file = Path.Combine(output,address[2..]+".json");
    File.WriteAllText(file,JsonSerializer.Serialize(new
    {
        decompiled=true,input_sha256=catalog.BinarySha256,address,prototype_applied=method.NativePrototype,
        warnings=Array.Empty<object>(),structured=new { schema=1,root=node,nodes,variables,arguments=new[] {0,1,2,3,4} }
    },Catalog.Json));
    bodies[wrapperType.Name] = [..bodies[wrapperType.Name],new Recover(catalog,wrapperType,method,new Ctree(file,catalog,method)).Run()];
}
int forSkip = Add("if",null,("condition",Is(3)),("then",Add("continue")),("else",null));
int forLoop = Add("for",null,("init",Add("asg",integer,("x",Variable(5)),("y",Number(0)))),("condition",test),
    ("step",Add("postinc",integer,("x",Variable(5)))),("body",Add("block",null,("items",new[] {forSkip,add,stop}))));
AddFlow("ExecuteFor","0x6000003","0x1008",Add("block",null,("items",new[] {statement,Assign(6,Number(0)),forLoop,flowReturn})));
int Plus(int n) => Expression(Add("asgadd",integer,("x",Variable(6)),("y",Number(n))));
int switchNode = Add("switch",null,("expression",Add("band",integer,("x",Variable(1)),("y",Number(3)))),
    ("cases",new[]
    {
        new { values=new ulong[] {0},body=Add("block",null,("items",new[] {Plus(100),Add("break")})) },
        new { values=new ulong[] {1},body=Add("block",null,("items",new[] {Plus(10)})) },
        new { values=new ulong[] {2},body=Add("block",null,("items",new[] {Plus(20),Add("break")})) },
        new { values=Array.Empty<ulong>(),body=Add("block",null,("items",new[] {Plus(30)})) }
    }));
AddFlow("ExecuteSwitch","0x6000004","0x100c",Add("block",null,("items",new[] {statement,Assign(6,Number(0)),switchNode,flowReturn})));
int doBody = Add("block",null,("items",new[] {Plus(1),Increment()}));
int doLoop = Add("do",null,("condition",test),("body",doBody));
AddFlow("ExecuteDo","0x6000005","0x1010",Add("block",null,("items",new[] {statement,Assign(5,Number(0)),Assign(6,Number(0)),doLoop,flowReturn})));
if (args[0] == "missing-body") bodies[stamina.Name] = bodies[stamina.Name].Where(b=>b.Method != ctor).ToArray();
Dependencies.Verify(catalog,bodies);
File.WriteAllText(Path.Combine(output,"Recovered.cs"),new CSharp(catalog).Generate(bodies));
Console.WriteLine("PASS: typed calls, explicit identity, dependency closure, byref initializer emitted");
