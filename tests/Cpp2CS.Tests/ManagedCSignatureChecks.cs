using System.Reflection;
using Cpp2CS.Model;
using Cpp2CS.Native.Abi;
using Cpp2CS.Runtime;

namespace Cpp2CS.Tests;

internal static class ManagedCSignatureChecks
{
    public const string Command = "managed-c-signature";
    public static int Run()
    {
        var a = new Assertions();
        var layouts = new Layouts();
        var builder = new ManagedCSignatureBuilder(layouts);
        var integer = new DefinitionRef(Definition("Int32",true),[]);
        var floating = new DefinitionRef(Definition("Double",true),[]);
        var owner = Definition("Owner",false);
        var valueOwner = Definition("Value",true);
        var value = new DefinitionRef(valueOwner,[]);
        var fields = Enumerable.Range(0,3).Select(i=>new FieldDef
        {
            Index=i,Owner=valueOwner,Name="Field"+i,Type=floating,Attributes=FieldAttributes.Public,Offset=i*8,
        }).ToArray();
        valueOwner.Fields=fields;
        layouts.Items[value]=new TypeLayout
        {
            Type=value,ObjectHeaderSize=24,InstanceSize=48,ActualSize=48,MinimumAlignment=8,HasReferences=false,
            Fields=fields.Select((f,i)=>new FieldSlot(f,floating,24+i*8)).ToArray(),Statics=[],StaticSize=0,ThreadStatics=[],FromMetadata=true,
        };
        MethodDef Method(TypeDef declaring, bool isStatic, TypeRef result, params ParameterDef[] parameters) => new()
        {
            Index=0,Owner=declaring,Name="Apply",Token=0,Attributes=isStatic ? MethodAttributes.Static : MethodAttributes.Public,
            ImplAttributes=0,Slot=-1,ReturnType=result,Parameters=parameters,
        };
        ParameterDef Parameter(TypeRef type, ParameterAttributes attributes=0) => new("arg",type,attributes,null,false);
        var m=Method(owner,true,integer,Parameter(integer),Parameter(floating));
        var signature=builder.Build(new(m,[],[])).Value!;
        a.True(signature.ThisIndex is null && signature.ParameterIndices.SequenceEqual([0,1])
            && signature.MethodInformationIndex==2 && signature.Signature.Parameters.SequenceEqual(new CType[] {new CInteger(32),new CFloat(64),new CPointer(64)})
            && signature.Signature.ReturnType==new CInteger(32),"静态方法的形参、返回和隐藏信息");
        foreach (var declaring in new[] {owner,valueOwner})
        {
            signature=builder.Build(new(Method(declaring,false,new PrimitiveRef("void"),Parameter(integer)),[],[])).Value!;
            a.True(signature.ThisIndex==0 && signature.ParameterIndices.SequenceEqual([1]) && signature.MethodInformationIndex==2
                && signature.Signature.Parameters[0]==new CPointer(64),"引用或值类型 this 均为指针");
        }
        m=Method(owner,true,value,Parameter(value),Parameter(new ByRefRef(integer)),Parameter(new ByRefRef(value),ParameterAttributes.Out),
            Parameter(new ArrayRef(integer,1)),Parameter(new PointerRef(integer)));
        signature=builder.Build(new(m,[],[])).Value!;
        a.True(signature.Signature.ReturnType is CAggregate {Size:24,Alignment:8,Fields.Length:3} aggregate
            && aggregate.Fields.Select(f=>f.Offset).SequenceEqual([0,8,16]),"结构体返回按布局扣除对象头");
        a.True(signature.Signature.Parameters[0] is CAggregate {Size:24}
            && signature.Signature.Parameters.Skip(1).All(t=>t==new CPointer(64)),"值参数按值，ref/out/数组/指针和方法信息为指针");
        var generic=Definition("Generic",true);
        generic.GenericParameters=[new(){Name="T",Position=0,Attributes=0}];
        var genericType=new DefinitionRef(generic,[integer]);
        layouts.Items[genericType]=new TypeLayout
        {
            Type=genericType,ObjectHeaderSize=16,InstanceSize=20,ActualSize=20,MinimumAlignment=4,HasReferences=false,
            Fields=[new(new(){Index=0,Owner=generic,Name="Value",Type=new GenericParameterRef("T",false,0),Attributes=0,Offset=0},integer,16)],
            Statics=[],StaticSize=0,ThreadStatics=[],FromMetadata=false,
        };
        m=Method(generic,false,new GenericParameterRef("U",true,0),Parameter(new GenericParameterRef("T",false,0)),Parameter(genericType));
        m.GenericParameters=[new(){Name="U",Position=0,Attributes=0}];
        var closed=new MethodRef(m,[integer],[floating]);
        signature=builder.Build(closed).Value!;
        a.True(signature.Signature.Parameters[1]==new CInteger(32) && signature.Signature.ReturnType==new CFloat(64)
            && signature.Signature.Parameters[2] is CAggregate {Size:4},"类与方法泛型实参封闭后推导");
        a.True(builder.Build(MethodRef.Open(m)) is {Value:null,Problem.Length:>0},"开放泛型失败");
        a.True(builder.Build(closed,sharedCode:true) is {Value:null,Problem.Length:>0},"共享入口需要见证");
        a.True(builder.Build(new(Method(owner,true,new DefinitionRef(Definition("Missing",true),[])),[],[]))
            is {Value:null,Problem.Length:>0},"缺少布局失败");
        var emptyOwner = Definition("Empty", true, defaultSize: false);
        var empty = new DefinitionRef(emptyOwner, []);
        layouts.Items[empty] = new TypeLayout
        {
            Type = empty, ObjectHeaderSize = 16, InstanceSize = 17, ActualSize = 17, MinimumAlignment = 1, HasReferences = false,
            Fields = [], Statics = [], StaticSize = 0, ThreadStatics = [], FromMetadata = true,
        };
        signature = builder.Build(new(Method(owner, true, new PrimitiveRef("void"), Parameter(empty), Parameter(integer)), [], [])).Value!;
        a.True(signature.Signature.Parameters[0] is CAggregate { Size: 1, Fields: [{ Offset: 0, Type: CArray { Count: 1, Element: CInteger { Bits: 8 } } }] },
            "空结构体带生成器的填充字节");
        var passed = new Cpp2CS.Targets.X64.Abi.SysV().Classify(signature.Signature).Assignment!;
        a.True(passed.Parameters[0].Pieces is [{ Slot: { Kind: Cpp2CS.Native.SlotKind.Integer, Position: 0 }, Length: 1 }]
            && passed.Parameters[1].Pieces is [{ Slot: { Kind: Cpp2CS.Native.SlotKind.Integer, Position: 1 } }],
            "空结构体在 SysV 下占一个整数槽，后面的实参顺延");
        var sizedOwner = Definition("Sized", true, defaultSize: false);
        var sized = new DefinitionRef(sizedOwner, []);
        var sizedField = new FieldDef { Index = 0, Owner = sizedOwner, Name = "Field", Type = floating, Attributes = FieldAttributes.Public, Offset = 0 };
        sizedOwner.Fields = [sizedField];
        layouts.Items[sized] = new TypeLayout
        {
            Type = sized, ObjectHeaderSize = 16, InstanceSize = 32, ActualSize = 32, MinimumAlignment = 8, HasReferences = false,
            Fields = [new(sizedField, floating, 16)], Statics = [], StaticSize = 0, ThreadStatics = [], FromMetadata = true,
        };
        a.True(builder.Build(new(Method(owner, true, new PrimitiveRef("void"), Parameter(sized)), [], []))
            is { Value: null, Problem.Length: > 0 }, "显式大小且有字段的值类型明确失败");
        return a.Finish("托管 C 层签名");
    }
    private static TypeDef Definition(string name,bool value,bool? defaultSize=true) => new()
    {
        Index=0,Assembly="mscorlib.dll",Namespace="System",Name=name,Token=0,Attributes=TypeAttributes.Public,IsValueType=value,IsEnum=false,
        ClassSizeIsDefault=defaultSize,
    };
    private sealed class Layouts : ITypeLayouts
    {
        public Dictionary<DefinitionRef,TypeLayout> Items {get;}=[];
        public TypeLayout? Of(DefinitionRef type)=>Items.GetValueOrDefault(type);
        public (int Size,int Alignment)? TrySizeAndAlignment(TypeRef type)=>type is DefinitionRef d && Of(d) is {} layout ? (layout.ValueSize,layout.MinimumAlignment) : null;
        public (int Size,int Alignment) SizeAndAlignment(TypeRef type)=>TrySizeAndAlignment(type) ?? throw new InvalidOperationException("缺少测试布局");
    }
}
