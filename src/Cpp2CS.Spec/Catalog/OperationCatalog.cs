using System.Collections.Frozen;
using System.Collections.Immutable;

namespace Cpp2CS.Spec.Catalog;

/// <summary>
/// 操作目录。每一项的效果模板来自 il2cpp 对该指令生成的 C++ 与运行时头文件里被调用的辅助函数，
/// 出处写在各项的 Source 里：Translation 是生成代码的写法，Runtime 是头文件（相对 libil2cpp 目录）与符号，
/// Standard 是 ECMA-335 的条目。目录项里没有控制流形态。
/// </summary>
public static class OperationCatalog
{
    private const string Common = "codegen/il2cpp-codegen-common.h";
    private const string Codegen = "codegen/il2cpp-codegen-il2cpp.h";

    private static readonly TemplateValue P0 = new(ValueOp.Operand, [], 0), P1 = new(ValueOp.Operand, [], 1), P2 = new(ValueOp.Operand, [], 2);
    private static TemplateValue S(int step) => new(ValueOp.Step, [], step);
    private static TemplateValue V(ValueOp op, params TemplateValue[] arguments) => new(op, [.. arguments]);
    private static TemplateValue Named(RuntimeFunction function, params TemplateValue[] arguments) => new(ValueOp.Named, [.. arguments], Function: function);
    private static TemplateValue Resize(TemplateValue x, int keep, int to, bool signed) => new(ValueOp.Resize, [x], keep, to, signed ? 1 : 0);
    private static TemplateValue IsNull(TemplateValue x) => V(ValueOp.IsZero, x);
    private static TemplateValue Loaded(TemplateValue x) => V(ValueOp.FromStorage, x);
    private static TemplateValue Stored(TemplateValue x) => V(ValueOp.ToStorage, x);

    private static TemplateStep ThrowIf(TemplateValue condition, ExceptionKind exception) => new(StepKind.ThrowIf, [condition], Exception: exception);
    private static TemplateStep ThrowIfNull(TemplateValue x) => ThrowIf(IsNull(x), ExceptionKind.NullReference);
    private static TemplateStep Read(LocationKind location, params TemplateValue[] @base) => new(StepKind.Read, [.. @base], location);
    private static TemplateStep Write(LocationKind location, TemplateValue value, params TemplateValue[] @base) => new(StepKind.Write, [.. @base, value], location);
    private static TemplateStep Do(StepKind kind, params TemplateValue[] values) => new(kind, [.. values]);

    private static CatalogEntry E(string id, string il, string summary, StackClass[] operands, TemplateStep[] steps, TemplateValue? result,
        ResultKind kind, string translation, string runtime, string standard, bool sameKind = false,
        VariantCondition condition = VariantCondition.None, bool fromSignature = false, int impliedBits = 0) =>
        new(id, il, summary, [.. operands], sameKind, condition, [.. steps], result, kind, new(translation, runtime, "ECMA-335 " + standard))
        { OperandsFromSignature = fromSignature, ImpliedBits = impliedBits };

    private static readonly StackClass[] None = [];
    private static readonly StackClass[] Integers = [StackClass.Integer, StackClass.Integer];
    private static readonly StackClass[] Floats = [StackClass.Float, StackClass.Float];

    private static CatalogEntry Shift(string il, ValueOp op, string symbol, string standard) =>
        E(il, il, "移位量不小于位宽时结果未定义", [StackClass.Integer, StackClass.Int32], [],
            V(ValueOp.Select, V(ValueOp.ShiftInRange, P1, P0), V(op, P0, P1), V(ValueOp.Undefined, P0)), ResultKind.SameAsOperand,
            $"a {symbol} b（移位量由 C# 编译器先与 31 或 63 相与；生成代码不再检查）", "—", standard);

    /// <summary>
    /// 整数的除与余。翻译是 C++ 的运算：被除数为最小值且除数为 −1 时商不可表示，C++ 里除与余都没有定义，
    /// 模板在这里带有定义条件；标准在这个输入上的规定登记为偏差（设计 9.1、16.2）。
    /// </summary>
    private static CatalogEntry Divide(string il, ValueOp op, string symbol, string standard, Deviation deviation) =>
        E(il + ".int", il, "除数为零时抛出；被除数为最小值且除数为 −1 时翻译没有定义（生成代码是 C++ 的运算，没有溢出检查）", Integers,
            [ThrowIf(V(ValueOp.IsZero, P1), ExceptionKind.DivideByZero),
                Do(StepKind.Require, V(ValueOp.Not, V(ValueOp.Both, V(ValueOp.IsMinimum, P0), V(ValueOp.IsAllOnes, P1))))],
            V(op, P0, P1),
            ResultKind.SameAsOperand, $"DivideByZeroCheck(b); a {symbol} b", $"{Codegen}: DivideByZeroCheck", standard, sameKind: true)
            with { Deviations = [deviation] };

    private static CatalogEntry Compare(string il, TemplateValue condition, string symbol, string standard) =>
        E(il + ".int", il, "有符号整数比较后分支", Integers, [Do(StepKind.Branch, condition)], null, ResultKind.None,
            $"if (a {symbol} b) goto IL_xxxx", "—", standard, sameKind: true);

    private static readonly ImmutableArray<CatalogEntry> entries =
    [
        // ---- 数据的搬动：没有效果 ----
        E("ldarg", "ldarg", "形参的值", None, [], V(ValueOp.Argument), ResultKind.Subject, "L_n = ___i_name", "—", "III.3.38 ldarg"),
        E("starg", "starg", "写形参：按形参类型存储", [StackClass.Assignable], [Do(StepKind.StoreArgument, Loaded(Stored(P0)))], null, ResultKind.None,
            "___i_name = v", "—", "III.3.61 starg"),
        E("ldloc", "ldloc", "局部变量的值", None, [], V(ValueOp.Local), ResultKind.Subject, "L_n = V_i", "—", "III.3.43 ldloc"),
        E("stloc", "stloc", "写局部变量：按变量类型存储", [StackClass.Assignable], [Do(StepKind.StoreLocal, Loaded(Stored(P0)))], null, ResultKind.None,
            "V_i = v", "—", "III.3.63 stloc"),
        E("ldc.i4", "ldc.i4", "int32 常量", None, [], new(ValueOp.Immediate, [], 32), ResultKind.Int32, "字面量", "—", "III.3.40 ldc"),
        E("ldnull", "ldnull", "空引用", None, [], V(ValueOp.Null), ResultKind.Object, "NULL", "—", "III.3.45 ldnull"),
        E("pop", "pop", "丢弃栈顶", [StackClass.Any], [], null, ResultKind.None, "（不生成代码）", "—", "III.3.54 pop"),

        // ---- 算术与位运算 ----
        E("add.int", "add", "整数加，回绕", Integers, [], V(ValueOp.Add, P0, P1), ResultKind.SameAsOperand,
            "il2cpp_codegen_add(a, b)", $"{Common}: il2cpp_codegen_add", "III.3.1 add", sameKind: true),
        E("add.float", "add", "浮点加", Floats, [], V(ValueOp.FloatAdd, P0, P1), ResultKind.SameAsOperand,
            "il2cpp_codegen_add(a, b)", $"{Common}: il2cpp_codegen_add", "III.3.1 add", sameKind: true),
        E("sub.int", "sub", "整数减，回绕", Integers, [], V(ValueOp.Sub, P0, P1), ResultKind.SameAsOperand,
            "il2cpp_codegen_subtract(a, b)", $"{Common}: il2cpp_codegen_subtract", "III.3.64 sub", sameKind: true),
        E("sub.float", "sub", "浮点减", Floats, [], V(ValueOp.FloatSubtract, P0, P1), ResultKind.SameAsOperand,
            "il2cpp_codegen_subtract(a, b)", $"{Common}: il2cpp_codegen_subtract", "III.3.64 sub", sameKind: true),
        E("mul.int", "mul", "整数乘，回绕", Integers, [], V(ValueOp.Mul, P0, P1), ResultKind.SameAsOperand,
            "il2cpp_codegen_multiply(a, b)", $"{Common}: il2cpp_codegen_multiply", "III.3.48 mul", sameKind: true),
        E("mul.float", "mul", "浮点乘", Floats, [], V(ValueOp.FloatMultiply, P0, P1), ResultKind.SameAsOperand,
            "il2cpp_codegen_multiply(a, b)", $"{Common}: il2cpp_codegen_multiply", "III.3.48 mul", sameKind: true),
        Divide("div", ValueOp.SignedDivide, "/", "III.3.31 div",
            new("被除数是最小值且除数是 −1", "ECMA-335 III.3.31：结果不能表示时抛出 ArithmeticException", ImplementationDefined: false)),
        E("div.float", "div", "浮点除，不抛出", Floats, [], V(ValueOp.FloatDivide, P0, P1), ResultKind.SameAsOperand,
            "a / b", "—", "III.3.31 div", sameKind: true),
        Divide("rem", ValueOp.SignedRemainder, "%", "III.3.55 rem",
            new("被除数是最小值且除数是 −1", "ECMA-335 III.3.55：可以抛出 ArithmeticException，也可以不抛出", ImplementationDefined: true)),
        E("and", "and", "按位与", Integers, [], V(ValueOp.And, P0, P1), ResultKind.SameAsOperand, "a & b", "—", "III.3.3 and", sameKind: true),
        E("xor", "xor", "按位异或", Integers, [], V(ValueOp.Xor, P0, P1), ResultKind.SameAsOperand, "a ^ b", "—", "III.3.67 xor", sameKind: true),
        E("neg.int", "neg", "整数取负，回绕", [StackClass.Integer], [], V(ValueOp.Negate, P0), ResultKind.SameAsOperand, "-a", "—", "III.3.50 neg"),
        Shift("shl", ValueOp.ShiftLeft, "<<", "III.3.58 shl"),
        Shift("shr", ValueOp.ShiftRightSigned, ">>", "III.3.59 shr"),
        Shift("shr.un", ValueOp.ShiftRightUnsigned, ">>（按无符号）", "III.3.60 shr.un"),

        // ---- 转换 ----
        E("conv.i2", "conv.i2", "取低 16 位，按符号扩到 int32", [StackClass.Integer], [], Resize(P0, 16, 32, true), ResultKind.Int32,
            "(int16_t)a", "—", "III.3.27 conv"),
        E("conv.i4.float", "conv.i4", "浮点转 int32，向零舍入；范围外的结果由运行时函数给出", [StackClass.Float], [],
            Named(RuntimeFunction.CastDoubleToInt32, V(ValueOp.FloatToDouble, P0)), ResultKind.Int32,
            "il2cpp_codegen_cast_double_to_int<int32_t>(a)", $"{Common}: il2cpp_codegen_cast_double_to_int", "III.3.27 conv"),
        E("conv.r.un", "conv.r.un", "无符号整数转 double", [StackClass.Integer], [], V(ValueOp.UnsignedToDouble, P0), ResultKind.Float64,
            "(double)(uint32_t)a 或 (double)(uint64_t)a", "—", "III.3.27 conv"),
        E("conv.r8.float", "conv.r8", "浮点转 double", [StackClass.Float], [], V(ValueOp.FloatToDouble, P0), ResultKind.Float64,
            "(double)a", "—", "III.3.27 conv"),

        // ---- 字段 ----
        E("ldfld.object", "ldfld", "读对象的实例字段", [StackClass.Object], [ThrowIfNull(P0), Read(LocationKind.InstanceField, P0)],
            Loaded(S(1)), ResultKind.Subject, "NullCheck(o); o->field", $"{Codegen}: NullCheck", "III.4.10 ldfld", condition: VariantCondition.InstanceField),
        E("ldfld.value", "ldfld", "取值类型的值里的一个字段", [StackClass.Value], [], Loaded(V(ValueOp.FieldOfValue, P0)), ResultKind.Subject,
            "v.field", "—", "III.4.10 ldfld", condition: VariantCondition.InstanceField),
        E("ldflda.address", "ldflda", "字段的地址，所属值经地址给出", [StackClass.ByRef], [], Named(RuntimeFunction.FieldAddress, P0), ResultKind.ByRef,
            "&p->field", "—", "III.4.11 ldflda", condition: VariantCondition.InstanceField),
        E("stfld.object", "stfld", "写对象的实例字段", [StackClass.Object, StackClass.Assignable],
            [ThrowIfNull(P0), Write(LocationKind.InstanceField, Stored(P1), P0)], null, ResultKind.None,
            "NullCheck(o); o->field = v（引用类型的字段另有写屏障，不可观察）", $"{Codegen}: NullCheck", "III.4.28 stfld", condition: VariantCondition.InstanceField),
        E("stfld.address", "stfld", "经地址写字段", [StackClass.ByRef, StackClass.Assignable],
            [Write(LocationKind.FieldAtAddress, Stored(P1), P0)], null, ResultKind.None, "p->field = v", "—", "III.4.28 stfld",
            condition: VariantCondition.InstanceField),
        E("ldsfld.init", "ldsfld", "读静态字段，先确保所属的类已初始化", None,
            [Do(StepKind.ClassInitialize), Read(LocationKind.StaticField)], Loaded(S(1)), ResultKind.Subject,
            "il2cpp_codegen_runtime_class_init_inline(T_il2cpp_TypeInfo_var); ((T_StaticFields*)il2cpp_codegen_static_fields_for(T_il2cpp_TypeInfo_var))->field",
            $"{Codegen}: il2cpp_codegen_runtime_class_init_inline, il2cpp_codegen_static_fields_for",
            "III.4.14 ldsfld", condition: VariantCondition.StaticWithInitializer),
        E("stsfld.init", "stsfld", "写静态字段，先确保所属的类已初始化", [StackClass.Assignable],
            [Do(StepKind.ClassInitialize), Write(LocationKind.StaticField, Stored(P0))], null, ResultKind.None,
            "il2cpp_codegen_runtime_class_init_inline(T_il2cpp_TypeInfo_var); ((T_StaticFields*)il2cpp_codegen_static_fields_for(T_il2cpp_TypeInfo_var))->field = v",
            $"{Codegen}: il2cpp_codegen_runtime_class_init_inline, il2cpp_codegen_static_fields_for",
            "III.4.30 stsfld", condition: VariantCondition.StaticWithInitializer),

        // ---- 数组 ----
        E("ldelem.i4", "ldelem.i4", "读 int32 数组的元素", [StackClass.Object, StackClass.Int32],
            [ThrowIfNull(P0), ThrowIf(V(ValueOp.Not, V(ValueOp.UnsignedLess, P1, Named(RuntimeFunction.ArrayLength, P0))), ExceptionKind.IndexOutOfRange),
                Read(LocationKind.ArrayElement, P0, P1)],
            S(2), ResultKind.Int32, "NullCheck(a); a->GetAt(i)（GetAt 内是 IL2CPP_ARRAY_BOUNDS_CHECK 与读取）",
            $"{Codegen}: NullCheck, IL2CPP_ARRAY_BOUNDS_CHECK", "III.4.8 ldelem.<type>", impliedBits: 32),
        E("stelem.i4", "stelem.i4", "写 int32 数组的元素", [StackClass.Object, StackClass.Int32, StackClass.Int32],
            [ThrowIfNull(P0), ThrowIf(V(ValueOp.Not, V(ValueOp.UnsignedLess, P1, Named(RuntimeFunction.ArrayLength, P0))), ExceptionKind.IndexOutOfRange),
                Write(LocationKind.ArrayElement, P2, P0, P1)],
            null, ResultKind.None, "NullCheck(a); a->SetAt(i, v)（SetAt 内是 IL2CPP_ARRAY_BOUNDS_CHECK 与写入）",
            $"{Codegen}: NullCheck, IL2CPP_ARRAY_BOUNDS_CHECK", "III.4.27 stelem.<type>", impliedBits: 32),

        // ---- 类型检查 ----
        E("isinst", "isinst", "对象可以当作该类使用时是对象自己，否则为空", [StackClass.Object], [], Named(RuntimeFunction.IsInstance, P0), ResultKind.Object,
            "IsInstClass / IsInstSealed / IsInst(o, T_il2cpp_TypeInfo_var)", $"{Codegen}: IsInst, IsInstClass, IsInstSealed", "III.4.6 isinst"),
        E("castclass", "castclass", "对象非空且不能当作该类使用时抛出", [StackClass.Object],
            [ThrowIf(V(ValueOp.Both, V(ValueOp.Not, IsNull(P0)), IsNull(Named(RuntimeFunction.IsInstance, P0))), ExceptionKind.InvalidCast)],
            P0, ResultKind.Object, "CastclassClass / CastclassSealed / Castclass(o, T_il2cpp_TypeInfo_var)",
            $"{Codegen}: Castclass, CastclassClass, CastclassSealed", "III.4.3 castclass"),

        // ---- 比较与分支 ----
        E("cgt.un", "cgt.un", "无符号大于；与空引用比较时是“非空”", [StackClass.Scalar, StackClass.Scalar], [],
            V(ValueOp.Flag, V(ValueOp.UnsignedLess, P1, P0)), ResultKind.Int32, "(a > b) 按无符号比较 ? 1 : 0", "—", "III.3.23 cgt.un", sameKind: true),
        E("br", "br", "无条件转移", None, [Do(StepKind.Jump)], null, ResultKind.None, "goto IL_xxxx", "—", "III.3.15 br"),
        E("brfalse", "brfalse", "为零或为空时转移", [StackClass.Scalar], [Do(StepKind.Branch, V(ValueOp.IsZero, P0))], null, ResultKind.None,
            "if (!a) goto IL_xxxx", "—", "III.3.17 brfalse"),
        E("brtrue", "brtrue", "非零或非空时转移", [StackClass.Scalar], [Do(StepKind.Branch, V(ValueOp.Not, V(ValueOp.IsZero, P0)))], null, ResultKind.None,
            "if (a) goto IL_xxxx", "—", "III.3.18 brtrue"),
        Compare("bge", V(ValueOp.Not, V(ValueOp.SignedLess, P0, P1)), ">=", "III.3.6 bge"),
        Compare("bgt", V(ValueOp.SignedLess, P1, P0), ">", "III.3.8 bgt"),
        Compare("ble", V(ValueOp.Not, V(ValueOp.SignedLess, P1, P0)), "<=", "III.3.10 ble"),
        Compare("blt", V(ValueOp.SignedLess, P0, P1), "<", "III.3.12 blt"),
        E("switch", "switch", "跳转表：选择子按无符号数与表长比较", [StackClass.Int32], [Do(StepKind.Switch, P0)], null, ResultKind.None,
            "switch (a) { case k: goto IL_xxxx; }", "—", "III.3.66 switch"),
        E("ret.void", "ret", "返回", None, [Do(StepKind.Return)], null, ResultKind.None, "return", "—", "III.3.57 ret",
            condition: VariantCondition.ReturnsVoid),
        E("ret.value", "ret", "返回一个值：按返回类型存储", [StackClass.Assignable], [Do(StepKind.Return, Stored(P0))], null, ResultKind.None,
            "return v", "—", "III.3.57 ret；III.1.6", condition: VariantCondition.ReturnsValue),

        // ---- 调用 ----
        E("call.static", "call", "调用没有 this 的方法，所属的类没有静态构造函数", None, [new(StepKind.Call, [])], Loaded(S(0)), ResultKind.Subject,
            "M(x…, method)", "—", "III.3.19 call", condition: VariantCondition.StaticMethod, fromSignature: true),
        E("call.static.init", "call", "调用没有 this 的方法，先确保所属的类已初始化", None,
            [Do(StepKind.ClassInitialize), new(StepKind.Call, [])], Loaded(S(1)), ResultKind.Subject,
            "il2cpp_codegen_runtime_class_init_inline(T_il2cpp_TypeInfo_var); M(x…, method)",
            $"{Codegen}: il2cpp_codegen_runtime_class_init_inline", "III.3.19 call；I.8.9.5",
            condition: VariantCondition.StaticMethodWithInitializer, fromSignature: true),
        E("callvirt.unique", "callvirt", "调用目标唯一的实例方法", None, [ThrowIfNull(P0), new(StepKind.Call, [])], Loaded(S(1)), ResultKind.Subject,
            "NullCheck(o); M(o, x…, method)", $"{Codegen}: NullCheck", "III.4.2 callvirt", condition: VariantCondition.UniqueTarget, fromSignature: true),
        E("callvirt.virtual", "callvirt", "经虚表调用类上的虚方法", None,
            [ThrowIfNull(P0), new(StepKind.Call, [Named(RuntimeFunction.VirtualInvokeData, Named(RuntimeFunction.ClassOf, P0))], Indirect: true)],
            Loaded(S(1)), ResultKind.Subject, "NullCheck(o); VirtualFuncInvokerN<R, T…>::Invoke(slot, o, x…)",
            $"{Codegen}: NullCheck, il2cpp_codegen_get_virtual_invoke_data", "III.4.2 callvirt", condition: VariantCondition.ClassVirtual, fromSignature: true),
        // 接口查找的参数是接收者对象本身：慢路径 GetInterfaceInvokeDataFromVTableSlowPath(obj, itf, slot) 用到对象，类只是它的一个属性。
        E("callvirt.interface", "callvirt", "经接口查找调用接口方法", None,
            [ThrowIfNull(P0),
                new(StepKind.RuntimeCall, [P0], Function: RuntimeFunction.InterfaceInvokeData),
                new(StepKind.Call, [S(1)], Indirect: true)],
            Loaded(S(2)), ResultKind.Subject, "NullCheck(o); InterfaceFuncInvokerN<R, T…>::Invoke(slot, I_il2cpp_TypeInfo_var, o, x…)",
            $"{Codegen}: NullCheck, il2cpp_codegen_get_interface_invoke_data；vm/ClassInlines.h: GetInterfaceInvokeDataFromVTable, GetInterfaceInvokeDataFromVTableSlowPath",
            "III.4.2 callvirt", condition: VariantCondition.InterfaceMethod, fromSignature: true),
    ];

    private static readonly FrozenDictionary<string, CatalogEntry> byId = entries.ToFrozenDictionary(e => e.Id);
    private static readonly ILookup<string, CatalogEntry> byIl = entries.ToLookup(e => e.Il);

    public static ImmutableArray<CatalogEntry> Entries => entries;

    public static CatalogEntry Get(string id) => byId[id];

    /// <summary>同一条指令（规范助记符）的全部目录项。</summary>
    public static IEnumerable<CatalogEntry> ForInstruction(string canonical) => byIl[canonical];
}
