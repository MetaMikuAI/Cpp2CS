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
        VariantCondition condition = VariantCondition.None, bool fromSignature = false, ScalarStorage? storage = null) =>
        new(id, il, summary, [.. operands], sameKind, condition, [.. steps], result, kind, new(translation, runtime, "ECMA-335 " + standard))
        { OperandsFromSignature = fromSignature, Storage = storage };

    private static readonly StackClass[] None = [];
    private static readonly StackClass[] Integers = [StackClass.Integer, StackClass.Integer];
    private static readonly StackClass[] Floats = [StackClass.Float, StackClass.Float];

    /// <summary>ldind 与 stind 和对应标量的 ldobj 与 stobj 有相同的读写，存储类型由助记符给出。</summary>
    private static IEnumerable<CatalogEntry> Indirect(string suffix, ScalarStorage storage, string cpp, bool loadOnly = false)
    {
        string load = "ldind." + suffix;
        yield return E(load, load, "间接读取并扩到栈上位宽", [StackClass.ByRef], [Read(LocationKind.Address, P0)],
            Loaded(S(0)), ResultKind.Subject, $"*(({cpp}*)p)", "—", "III.3.42 ldind.<type>", storage: storage);
        if (loadOnly) yield break;
        string store = "stind." + suffix;
        yield return E(store, store, "按存储类型间接写入", [StackClass.ByRef, StackClass.Assignable],
            [Write(LocationKind.Address, Stored(P1), P0)], null, ResultKind.None, $"*(({cpp}*)p) = ({cpp})v",
            storage.Kind == StackKind.Object ? "引用写入的写屏障不可观察" : "—", "III.3.62 stind.<type>", storage: storage);
    }

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

    private static CatalogEntry Compare(string il, TemplateValue condition, string symbol, string standard,
        string summary = "有符号整数比较后分支", string? translation = null) =>
        E(il + ".int", il, summary, Integers, [Do(StepKind.Branch, condition)], null, ResultKind.None,
            translation ?? $"if (a {symbol} b) goto IL_xxxx", "—", standard, sameKind: true);

    private static TemplateValue OutOfBounds(TemplateValue array, TemplateValue index) =>
        V(ValueOp.Not, V(ValueOp.UnsignedLess, index, Named(RuntimeFunction.ArrayLength, array)));

    private static readonly ImmutableArray<CatalogEntry> entries =
    [
        // ---- 形参、局部与常量 ----
        E("ldarg", "ldarg", "形参的值", None, [], V(ValueOp.Argument), ResultKind.Subject, "L_n = ___i_name", "—", "III.3.38 ldarg",
            condition: VariantCondition.AddressNotTaken),
        E("ldarg.frame", "ldarg", "读被取地址的形参", None, [Read(LocationKind.Address, V(ValueOp.ArgumentAddress))],
            Loaded(S(0)), ResultKind.Subject, "L_n = ___i_name", "—", "III.3.38 ldarg", condition: VariantCondition.AddressTaken),
        E("ldarga", "ldarga", "形参的地址", None, [], V(ValueOp.ArgumentAddress), ResultKind.ByRef, "&___i_name", "—", "III.3.39 ldarga"),
        E("starg", "starg", "写形参：按形参类型存储", [StackClass.Assignable], [Do(StepKind.StoreArgument, Loaded(Stored(P0)))], null, ResultKind.None,
            "___i_name = v", "—", "III.3.61 starg", condition: VariantCondition.AddressNotTaken),
        E("starg.frame", "starg", "写被取地址的形参", [StackClass.Assignable], [Write(LocationKind.Address, Stored(P0), V(ValueOp.ArgumentAddress))],
            null, ResultKind.None, "___i_name = v", "—", "III.3.61 starg", condition: VariantCondition.AddressTaken),
        E("ldloc", "ldloc", "局部变量的值", None, [], V(ValueOp.Local), ResultKind.Subject, "L_n = V_i", "—", "III.3.43 ldloc",
            condition: VariantCondition.AddressNotTaken),
        E("ldloc.frame", "ldloc", "读被取地址的局部", None, [Read(LocationKind.Address, V(ValueOp.LocalAddress))],
            Loaded(S(0)), ResultKind.Subject, "L_n = V_i", "—", "III.3.43 ldloc", condition: VariantCondition.AddressTaken),
        E("ldloca", "ldloca", "局部变量的地址", None, [], V(ValueOp.LocalAddress), ResultKind.ByRef, "&V_i", "—", "III.3.44 ldloca"),
        E("stloc", "stloc", "写局部变量：按变量类型存储", [StackClass.Assignable], [Do(StepKind.StoreLocal, Loaded(Stored(P0)))], null, ResultKind.None,
            "V_i = v", "—", "III.3.63 stloc", condition: VariantCondition.AddressNotTaken),
        E("stloc.frame", "stloc", "写被取地址的局部", [StackClass.Assignable], [Write(LocationKind.Address, Stored(P0), V(ValueOp.LocalAddress))],
            null, ResultKind.None, "V_i = v", "—", "III.3.63 stloc", condition: VariantCondition.AddressTaken),
        E("ldc.i4", "ldc.i4", "int32 常量", None, [], new(ValueOp.Immediate, [], 32), ResultKind.Int32, "字面量", "—", "III.3.40 ldc"),
        E("ldnull", "ldnull", "空引用", None, [], V(ValueOp.Null), ResultKind.Object, "NULL", "—", "III.3.45 ldnull"),
        // 字面量槽的惰性初始化不可观察；初始化之后槽里是字面量表里的那个字符串对象（同一内容同一对象）。
        E("ldstr", "ldstr", "字符串字面量：结果是字符串实体，没有效果", None, [], V(ValueOp.Literal), ResultKind.Object,
            "语料 Construction.ThrowEither：((String_t*)il2cpp_codegen_initialize_runtime_metadata_inline((uintptr_t*)&_stringLiteral8739…))",
            $"{Codegen}: il2cpp_codegen_initialize_runtime_metadata_inline；vm/GlobalMetadata.cpp: InitializeRuntimeMetadata 的 kIl2CppMetadataUsageStringLiteral（GetStringLiteralFromIndex）",
            "III.4.16 ldstr"),
        E("dup", "dup", "复制栈顶的值", [StackClass.Any], [Do(StepKind.PushOperand)], P0, ResultKind.SameAsOperand,
            "语料 Passing.RewriteLarge：int64_t* L_1 = L_0", "—", "III.3.33 dup"),
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
        E("conv.i8.int", "conv.i8", "整数按符号扩到 int64", [StackClass.Integer], [], V(ValueOp.ToInt64, P0), ResultKind.Int64,
            "(int64_t)a", "—", "III.3.27 conv"),
        E("conv.i2", "conv.i2", "取低 16 位，按符号扩到 int32", [StackClass.Integer], [], Resize(P0, 16, 32, true), ResultKind.Int32,
            "(int16_t)a", "—", "III.3.27 conv"),
        E("conv.i4.int", "conv.i4", "整数转 int32：取低 32 位", [StackClass.Integer], [], Resize(P0, 32, 32, true), ResultKind.Int32,
            "语料 ArrayStore.StoreLengthLoop：(int32_t)(((RuntimeArray*)L_5)->max_length)", "—", "III.3.27 conv"),
        E("conv.i4.float", "conv.i4", "浮点转 int32，向零舍入；范围外的结果由运行时函数给出", [StackClass.Float], [],
            Named(RuntimeFunction.CastDoubleToInt32, V(ValueOp.FloatToDouble, P0)), ResultKind.Int32,
            "il2cpp_codegen_cast_double_to_int<int32_t>(a)", $"{Common}: il2cpp_codegen_cast_double_to_int", "III.3.27 conv"),
        E("conv.r.un", "conv.r.un", "无符号整数转 double", [StackClass.Integer], [], V(ValueOp.UnsignedToDouble, P0), ResultKind.Float64,
            "(double)(uint32_t)a 或 (double)(uint64_t)a", "—", "III.3.27 conv"),
        E("conv.r8.float", "conv.r8", "浮点转 double", [StackClass.Float], [], V(ValueOp.FloatToDouble, P0), ResultKind.Float64,
            "(double)a", "—", "III.3.27 conv"),

        // ---- 间接读写与字段。语料 Passing.RewriteLarge：读取 *((int64_t*)L_1)，更新后写回同址。 ----
        .. Indirect("i1", new(StackKind.Int32, 8, true), "int8_t"),
        .. Indirect("u1", new(StackKind.Int32, 8, false), "uint8_t", loadOnly: true),
        .. Indirect("i2", new(StackKind.Int32, 16, true), "int16_t"),
        .. Indirect("u2", new(StackKind.Int32, 16, false), "uint16_t", loadOnly: true),
        .. Indirect("i4", new(StackKind.Int32, 32, true), "int32_t"),
        .. Indirect("u4", new(StackKind.Int32, 32, false), "uint32_t", loadOnly: true),
        .. Indirect("i8", new(StackKind.Int64, 64, true), "int64_t"),
        .. Indirect("i", new(StackKind.NativeInt, 0, true), "intptr_t"),
        .. Indirect("r4", new(StackKind.Float32, 32, false), "float"),
        .. Indirect("r8", new(StackKind.Float64, 64, false), "double"),
        .. Indirect("ref", new(StackKind.Object, 0, false), "RuntimeObject*"),
        E("ldobj", "ldobj", "读指针所指的值", [StackClass.ByRef], [Read(LocationKind.Address, P0)], Loaded(S(0)), ResultKind.Subject,
            "*p", "—", "III.4.13 ldobj"),
        E("stobj", "stobj", "写指针所指的值", [StackClass.ByRef, StackClass.Assignable], [Write(LocationKind.Address, Stored(P1), P0)],
            null, ResultKind.None, "*p = v", "—", "III.4.29 stobj"),
        E("initobj", "initobj", "将指针所指的值置零", [StackClass.ByRef], [Write(LocationKind.Address, V(ValueOp.StorageZero), P0)],
            null, ResultKind.None, "memset(p, 0, sizeof(T))", "—", "III.4.5 initobj"),
        E("ldfld.address", "ldfld", "经地址读字段", [StackClass.ByRef], [Read(LocationKind.FieldAtAddress, P0)], Loaded(S(0)), ResultKind.Subject,
            "p->field", "—", "III.4.10 ldfld", condition: VariantCondition.InstanceField),
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
            $"{Codegen}: NullCheck, IL2CPP_ARRAY_BOUNDS_CHECK", "III.4.8 ldelem.<type>", storage: new ScalarStorage(StackKind.Int32, 32, true)),
        E("stelem.i4", "stelem.i4", "写 int32 数组的元素", [StackClass.Object, StackClass.Int32, StackClass.Int32],
            [ThrowIfNull(P0), ThrowIf(V(ValueOp.Not, V(ValueOp.UnsignedLess, P1, Named(RuntimeFunction.ArrayLength, P0))), ExceptionKind.IndexOutOfRange),
                Write(LocationKind.ArrayElement, P2, P0, P1)],
            null, ResultKind.None, "NullCheck(a); a->SetAt(i, v)（SetAt 内是 IL2CPP_ARRAY_BOUNDS_CHECK 与写入）",
            $"{Codegen}: NullCheck, IL2CPP_ARRAY_BOUNDS_CHECK", "III.4.27 stelem.<type>", storage: new ScalarStorage(StackKind.Int32, 32, true)),
        E("ldelem.ref", "ldelem.ref", "读对象引用数组的元素", [StackClass.Object, StackClass.Int32],
            [ThrowIfNull(P0), ThrowIf(OutOfBounds(P0, P1), ExceptionKind.IndexOutOfRange), Read(LocationKind.ArrayElement, P0, P1)],
            S(2), ResultKind.Object,
            "语料 ArrayStore.StoreThenLoad：NullCheck(L_3); (L_3)->GetAt(static_cast<il2cpp_array_size_t>(L_5))（GetAt 内是 IL2CPP_ARRAY_BOUNDS_CHECK 与读取）",
            $"{Codegen}: NullCheck, IL2CPP_ARRAY_BOUNDS_CHECK；数组结构体的 GetAt", "III.4.8 ldelem.<type>", storage: new ScalarStorage(StackKind.Object, 0, false)),
        // 三个检查的先后照生成代码：判空，类型（ArrayElementTypeCheck），越界（SetAt 里的 IL2CPP_ARRAY_BOUNDS_CHECK）。
        // 几种异常同时成立时以本运行时的先后为准（设计 16.2）。元素类型是密封类时生成代码不写 ArrayElementTypeCheck：
        // 那时类型检查在可验证的 IL 上不会成立，由类型事实证明，模板不变。
        E("stelem.ref", "stelem.ref", "写对象引用数组的元素：判空，值非空且不能当作元素类使用时抛出，越界抛出，写入",
            [StackClass.Object, StackClass.Int32, StackClass.Object],
            [ThrowIfNull(P0),
                ThrowIf(V(ValueOp.Both, V(ValueOp.Not, IsNull(P2)),
                    IsNull(Named(RuntimeFunction.IsInstance, P2, Named(RuntimeFunction.ElementClass, Named(RuntimeFunction.ClassOf, P0))))),
                    ExceptionKind.ArrayTypeMismatch),
                ThrowIf(OutOfBounds(P0, P1), ExceptionKind.IndexOutOfRange),
                Write(LocationKind.ArrayElement, P2, P0, P1)],
            null, ResultKind.None,
            "语料 ArrayStore.StoreObject：NullCheck(L_0); ArrayElementTypeCheck (L_0, L_2); (L_0)->SetAt(static_cast<il2cpp_array_size_t>(L_1), (RuntimeObject*)L_2)"
                + "（SetAt 内是 IL2CPP_ARRAY_BOUNDS_CHECK、写入与写屏障）；ArrayStore.StoreString（元素类型 String 是密封类）只有 NullCheck 与 SetAt",
            $"{Codegen}: NullCheck, ArrayElementTypeCheck（value != NULL 且 IsInst(value, array->klass->element_class) == NULL 时抛出 ArrayTypeMismatchException）, IL2CPP_ARRAY_BOUNDS_CHECK；数组结构体的 SetAt",
            "III.4.27 stelem.<type>", storage: new ScalarStorage(StackKind.Object, 0, false)),
        E("ldlen", "ldlen", "数组的长度，本机无符号整数", [StackClass.Object],
            [ThrowIfNull(P0)], Named(RuntimeFunction.ArrayLengthNative, P0), ResultKind.NativeInt,
            "语料 ArrayStore.StoreLengthLoop：NullCheck(L_5); ((RuntimeArray*)L_5)->max_length（il2cpp_array_size_t，指针宽）",
            $"{Codegen}: NullCheck；il2cpp-object-internals.h: Il2CppArray::max_length, IL2CPP_ARRAY_MAX_INDEX；vm/Array.cpp: NewSpecific",
            "III.4.12 ldlen"),

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
        // 只收整数：浮点的 bne.un 是“不相等或无序”时转移，语料里没有用例。
        Compare("bne.un", V(ValueOp.Not, V(ValueOp.Equal, P0, P1)), "!=", "III.3.16 bne.un", "整数不相等时转移",
            "语料 Construction.ThrowOneOfThree：if ((!(((uint32_t)L_2) == ((uint32_t)1)))) goto IL_001d（整数的相等与符号无关）"),
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

        // ---- 构造与抛出 ----
        // 分配之后运行时再确保类已初始化（Object::NewAllocSpecific 末尾的 Runtime::ClassInit）；新对象在首次被使用之前不可见，
        // 两个分量的先后不可观察。值类型的构造（this 是地址）不在本项。
        E("newobj.class", "newobj", "构造引用类型的对象：新对象（含所属类的类初始化分量），调用构造函数，结果是新引用", None,
            [Do(StepKind.NewObject), new(StepKind.Call, [S(0)])], S(0), ResultKind.Object,
            "语料 Construction.NodeSwapped：L_4 = (Node_t3E58…*)il2cpp_codegen_object_new(Node_t3E58…_il2cpp_TypeInfo_var); Node__ctor_mC157…(L_4, L_2, L_3, NULL)",
            $"{Codegen}: il2cpp_codegen_object_new；codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_object_new；vm/Object.cpp: Object::NewAllocSpecific",
            "III.4.21 newobj；I.8.9.5", condition: VariantCondition.ReferenceTypeConstructor, fromSignature: true) with { Constructs = true },
        // 翻译不检查空：il2cpp_codegen_raise_exception 先经异常对象写它的 trace_ips、stack_trace 字段，空对象上是空指针解引用。
        E("throw", "throw", "抛出栈顶的异常对象；对象为空时翻译没有定义", [StackClass.Object],
            [Do(StepKind.Require, V(ValueOp.Not, IsNull(P0))), Do(StepKind.Throw, P0)], null, ResultKind.None,
            "语料 Construction.ThrowEither：IL2CPP_RAISE_MANAGED_EXCEPTION(L_1, ((RuntimeMethod*)il2cpp_codegen_initialize_runtime_metadata_inline(…_RuntimeMethod_var)))",
            $"{Codegen}: IL2CPP_RAISE_MANAGED_EXCEPTION；codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_raise_exception；vm/Exception.cpp: Exception::Raise",
            "III.4.35 throw")
            with { Deviations = [new("异常对象为空", "ECMA-335 III.4.35：对象为空时抛出 NullReferenceException", ImplementationDefined: false)] },
        // ---- 空操作：模板没有效果，下降时不写出指令 ----
        // 它用来消费两臂在可观察行为上相同的分支（设计 9.1、9.5）：元数据惰性初始化的守卫没有托管操作可以归属。
        E("nop", "nop", "空操作：没有效果", None, [], null, ResultKind.None,
            "语料 Guards.MetadataOnBranches：if (!s_Il2CppMethodInitialized) { il2cpp_codegen_initialize_runtime_metadata(…); s_Il2CppMethodInitialized = true; }",
            "codegen/il2cpp-codegen-il2cpp.cpp: il2cpp_codegen_initialize_runtime_metadata；vm/MetadataCache.cpp: MetadataCache::InitializeRuntimeMetadata",
            "III.3.51 nop") with { Elided = true },
        E("call.instance", "call", "按方法令牌直接调用实例方法", None, [new(StepKind.Call, [])], Loaded(S(0)), ResultKind.Subject,
            "语料 Corpus.Cases.cpp:2907 Base__ctor_m…(__this, NULL)；mscorlib.cpp:3023 ErrorInfo_get_Error_m…_inline((&___0_errorInfo), NULL)",
            "—", "III.3.19 call", condition: VariantCondition.InstanceMethod, fromSignature: true),
    ];

    private static readonly FrozenDictionary<string, CatalogEntry> byId = entries.ToFrozenDictionary(e => e.Id);
    private static readonly ILookup<string, CatalogEntry> byIl = entries.ToLookup(e => e.Il);

    public static ImmutableArray<CatalogEntry> Entries => entries;

    public static CatalogEntry Get(string id) => byId[id];

    /// <summary>同一条指令（规范助记符）的全部目录项。</summary>
    public static IEnumerable<CatalogEntry> ForInstruction(string canonical) => byIl[canonical];
}
