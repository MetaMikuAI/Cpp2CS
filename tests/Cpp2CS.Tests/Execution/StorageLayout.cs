namespace Cpp2CS.Tests.Execution;
/// <summary>解释器私有存储编码，不描述任何目标运行时的 ABI。</summary>
internal static class StorageLayout
{
    public const int ObjectKlass = 0, ObjectHeaderSize = 8;
    public const int ArrayMaxLength = 8, ArrayData = 16;
    public const int StringLength = 8, StringChars = 12;
}
