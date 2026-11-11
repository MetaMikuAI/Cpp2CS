namespace Cpp2CS.Tests.Execution;
[AttributeUsage(AttributeTargets.Class, AllowMultiple = true)]
internal sealed class ShapeModelAttribute(string name) : Attribute
{
    public string Name => name;
    public required string Basis { get; init; }
}
