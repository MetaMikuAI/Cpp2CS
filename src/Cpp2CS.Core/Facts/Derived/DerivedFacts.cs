
namespace Cpp2CS.Facts.Derived;

public sealed record DerivedFacts
{
    public UnregisteredMethods Unregistered { get; init; } = UnregisteredMethods.Empty;
}
