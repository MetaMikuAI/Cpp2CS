
namespace Cpp2CS.Recovery.Typing;

internal static class TypingContributors
{
    public static IReadOnlyList<ITypeContributor> Create(TypingInputs input) =>
    [
        new EntryArgumentContributor(), new PhiContributor(), new CopyContributor(),
        new DefinitionContributor(input), new CallResultContributor(), new AllocationContributor(),
        new UseContributor(input), new PhiUseContributor(), new RuntimeContributor(input),
        new TypeCheckContributor(input), new FloatContributor(input), new StructContributor(input),
        new DelegateContributor(input), new ExceptionContributor(input), new PairingContributor(input),
        new AtomicReferenceContributor(input),
    ];
}
