using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Structure;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Naming;

public abstract record MetadataEntity;
public sealed record ClassEntity(TypeRef Type) : MetadataEntity;
public sealed record TypeEntity(TypeRef Type) : MetadataEntity;
public sealed record MethodEntity(MethodRef Method) : MetadataEntity;
public sealed record FieldEntity(FieldRef Field) : MetadataEntity;
public sealed record StringEntity(string Value) : MetadataEntity;
public interface IMetadataSlotDecoder { Outcome<MetadataEntity> Decode(ulong imageOffset); }
public sealed record FlagEvidence(bool IsFlag, ImmutableArray<Reason> Reasons, int Reads, int Writes);
public sealed record NamingFacts(ImmutableDictionary<ulong, Outcome<MetadataEntity>> Slots,
    ImmutableDictionary<ulong, FlagEvidence> Flags, bool Complete)
{
    public static NamingFacts Empty { get; } = new(ImmutableDictionary<ulong, Outcome<MetadataEntity>>.Empty,
        ImmutableDictionary<ulong, FlagEvidence>.Empty, false);
}
public sealed class InitializationFlagQuery(NamingFacts facts) : Query<ulong, FlagEvidence>
{
    public override Outcome<FlagEvidence> Compute(QueryContext c, ulong key) => Outcome<FlagEvidence>.Success(
        facts.Flags.GetValueOrDefault(key) ?? new(false, [new("naming.no-access-evidence", "本函数没有该字节的访问凭据。")], 0, 0));
}

/// <summary>逐函数验证方法初始化模板；跨函数汇总只合并各函数已经独立得到的结论。</summary>
/// <remarks>Complete 描述观察范围，不参与函数内标志的判定。</remarks>
public sealed class NamingSurvey(CallNamingQuery calls, IMetadataSlotDecoder decoder, IImage? image = null,
    MethodBinder? binder = null, RuntimeSpec? spec = null, SignatureBinding? entry = null)
{
    private readonly Dictionary<ulong, Outcome<MetadataEntity>> slots = [];
    private readonly Dictionary<ulong, FlagEvidence> flags = [];
    private readonly StateQueries state = new(image: image);
    private bool complete = true;
    public void Incomplete() => complete = false;
    private sealed record Access(Point Point, Statement Statement, Location Location);

    public void Observe(NativeFunction function)
    {
        var c = state.CreateContext(function);
        foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
            if (c.Get(calls, call.Identity) is { IsSuccess: true, Value.Operation.Name: "InitializeMetadata" } classified
                && classified.Value.Inputs?.GetValueOrDefault("slot")?.Source is TermSource source
                && Address(c, source.Term, function.AddressWidth) is { } address)
                slots.TryAdd(address, decoder.Decode(address));
        var accesses = new List<Access>();
        var unclassified = new List<(Access Access, Term Address, Reason? Why)>();
        foreach (var block in function.Blocks)
        for (int i = 0; i < block.Statements.Length; i++)
        {
            var statement = block.Statements[i];
            var request = statement switch
            {
                MemoryRead read => new AddressRequest(read.Address, read.Width),
                MemoryWrite write => new AddressRequest(write.Address, write.Width), _ => default,
            };
            if (request.Address is null) continue;
            var resolved = c.Get(state.Resolve, request.Address);
            var location = resolved.IsSuccess ? c.Get(state.Locations, new(resolved.Value, request.Width)) : default;
            if (location.IsSuccess && location.Value is { Region: Region.Image, Offset: not null })
                accesses.Add(new(new(block.Identity, i), statement, location.Value));
            else unclassified.Add((new(new(block.Identity, i), statement, location.IsSuccess ? location.Value
                : new(Region.Other, request.Address, null, request.Width, request.Address)), request.Address, location.Why));
        }
        var candidates = accesses.Where(a => a.Location is { Width: 8, Offset: not null }).Select(a => a.Location).Distinct().ToArray();
        if (candidates.Length == 0) return;
        var localSlots = slots.ToImmutableDictionary();
        var names = binder is not null && spec is not null ? new ValueNamingQuery(state, calls,
            new(localSlots, ImmutableDictionary<ulong, FlagEvidence>.Empty, true), spec, binder, entry) : null;
        if (names is not null) c = names.CreateContext(function);
        var uses = new SemanticUses(c, calls, state, binder, entry);
        var prefix = names is null ? null : new InitializationPrefixQuery(state, calls, names, image);
        var unknownUses = new Dictionary<ulong, List<(Access Access, Reason? Why)>>();
        foreach (var unknown in unclassified)
            foreach (var address in uses.ImageAddresses(unknown.Address, c, state))
            {
                if (!unknownUses.TryGetValue(address, out var list)) unknownUses[address] = list = [];
                list.Add((unknown.Access, unknown.Why));
            }
        var escapedUses = new Dictionary<ulong, List<SemanticUses.Use>>();
        foreach (var use in uses.Roots.Where(u => !u.Address))
            foreach (var address in uses.ImageAddresses(use.Value, c, state))
            {
                if (!escapedUses.TryGetValue(address, out var list)) escapedUses[address] = list = [];
                list.Add(use);
            }
        foreach (var candidate in candidates)
        {
            if (candidate.Offset is not { } number || number < 0 || number > ulong.MaxValue) continue;
            ulong address = (ulong)number;
            var why = new List<Reason>(); int reads = 0, writes = 0;
            var verifiedWrites = new HashSet<WriteIdentity>();
            void Reject(string code, string text, Access? access = null, Reason? cause = null)
            {
                var position = access?.Statement.Trace is { } trace ? $"0x{trace.NativeAddress:x}" : access is null ? "地址" : $"块 {function.Blocks.IndexOf(function.Blocks.Single(b => b.Identity == access.Point.Block))} 的语句 {access.Point.Before}";
                why.Add(new("naming.flag-" + code, position + "：" + text, cause));
            }
            var info = image?.Query(address);
            if (info is not { Writable: true, Executable: false, AvailableBytes: > 0 } || info.Storage == StorageKind.Unmapped)
                Reject("storage", "不是映像可写数据里的字节。");
            foreach (var slot in localSlots.Keys)
            {
                var metadata = candidate with { Offset = slot, Width = function.AddressWidth };
                if (c.Get(state.Alias, new(candidate, metadata)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint })
                    Reject("slot", "该字节与元数据槽位重叠。");
            }
            var related = accesses.Where(access => c.Get(state.Alias, new(candidate, access.Location)) is not { IsSuccess: true, Value.Kind: AliasKind.Disjoint }).ToArray();
            foreach (var access in related)
            {
                if (access.Location != candidate)
                { Reject("overlap", "存在宽访问或无法归类的映像地址访问。", access); continue; }
                if (names is not null && c.Get(names, function.Terms.Atom(new MemoryAtom(access.Location, null), 8)) is
                    { IsSuccess: true, Value.Name: FieldName or BitStorageName or EntityName })
                    Reject("named", "该字节属于已命名的规格结构或元数据槽位。", access);
                if (access.Statement is MemoryRead read)
                {
                    reads++;
                    var users = uses.Of(read.Identity).ToArray();
                    if (read.Acquire || users.Length == 0)
                        Reject("read", "读取没有零／非零分支测试凭据。", access);
                    foreach (var use in users)
                    {
                        var test = use.Condition ? InitializationTest.Of(use.Value) : null;
                        if (test is null || test.Read != read.Identity)
                        { Reject("read", "读取另有真实使用：" + use.Kind + "。", access); continue; }
                        if (prefix is null) { Reject("context", "缺少签名与规格的模板判定上下文。", access); continue; }
                        var head = function.Blocks.Single(b => b.Identity == use.Point.Block);
                        var branch = (Branch)head.End;
                        var group = c.Get(prefix, new(new(head.Identity, test.ZeroWhenTrue ? branch.True : branch.False), null,
                            candidate, test.Low, test.Width));
                        if (!group.IsSuccess)
                        { Reject("order", "从测试到置位的元数据初始化模板未成立。", access, group.Why); continue; }
                        verifiedWrites.UnionWith(group.Value.Statements.OfType<MemoryWrite>().Select(w => w.Identity));
                    }
                }
                else if (access.Statement is MemoryWrite write)
                {
                    writes++;
                    var value = c.Get(state.Resolve, write.Value);
                    if (write.Release || !value.IsSuccess || value.Value.ConstantValue is not { IsZero: false })
                        Reject("write", "写入不是非零字节常量。", access, value.Why);
                }
            }
            foreach (var unknown in unknownUses.GetValueOrDefault(address) ?? [])
                Reject("access", "这次内存访问含该字节的地址，但未得到唯一的常量访问位置。", unknown.Access, unknown.Why);
            foreach (var access in related.Where(a => a.Statement is MemoryWrite write && !verifiedWrites.Contains(write.Identity)))
                Reject("order", "这次写入没有对应测试之后的元数据初始化凭据。", access);
            foreach (var use in escapedUses.GetValueOrDefault(address) ?? [])
                Reject("escape", "地址另有真实非内存用途：" + use.Kind + "。");
            if (reads == 0 || writes == 0) Reject("access", "本函数缺少读取或写入凭据。");
            var result = new FlagEvidence(why.Count == 0, why.Distinct().ToImmutableArray(), reads, writes);
            if (flags.TryGetValue(address, out var previous)) result = new(previous.IsFlag && result.IsFlag,
                previous.Reasons.AddRange(result.Reasons).Distinct().ToImmutableArray(), previous.Reads + reads, previous.Writes + writes);
            flags[address] = result;
        }
    }

    private ulong? Address(QueryContext c, Term term, int width)
    {
        if (term.Width != c.Snapshot.AddressWidth || term.ContainsUndefined) return null;
        var value = c.Get(state.Resolve, term); if (!value.IsSuccess || value.Value.ContainsUndefined) return null;
        var location = c.Get(state.Locations, new(value.Value, width));
        return location.IsSuccess && location.Value is { Region: Region.Image, Offset: { } offset } && offset >= 0 && offset <= ulong.MaxValue ? (ulong)offset : null;
    }
    public NamingFacts Finish() => new(slots.ToImmutableDictionary(), flags.ToImmutableDictionary(), complete);
}
