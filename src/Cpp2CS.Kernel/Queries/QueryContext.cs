using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.Queries;

/// <summary>绑定不可变快照；同一上下文只允许一个调用者。作者错误抛出后须丢弃上下文。</summary>
public sealed class QueryContext
{
    private abstract class Table
    {
        public long Computations, Hits, Failures;
    }
    private sealed class Table<K, V> : Table where K : notnull
    {
        public readonly Dictionary<K, Entry<K, V>> Entries = [];
    }
    private abstract class Entry
    {
        public int Active = -1;
        public bool Published;
        public bool Participant;
        public bool Queued;
        public HashSet<Entry>? Dependents;
        public long Steps;
        public Reason? BudgetFailure;
        public Session? Session;
        public HashSet<QueryAddress>? Dependencies;
        public abstract Query Query { get; }
        public abstract QueryAddress Address { get; }
        public abstract Reason? Why { get; }
        public abstract bool Evaluate(QueryContext context);
        public abstract void Publish(Reason? failure);
        public abstract void Forget();
    }
    private sealed class Entry<K, V>(Query<K, V> query, K key, Table<K, V> table, ILattice<V>? lattice) : Entry where K : notnull
    {
        public Outcome<V> Result = lattice is null ? default : Outcome<V>.Success(lattice.Bottom);
        private Outcome<V> previousCandidate;
        private bool hasCandidate;
        public override Query Query => query;
        public override QueryAddress Address => new(query, key);
        public override Reason? Why => Result.Why;
        public override bool Evaluate(QueryContext context)
        {
            Steps = 0;
            BudgetFailure = null;
            Active = context.stack.Count;
            context.stack.Add(this);
            table.Computations++;
            var next = query.Compute(context, key);
            context.stack.RemoveAt(context.stack.Count - 1);
            Active = -1;
            if (BudgetFailure is { } exhausted) next = Outcome<V>.Failure(exhausted);
            // 组内的失败是格的顶：从近似值变成失败算一次变化，读过近似值的键要重算。
            if (lattice is null || !next.IsSuccess) { Result = next; return lattice is not null; }
            if (hasCandidate && !lattice.LessOrEqual(previousCandidate.Value, next.Value))
                throw new InvalidOperationException("不动点查询的计算结果不单调。");
            var old = Result.Value;
            var joined = lattice.Join(old, next.Value);
            if (!lattice.LessOrEqual(old, joined) || !lattice.LessOrEqual(next.Value, joined))
                throw new InvalidOperationException("合并不是格的上界。");
            var changed = !lattice.LessOrEqual(joined, old);
            previousCandidate = next;
            hasCandidate = true;
            Result = Outcome<V>.Success(joined);
            return changed;
        }
        public override void Publish(Reason? failure)
        {
            if (failure is not null) Result = Outcome<V>.Failure(new("query.fixed-point", "不动点未完成。", failure));
            Published = true;
            Session = null;
            if (!Result.IsSuccess) table.Failures++;
        }
        public override void Forget() => table.Entries.Remove(key);
    }
    private sealed class Session(FixedPointGroup group)
    {
        public readonly FixedPointGroup Group = group;
        // 保存本次求解的键；反向依赖只在求解期间存在，收敛后释放。
        public readonly List<Entry> Entries = [];
        public readonly Queue<Entry> Work = new();
        public void Enqueue(Entry entry)
        {
            if (entry.Published || entry.Queued || !entry.Participant) return;
            entry.Queued = true; Work.Enqueue(entry);
        }
        public long Steps;
        public Reason? Failure;
    }
    private readonly object? facts;
    private readonly Dictionary<Query, Table> tables = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Query, (FixedPointGroup Group, FixedPointMember Member)> groups = new(ReferenceEqualityComparer.Instance);
    private readonly List<Session> sessions = [];
    private readonly List<Entry> stack = [];
    public QueryContext(NativeFunction snapshot, object? globalFacts = null, params FixedPointGroup[] fixedPointGroups)
    {
        Snapshot = snapshot ?? throw new ArgumentNullException(nameof(snapshot));
        facts = globalFacts;
        foreach (var group in fixedPointGroups)
            foreach (var member in group.Members)
                if (!groups.TryAdd(member.Query, (group, member))) throw new ArgumentException("查询不能属于多个组。");
    }
    public NativeFunction Snapshot { get; }
    public bool RecordDependencies { get; init; }
    public long StackSwitches { get; private set; }
    public T Facts<T>() where T : class => facts as T ?? throw new InvalidOperationException("全局事实类型不匹配。");
    public ImmutableDictionary<Query, QueryStatistics> Statistics => tables.ToImmutableDictionary(
        p => p.Key, p => new QueryStatistics(p.Value.Computations, p.Value.Hits, p.Value.Failures));
    public QueryTrace Explain<K, V>(Query<K, V> query, K key) where K : notnull
    {
        if (!RecordDependencies) throw new InvalidOperationException("创建上下文时未启用依赖记录。");
        var entry = ((Table<K, V>)tables[query]).Entries[key];
        if (!entry.Published) throw new InvalidOperationException("结果尚未发布。");
        return new(entry.Address, entry.Dependencies?.ToImmutableArray() ?? [], entry.Why);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public Outcome<V> Get<K, V>(Query<K, V> query, K key) where K : notnull
    {
        if (stack.Count != 0)
        {
            if (Charge(1) is { } why) return Outcome<V>.Failure(why);
            if (RecordDependencies) (stack[^1].Dependencies ??= []).Add(new(query, key));
        }
        if (!tables.TryGetValue(query, out var untyped)) tables.Add(query, untyped = new Table<K, V>());
        var table = (Table<K, V>)untyped;
        if (table.Entries.TryGetValue(key, out var entry) && entry.Published)
        {
            table.Hits++;
            return entry.Result;
        }
        // 检查位于进入计算之前，命中路径无需换栈。
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack()) return OnFreshStack(query, key);
        return Resolve(query, key, table, entry);
    }

    /// <summary>长循环显式计步；返回失败时作者应立即返回该原因，框架也会拒绝发布成功。</summary>
    public Reason? Step(long count = 1)
    {
        if (count <= 0) throw new ArgumentOutOfRangeException(nameof(count));
        if (stack.Count == 0) throw new InvalidOperationException("只能在查询计算中计步。");
        return Charge(count);
    }
    private Reason? Charge(long count)
    {
        var frame = stack[^1];
        if (frame.BudgetFailure is not null) return frame.BudgetFailure;
        if (count > frame.Query.StepBudget - frame.Steps)
            return frame.BudgetFailure = new("query.budget", "查询步数预算耗尽。");
        frame.Steps += count;
        // 嵌套组及组外辅助查询消耗的步骤也属于外层组的工作。
        foreach (var session in sessions)
        {
            if (session.Failure is not null) return frame.BudgetFailure = session.Failure;
            if (count > session.Group.StepLimit - session.Steps)
                return frame.BudgetFailure = session.Failure = new("query.fixed-point-limit", "不动点步数上限耗尽。");
            session.Steps += count;
        }
        return null;
    }
    private Outcome<V> Resolve<K, V>(Query<K, V> query, K key, Table<K, V> table, Entry<K, V>? entry) where K : notnull
    {
        if (entry is not null)
        {
            var session = entry.Session;
            if (session is null) ThrowCycle(entry);
            var start = entry.Active >= 0 ? entry.Active : stack.FindIndex(e => e.Session == session);
            if (start < 0 || stack.Skip(start).Any(e => e.Session != session)) ThrowCycle(entry);
            if (entry.Active >= 0)
            {
                for (var i = start; i < stack.Count; i++) stack[i].Participant = true;
            }
            (entry.Dependents ??= []).Add(stack[^1]);
            if (entry.Participant) stack[^1].Participant = true;
            table.Hits++;
            return entry.Result;
        }
        Session? owner = null;
        ILattice<V>? lattice = null;
        var root = false;
        if (groups.TryGetValue(query, out var declaration))
        {
            // 组外调用可以独立求解同组的其他键；只有实际读取未完成值才检查环。
            owner = stack.Count != 0 && stack[^1].Session?.Group == declaration.Group ? stack[^1].Session : null;
            if (owner is null)
            {
                owner = new(declaration.Group);
                sessions.Add(owner);
                root = true;
            }
            lattice = ((FixedPointMember.Member<K, V>)declaration.Member).Lattice(key);
        }
        entry = new(query, key, table, lattice) { Session = owner };
        table.Entries.Add(key, entry);
        owner?.Entries.Add(entry);
        entry.Evaluate(this);
        if (owner is null)
        {
            // 外层组的上限耗尽造成的失败不属于这个查询，不记忆。
            if (entry.Why is not null && Exhausted) entry.Forget();
            else entry.Publish(null);
        }
        else
        {
            // 失败只属于这个键，立即成为最终结果；未读取近似值的成功计算也已是最终结果。
            // 上限耗尽之后的结果留给 Settle 统一处理。
            if (!Exhausted && (entry.Why is not null || !entry.Participant)) entry.Publish(null);
            if (!entry.Published && stack.Count != 0 && stack[^1].Session == owner)
                (entry.Dependents ??= []).Add(stack[^1]);
            owner.Enqueue(entry);
            if (root) Settle(owner);
        }
        if (entry.Participant && stack.Count != 0 && stack[^1].Session == owner)
            stack[^1].Participant = true;
        return entry.Result;
    }
    private void Settle(Session session)
    {
        // 只有依赖的近似值增长才重算读者；发现环时的首次计算按完成次序入队。
        while (!Exhausted && session.Work.TryDequeue(out var entry))
        {
            entry.Queued = false;
            if (entry.Published) continue;
            if (entry.Evaluate(this) && entry.Dependents is { } readers)
                foreach (var reader in readers) session.Enqueue(reader);
            if (entry.Why is not null && !Exhausted) entry.Publish(null);
        }
        // 本组上限耗尽：未完成的键都是洞。外层组耗尽：本组未完成的结果不记忆。
        foreach (var entry in session.Entries)
        {
            if (entry.Published) continue;
            if (session.Failure is null && Exhausted) entry.Forget();
            else entry.Publish(session.Failure);
        }
        foreach (var entry in session.Entries) entry.Dependents = null;
        sessions.Remove(session);
    }
    private bool Exhausted => sessions.Exists(s => s.Failure is not null);
    private void ThrowCycle(Entry entry)
    {
        var start = entry.Active >= 0 ? entry.Active : stack.FindIndex(e => e.Session == entry.Session);
        throw new QueryCycleException(stack.Skip(Math.Max(0, start)).Select(e => e.Address).Append(entry.Address).ToImmutableArray());
    }
    [MethodImpl(MethodImplOptions.NoInlining)]
    private Outcome<V> OnFreshStack<K, V>(Query<K, V> query, K key) where K : notnull
    {
        Outcome<V> result = default;
        ExceptionDispatchInfo? error = null;
        // 只传递异常，不改变作者错误的含义；父线程 Join 期间不访问上下文。
        var thread = new Thread(() =>
        {
            try
            {
                var table = (Table<K, V>)tables[query];
                table.Entries.TryGetValue(key, out var entry);
                result = Resolve(query, key, table, entry);
            }
            catch (Exception exception) { error = ExceptionDispatchInfo.Capture(exception); }
        }, 32 * 1024 * 1024);
        StackSwitches++;
        thread.Start();
        thread.Join();
        error?.Throw();
        return result;
    }
}
