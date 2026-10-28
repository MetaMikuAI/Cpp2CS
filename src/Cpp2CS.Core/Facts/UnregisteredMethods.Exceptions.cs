using System.Text;

namespace Cpp2CS.Facts;

public sealed partial class UnregisteredMethods
{
    /// <summary>异常区间使用函数内偏移；动作链保留顺序、筛选值和重定位后的类型身份。</summary>
    internal static string ExceptionShape(CodeFunction function, Func<ulong, ulong?> relocatedPointer)
    {
        var text = new StringBuilder();
        foreach (var region in function.ExceptionRegions)
        {
            if (region.Start < function.Start || region.End > function.End || region.End < region.Start
                || region.LandingPad != 0 && !function.Contains(region.LandingPad)
                || (region.ActionOffset == 0) != (region.Actions.Length == 0)) return Exact();
            text.Append("EH:").Append(region.Start - function.Start).Append(':').Append(region.End - function.Start)
                .Append(':').Append(region.LandingPad == 0 ? "none" : (region.LandingPad - function.Start).ToString()).Append(';');
            for (var i = 0; i < region.Actions.Length; i++)
            {
                var action = region.Actions[i];
                if (action.Filter < 0 || (action.NextOffset == 0) != (i == region.Actions.Length - 1)) return Exact();
                ulong type = 0;
                if (action.Filter == 0)
                {
                    if (action.Kind != "cleanup" || action.TypeInfo is not null) return Exact();
                }
                else if (action.TypeInfo == 0)
                {
                    if (action.Kind != "catch-all") return Exact();
                }
                else
                {
                    if (action.Kind != "typed-catch" || action.TypeInfo is not > 0
                        || relocatedPointer(action.TypeInfo.Value) is not { } resolved || resolved == 0) return Exact();
                    type = resolved;
                }
                text.Append("action:").Append(action.Filter).Append(':').Append(action.Kind).Append(':').Append(type.ToString("x")).Append(';');
            }
        }
        return text.ToString();

        string Exact()
        {
            var original = new StringBuilder("EH-exact:").Append(function.Start).Append(';');
            foreach (var region in function.ExceptionRegions)
            {
                original.Append(region);
                foreach (var action in region.Actions) original.Append(action);
            }
            return original.ToString();
        }
    }
}
