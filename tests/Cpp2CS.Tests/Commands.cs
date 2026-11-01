namespace Cpp2CS.Tests;

internal enum Gate { None, Unit, Image, ImageOutput }

/// <summary>对照器内的自检命令声明（保留在原文件中；当前入口只接入 execute）。</summary>
[AttributeUsage(AttributeTargets.Method)]
internal sealed class CommandAttribute(string name, string description) : Attribute
{
    public string Name => name;
    public string Description => description;
    public string Arguments { get; init; } = "";
    public Gate Gate { get; init; }
}
