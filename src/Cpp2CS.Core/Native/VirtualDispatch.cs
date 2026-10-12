namespace Cpp2CS.Native;

public sealed record VirtualCall(ulong Address, string Owner, int Slot, string Method, string Evidence);

public static class VirtualDispatch
{
    public static VirtualCall[] Recover(SsaSemantics semantics, Symbols symbols, HeaderLayout layouts, ManagedNames managed)
    {
        var result = new List<VirtualCall>();
        SsaValue Raw(string id) => semantics.Raw(semantics.Unalias(id));
        foreach (var instruction in semantics.Program.Instructions.Where(i => i.Call is not null))
        {
            var call = Raw(instruction.Call!);
            if (Raw(call.Inputs[0]) is not { Operation: "load", Width: 64 } target) continue;
            var (klass, offset) = SsaSemantics.AddressParts(semantics.Resolve(target.Inputs[1]));
            var receiver = semantics.Argument(call.Id, 0);
            if (klass is not { Kind: "field", Name: "klass", Offset: 0, Inputs: [var instance] } || instance.Key != receiver.Key || receiver.Type is null) continue;
            var owner = symbols.Display(receiver.Type);
            var nativeClass = receiver.Type.TrimEnd('*');
            if (!nativeClass.EndsWith("_o")) continue;
            var table = layouts.Members(nativeClass[..^2] + "_c").SingleOrDefault(f => f.Name == "vtable");
            if (table is null || offset < table.Offset) continue;
            var slotField = layouts.Members(table.Type).SingleOrDefault(f => f.Offset == offset - table.Offset && f.Type == "VirtualInvokeData");
            if (slotField is null) continue;
            var separator = slotField.Name.IndexOf('_', 1);
            if (separator < 0 || !int.TryParse(slotField.Name.AsSpan(1, separator - 1), out var slot)) continue;
            var name = slotField.Name[(separator + 1)..];
            var candidates = symbols.NamedMethods.GetValueOrDefault(owner + "$$" + name, []);
            NativeMethod? method = candidates.Length == 1 ? candidates[0] : null;
            if (method is null && candidates.Length == 0 && managed.SignatureOf(owner, name) is { } signature &&
                symbols.NativeType(signature.ReturnType) is { } returnType && signature.ParameterTypes.Length == 0)
                method = new(0, owner + "$$" + name, returnType, [new(receiver.Type, "__this"), new("MethodInfo*", "method")], "metadata virtual declaration");
            if (method is null) continue;
            if (method.Parameters.FirstOrDefault()?.Name != "__this" || method.Parameters.LastOrDefault()?.Type != "MethodInfo*") continue;
            var abi = new NativeAbi(layouts, managed).Classify(method);
            if (abi?.Arguments.Last().Pieces.ToArray() is not [{ Location: Cpp2CS.Abi.RegisterLocation register, Size: 8 }] ||
                !register.Name.StartsWith('X') || !int.TryParse(register.Name.AsSpan(1), out var index) || index > 7) continue;
            var info = Raw(call.Inputs[index + 2]);
            if (info is not { Operation: "load", Width: 64 }) continue;
            var (infoClass, infoOffset) = SsaSemantics.AddressParts(semantics.Resolve(info.Inputs[1]));
            if (infoClass.Key != klass.Key || infoOffset != offset + layouts.Members("VirtualInvokeData").Single(f => f.Name == "method").Offset) continue;
            semantics.VirtualMethods[call.Id] = method;
            semantics.Refresh();
            result.Add(new(instruction.Address, owner, slot, method.Name, "receiver.klass vtable slot and paired MethodInfo; unique declared method signature from matching Dumper metadata"));
        }
        return result.ToArray();
    }
}
