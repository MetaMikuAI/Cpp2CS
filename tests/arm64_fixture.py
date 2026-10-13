"""既有单指令数据用例的显式环境；BTI 兼容性由专门用例检查。"""


def with_arm_fixture_environment(request):
    if request.get("arch") != "arm64" or request.get("evaluate") is False:
        return request
    assert "btype" not in request.get("slots", {}) and "codePages" not in request, request
    address = int(request["address"], 16)
    return dict(request, slots=dict(request.get("slots", {}), btype="0x0"),
                codePages=[dict(address=hex(address & ~4095), guarded=False)])


def checked_arm_fixture_result(request, result):
    if request.get("arch") != "arm64" or request.get("evaluate") is False or not result.get("supported"):
        return result
    word = int.from_bytes(bytes.fromhex(request["bytes"]), "little")
    expected = 0
    if result["Outcome"] == "Normal":
        if word & 0xFFFFFC1F == 0xD61F0000:
            expected = 1
        elif word & 0xFFFFFC1F == 0xD63F0000:
            expected = 2
    assert int(result["slots"]["btype"], 16) == expected, (request, result)
    return dict(result, slots={name: value for name, value in result["slots"].items() if name != "btype"})
