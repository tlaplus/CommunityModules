"""Checks the golden bytes in tests/CBORTests.tla against a second CBOR encoder.

    python3 tests/CBORTests/fixtures.py

Run it by hand after changing the encoding or a golden row; CI does not run it. It needs only the
standard library. If the third-party decoder cbor2 (pip install cbor2) is importable, it also prints
how cbor2 reads every golden, so a reviewer can check their meaning independently of TLC.

The encoder below is a second implementation of the encoding table in modules/CBOR.tla that shares
no code with CBOR.java. CBORTests.tla states each golden as an ASSUME that calls Golden or SameBytes
with the golden's name and its bytes as a TLA+ sequence of hex literals (<<\\h82, \\h61, ...>>).
TLC checks that ToCBOR writes those bytes; this script checks that they are the bytes this encoder
writes for the value of the same name. It exits non-zero on a mismatch, printing the expected
sequence, on a name it does not know, and on a value it has that no ASSUME states.
"""
import os
import re
import struct
import sys

TAG_MODEL_VALUE = 39
TAG_SET = 258
TAG_FUNCTION = 33000


class MV:
    def __init__(self, name): self.name = name


class Set:
    def __init__(self, *elems): self.elems = elems


class Fn:
    """A function given by its (x, f[x]) pairs."""
    def __init__(self, *pairs): self.pairs = pairs


def head(major, n):
    if n < 24:
        return bytes([major << 5 | n])
    for ai, fmt, limit in ((24, ">B", 0xFF), (25, ">H", 0xFFFF), (26, ">I", 0xFFFFFFFF), (27, ">Q", 2**64 - 1)):
        if n <= limit:
            return bytes([major << 5 | ai]) + struct.pack(fmt, n)
    raise ValueError(n)


def keyed(pairs, as_map):
    entries = sorted((enc(k), v) for k, v in pairs)
    assert all(a[0] != b[0] for a, b in zip(entries, entries[1:])), "duplicate key"
    out = head(5, len(entries)) if as_map else head(6, TAG_FUNCTION) + head(4, len(entries))
    for k, v in entries:
        out += k + enc(v) if as_map else head(4, 2) + k + enc(v)
    return out


def function(pairs):
    keys = [k for k, _ in pairs]
    if sorted(k for k in keys if type(k) is int) == list(range(1, len(keys) + 1)):
        return enc(tuple(v for _, v in sorted(pairs, key=lambda p: p[0])))
    return keyed(pairs, as_map=all(type(k) is str for k in keys))


def enc(v):
    if type(v) is bool:
        return b"\xf5" if v else b"\xf4"
    if type(v) is int:
        assert -(2**31) <= v < 2**31, "TLC integers are 32-bit"
        return head(0, v) if v >= 0 else head(1, -1 - v)
    if type(v) is str:
        b = v.encode("utf-8")
        return head(3, len(b)) + b
    if isinstance(v, MV):
        return head(6, TAG_MODEL_VALUE) + enc(v.name)
    if isinstance(v, Set):
        items = sorted(set(enc(e) for e in v.elems))
        return head(6, TAG_SET) + head(4, len(items)) + b"".join(items)
    if isinstance(v, tuple):
        return head(4, len(v)) + b"".join(enc(e) for e in v)
    if isinstance(v, dict):
        return function(list(v.items()))
    if isinstance(v, Fn):
        return function(list(v.pairs))
    raise TypeError(type(v))


MODEL_VALUE = MV("ModelValue")  # tests/AllTests.cfg: CONSTANT ModelValueConstant = ModelValue

S1 = {"x": 0, "y": Set()}
S2 = {"x": 1, "y": Set(MODEL_VALUE)}
LOCATION = {"beginLine": 5, "beginColumn": 9, "endLine": 5, "endColumn": 33, "module": "T"}

# name -> value. CBORTests.tla states each value again in TLA+, next to its bytes.
GOLDEN = {
    "int": (0, 23, 24, 255, 256, 65535, 65536, 2147483647, -1, -24, -25, -256, -257, -2147483648),
    "bool": (True, False),
    "string": ("", "a", "\u00fc", "\u65e5\u672c", "\U0001F600"),
    "modelvalue": MODEL_VALUE,
    "set": Set(100, -1, 10),
    "set-strings": Set("cbor-zz", "cbor-a", "cbor-aa"),
    "set-nested": Set(Set(), Set(1), Set(1, 2), Set(2)),
    "emptyset": Set(),
    "interval": Set(1, 2, 3),
    "seq": ("a", "b"),
    "empty": (),
    "record": {"cborzz": 1, "cbora": 2, "cboraa": 3},
    "fcn-int": Fn((0, "x"), (1, "y")),
    "fcn-tuple": Fn(((1, 2), 3), ((2, 1), 3)),
    "fcn-set": Fn((Set(), 0), (Set(1), 1)),
    "fcn-record": Fn(({"a": 1}, 1), ({"a": 2}, 2)),
    "fcn-modelvalue": Fn((MODEL_VALUE, 0)),
    "trace": {"counterexample": {"state": Set((1, S1), (2, S2)),
                                 "action": Set(((1, S1), {"name": "Next", "location": LOCATION}, (2, S2)))},
              "vars": Set("x", "y")},
}

NAME = re.compile(r'\b(?:Golden|SameBytes)\("([^"]+)"')
HEX_SEQUENCE = re.compile(r'<<\s*(\\h[0-9a-fA-F]{2}(?:\s*,\s*\\h[0-9a-fA-F]{2})*)\s*>>')


def tla(data):
    """data as a TLA+ sequence of hex literals, 16 to a line."""
    lines = [", ".join(f"\\h{b:02x}" for b in data[i:i + 16]) for i in range(0, len(data), 16)]
    return "<<" + ",\n  ".join(lines) + ">>"


def statements(text):
    """Yields each top-level unit of the module, which starts at column 0, with its first line number."""
    line = 1
    for chunk in re.split(r"\n(?=\S)", text):
        yield line, chunk
        line += chunk.count("\n") + 1


def check(path):
    failures = []
    seen = set()
    for line, stmt in statements(open(path, encoding="ascii").read()):
        names = NAME.findall(stmt)
        if not names:
            continue
        literals = HEX_SEQUENCE.findall(stmt)
        if len(set(names)) != 1 or len(literals) != 1:
            failures.append(f"line {line}: expected one golden name and one hex sequence, found {names} and "
                            f"{len(literals)} sequences")
            continue
        name = names[0]
        if name not in GOLDEN:
            failures.append(f"line {line}: no value for the golden {name!r}")
            continue
        seen.add(name)
        stated = bytes(int(h[2:], 16) for h in re.findall(r"\\h[0-9a-fA-F]{2}", literals[0]))
        expected = enc(GOLDEN[name])
        if stated == expected:
            print(f"ok   {name} (line {line})")
        else:
            failures.append(f"line {line}: the bytes of {name!r} differ; this encoder writes\n{tla(expected)}")
    failures += [f"no ASSUME states the golden {name!r}" for name in GOLDEN if name not in seen]
    for f in failures:
        print("FAIL " + f)
    return not failures


def show_cbor2():
    try:
        import cbor2
    except ImportError:
        return
    print("\ncbor2 reads the goldens as:")
    for name, value in GOLDEN.items():
        try:
            text = repr(cbor2.loads(enc(value)))
        except cbor2.CBORDecodeError as e:
            text = f"error: {e}"
        print(f"  {name}: {text if len(text) <= 200 else text[:200] + '...'}")


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    ok = check(sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, os.pardir, "CBORTests.tla"))
    show_cbor2()
    sys.exit(0 if ok else 1)
