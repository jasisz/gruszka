"""Damages the INDEX section of a Susz 1 file (Susz 1 spec, section 6a),
for tests/only.sh: python3 -I indexbad.py MODE IN OUT [NAME]. MAIN and
PROOFS are left as they are, so a full check of the damaged file gives the
verdict of the original; a subset check that relies on the damaged entry
must end as index invalid.

Modes:
  garbage  INDEX's bytes all replaced
  offset   entry 0's offset one byte later: every offset after it is wrong
  decl     NAME's entry in the name table gives another declaration
  kind     the kind of NAME's declaration entry changed (0 and 1 swapped,
           or 0 for any other kind)

Copied from Pestka (tests/indexbad.py); Gruszka's milestone 26 adds:
  later    NAME's entry in the name table gives the next declaration
  block    the proof block length of NAME's entry one byte longer
  order    the first two keys of the name table swapped (out of order)
  range    the first key's declaration one past the last
  count    one entry more than the file has declarations
  shared   a key's shared count one less than its common prefix
  kindof   NAME: print the INDEX kind of NAME's declaration (no OUT)
  keys     (no OUT): print each declaration's first key,
           dotted, one per line, in declaration order (no OUT written)
"""
import struct
import sys

MAGIC = b"SUSZ\r\n\x1a\n"


def rv(b, p):
    v, s = 0, 0
    while True:
        x = b[p]
        p += 1
        v |= (x & 127) << s
        if x < 128:
            return v, p
        s += 7


def wv(n):
    out = bytearray()
    while True:
        x = n & 127
        n >>= 7
        if n == 0:
            out.append(x)
            return bytes(out)
        out.append(x | 128)


def key(name):
    out = bytearray()
    for c in name.split("."):
        if c and c.isdigit() and len(c) < 20:
            out += b"\x02" + wv(int(c))
        else:
            u = c.encode()
            out += b"\x01" + wv(len(u)) + u
    return bytes(out)


def parse(b):
    p = 0
    nd, p = rv(b, p)
    entries = []
    for _ in range(nd):
        k = b[p]
        p += 1
        d, p = rv(b, p)
        l = None
        if k == 6:
            l, p = rv(b, p)
        entries.append([k, d, l])
    nn, p = rv(b, p)
    names, cur = [], b""
    for _ in range(nn):
        sh, p = rv(b, p)
        sl, p = rv(b, p)
        cur = cur[:sh] + b[p : p + sl]
        p += sl
        d, p = rv(b, p)
        names.append([cur, d])
    return entries, names


def dotted(k):
    out, p = [], 0
    while p < len(k):
        t = k[p]
        p += 1
        n, p = rv(k, p)
        if t == 2:
            out.append(str(n))
        else:
            out.append(k[p : p + n].decode())
            p += n
    return ".".join(out)


def encode(entries, names, short=-1):
    out = bytearray(wv(len(entries)))
    for k, d, l in entries:
        out.append(k)
        out += wv(d)
        if k == 6:
            out += wv(l)
    out += wv(len(names))
    prev = b""
    for j, (k, d) in enumerate(names):
        sh = 0
        while sh < len(prev) and sh < len(k) and prev[sh] == k[sh]:
            sh += 1
        if j == short and sh > 0:
            sh -= 1
        out += wv(sh) + wv(len(k) - sh) + k[sh:] + wv(d)
        prev = k
    return bytes(out)


def main():
    mode, src = sys.argv[1], sys.argv[2]
    dst = sys.argv[3] if mode not in ("keys", "kindof") else None
    b = bytearray(open(src, "rb").read())
    assert b[:8] == MAGIC
    n = len(b)
    tl = struct.unpack("<I", b[n - 8 : n - 4])[0]
    t = b[n - tl :]
    k = struct.unpack("<I", t[16:20])[0]
    secs = []
    for i in range(k):
        sid, flags, _, off, ln = struct.unpack("<HHIQQ", t[20 + 24 * i : 44 + 24 * i])
        secs.append([sid, flags, bytearray(b[off : off + ln])])
    idx = [s for s in secs if s[0] == 5]
    if not idx:
        sys.exit(3)
    body = idx[0][2]
    short = -1
    if mode == "garbage":
        body[:] = bytes((i * 37 + 11) & 255 for i in range(len(body)))
    else:
        entries, names = parse(bytes(body))
        if mode == "kindof":
            want = key(sys.argv[3])
            print(next(entries[d][0] for k, d in names if k == want))
            return
        if mode == "keys":
            first = {}
            for k, d in names:
                first.setdefault(d, k)
            for d in range(len(entries)):
                print(dotted(first[d]) if d in first else "")
            return
        if mode == "offset":
            entries[0][1] += 1
        elif mode == "order":
            names[0], names[1] = names[1], names[0]
        elif mode == "range":
            names[0][1] = len(entries)
        elif mode == "count":
            entries.append([0, 0, None])
        elif mode == "shared":
            short = next(j for j in range(1, len(names)) if names[j][0][:1] == names[j - 1][0][:1])
        else:
            want = key(sys.argv[4])
            hit = [x for x in names if x[0] == want]
            if not hit:
                sys.exit("no name " + sys.argv[4])
            d = hit[0][1]
            if mode == "decl":
                hit[0][1] = d - 1 if d > 0 else d + 1
            elif mode == "later":
                hit[0][1] = d + 1
            elif mode == "block":
                e = entries[d]
                if e[0] != 6:
                    sys.exit(3)
                e[2] += 1
            elif mode == "kind":
                e = entries[d]
                if e[0] == 6:
                    sys.exit(3)
                e[0] = {0: 1, 1: 0}.get(e[0], 0)
            else:
                sys.exit("unknown mode " + mode)
        body[:] = encode(entries, names, short)
    out = bytearray(MAGIC + struct.pack("<HHI", 1, 0, 0))
    dirs, off = b"", 16
    for sid, flags, sb in secs:
        out += sb
        dirs += struct.pack("<HHIQQ", sid, flags, 0, off, len(sb))
        off += len(sb)
    tr = bytes(t[:16]) + struct.pack("<I", len(secs)) + dirs
    open(dst, "wb").write(bytes(out + tr + struct.pack("<I", len(tr) + 8) + b"ZSUS"))


main()
