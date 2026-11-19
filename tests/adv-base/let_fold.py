# Source of tests/adv/{good,bad}_m34_let_fold*.ndjson (milestone 34): the
# Arena's perf/let-fold export (Lean v4.34.1, lean4export as the Arena runs
# it), edited in place:
#   good_m34_let_fold        bits 12 instead of bits 16: let d := bits 12 0;
#                            id (d + 0 = Nat.add d 0) (Eq.refl (d + 0))
#   bad_m34_let_fold_wrong   bits 12 too, and the right side Nat.add d 1
#                            (type and body): d + 0 = d + 1 is false
# The fold's arguments run past their probe, so literal folding over the
# let's value is skipped while its body is inferred (Lean's free variable
# guard); lazy delta must still decide both.
# Usage: python3 let_fold.py ARENA/good/perf/let-fold.ndjson OUTDIR
import json, sys
src, out = sys.argv[1], sys.argv[2]
L = [json.loads(l) for l in open(src)]
E = {o["ie"]: o for o in L if "ie" in o}
names = {}
for o in L:
    if "in" in o:
        names[o["in"]] = o.get("str") or o.get("num")
def full(i):
    if i == 0:
        return ""
    s = names[i]; p = full(s["pre"])
    return (p + "." if p else "") + str(s.get("str", s.get("i")))
def const(name):
    r = [o["ie"] for o in L if "const" in o and full(o["const"]["name"]) == name and o["const"]["us"] == []]
    assert len(r) == 1, (name, r)
    return r[0]
def dump(lines, path):
    open(path, "w").write("\n".join(json.dumps(o, separators=(",", ":")) for o in lines) + "\n")

# good: bits 16 -> bits 12 (4096 calls: past the fold probe)
g = [json.loads(json.dumps(o)) for o in L]
for o in g:
    if o.get("natVal") == "16":
        o["natVal"] = "12"
dump(g, f"{out}/good_m34_let_fold.ndjson")

# bad: `Nat.add X lit0` -> `Nat.add X lit1` in kernel_let_fold's type and
# value (the right side of the equation; Nat.add appears nowhere else in
# them). New nodes are appended with fresh ids, then the theorem.
b = [json.loads(json.dumps(o)) for o in L if "thm" not in o or full(o["thm"]["name"]) != "kernel_let_fold"]
for o in b:
    if o.get("natVal") == "16":
        o["natVal"] = "12"
thm = [o for o in L if "thm" in o and full(o["thm"]["name"]) == "kernel_let_fold"][0]["thm"]
nat_add = const("Nat.add")
let = E[thm["value"]]["letE"]
lit0 = E[let["value"]]["app"]["arg"]                 # bits 16 lit0: lit0
ofnat = E[E[lit0]["app"]["fn"]]["app"]["fn"]          # OfNat.ofNat Nat
instf = E[E[lit0]["app"]["arg"]]["app"]["fn"]         # instOfNatNat
n1 = [o["ie"] for o in L if o.get("natVal") == "1"][0]
nxt = [max(E) + 1]
def mk(kind, body):
    i = nxt[0]; nxt[0] += 1
    b.append({kind: body, "ie": i}); return i
lit1 = mk("app", {"arg": mk("app", {"arg": n1, "fn": instf}), "fn": mk("app", {"arg": n1, "fn": ofnat})})
memo = {}
changed = [0]
def sub(i):
    if i in memo:
        return memo[i]
    o = E[i]; r = i
    if "app" in o:
        a = o["app"]
        if a["arg"] == lit0 and "app" in E[a["fn"]] and E[a["fn"]]["app"]["fn"] == nat_add:
            changed[0] += 1
            r = mk("app", {"arg": lit1, "fn": sub(a["fn"])})
        else:
            f, x = sub(a["fn"]), sub(a["arg"])
            if (f, x) != (a["fn"], a["arg"]):
                r = mk("app", {"arg": x, "fn": f})
    elif "letE" in o:
        v = dict(o["letE"]); t, val, bd = sub(v["type"]), sub(v["value"]), sub(v["body"])
        if (t, val, bd) != (v["type"], v["value"], v["body"]):
            v.update(type=t, value=val, body=bd); r = mk("letE", v)
    elif "lam" in o or "forallE" in o:
        k = "lam" if "lam" in o else "forallE"
        v = dict(o[k]); t, bd = sub(v["type"]), sub(v["body"])
        if (t, bd) != (v["type"], v["body"]):
            v.update(type=t, body=bd); r = mk(k, v)
    memo[i] = r
    return r
nt = dict(thm); nt.update(type=sub(thm["type"]), value=sub(thm["value"]))
assert changed[0] == 2, changed
b.append({"thm": nt})
dump(b, f"{out}/bad_m34_let_fold_wrong.ndjson")
print("let-fold vectors written")
