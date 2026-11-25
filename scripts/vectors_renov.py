# Renovation vectors (python3 scripts/vectors_renov.py tests/adv-base/renov_unitLikeNested.ndjson tests/adv):
# unit-like types past 16 binders or nestings, and a recursor missing its minor
# and major premises, on lean-kernel-arena-beta's renovation/120_unitLikeNested
# export (Lean pr-release-16595-55bd690), kept as tests/adv-base/renov_unitLikeNested.ndjson.
import json, sys
base, out = sys.argv[1], sys.argv[2]
lines = [l for l in open(base).read().splitlines() if l.strip()]
assert lines[-1].startswith('{"thm"'); 
recs = [json.loads(l) for l in lines]

class B:
    def __init__(s):
        s.lines = list(lines)
        s.names = {}; s.nn = 0; s.ne = 0; s.nl = 0; s.ex = {}; s.lv = {}
        for r in recs:
            if 'in' in r:
                s.nn = max(s.nn, r['in'] + 1)
                if 'str' in r: s.names[(r['str']['pre'], r['str']['str'])] = r['in']
            if 'ie' in r:
                s.ne = max(s.ne, r['ie'] + 1)
                k = {kk: v for kk, v in r.items() if kk != 'ie'}
                s.ex[json.dumps(k, sort_keys=True)] = r['ie']
            if 'il' in r:
                s.nl = max(s.nl, r['il'] + 1)
                k = {kk: v for kk, v in r.items() if kk != 'il'}
                s.lv[json.dumps(k, sort_keys=True)] = r['il']
    def name(s, path):
        pre = 0
        for part in path.split('.'):
            key = (pre, part)
            if key not in s.names:
                s.names[key] = s.nn; s.lines.append(json.dumps({"in": s.nn, "str": {"pre": pre, "str": part}})); s.nn += 1
            pre = s.names[key]
        return pre
    def lvl(s, n):
        l = 0
        for _ in range(n):
            k = {"succ": l}; ks = json.dumps(k, sort_keys=True)
            if ks not in s.lv:
                s.lv[ks] = s.nl; s.lines.append(json.dumps({"il": s.nl, **k})); s.nl += 1
            l = s.lv[ks]
        return l
    def e(s, k):
        ks = json.dumps(k, sort_keys=True)
        if ks not in s.ex:
            s.ex[ks] = s.ne; s.lines.append(json.dumps({"ie": s.ne, **k})); s.ne += 1
        return s.ex[ks]
    def c(s, n, us=()): return s.e({"const": {"name": s.name(n), "us": [s.lvl(u) for u in us]}})
    def app(s, f, *a):
        for x in a: f = s.e({"app": {"fn": f, "arg": x}})
        return f
    def pi(s, ty, body, n='x'): return s.e({"forallE": {"binderInfo": "default", "body": body, "name": s.name(n), "type": ty}})
    def lam(s, ty, body, n='x'): return s.e({"lam": {"binderInfo": "default", "body": body, "name": s.name(n), "type": ty}})
    def bv(s, i): return s.e({"bvar": i})
    def sort(s, n): return s.e({"sort": s.lvl(n)})
    def proj(s, struct, i, x): return s.e({"proj": {"idx": i, "struct": x, "typeName": s.name(struct)}})
    def thm(s, n, ty, val, path):
        s.lines.append(json.dumps({"thm": {"all": [s.name(n)], "levelParams": [], "name": s.name(n), "type": ty, "value": val}}))
        open(path, 'w').write('\n'.join(s.lines) + '\n')

def eq(b, ty, x, y, lvl=1): return b.app(b.c('Eq', [lvl]), ty, x, y)
def refl(b, ty, x, lvl=1): return b.app(b.c('Eq.refl', [lvl]), ty, x)
def all_eq(b, T, name, path):
    # ∀ p q : T, p = q := fun p q => Eq.refl q
    ty = b.pi(T, b.pi(T, eq(b, T, b.bv(1), b.bv(0)), 'q'), 'p')
    val = b.lam(T, b.lam(T, refl(b, T, b.bv(0)), 'q'), 'p')
    b.thm(name, ty, val, path)

# 1. a 17- (and 40-) argument function into Unit is unit-like
for n in (17, 40):
    b = B(); T = b.c('Unit')
    for _ in range(n): T = b.pi(b.c('Bool'), T)
    all_eq(b, T, f'unitLikePi{n}', f'{out}/good_renov_unitlike_pi{n}.ndjson')
# 2. Wrap^20 Unit: T_k = Mixed Unit T_{k-1}
b = B(); T = b.c('Unit')
for _ in range(20): T = b.app(b.c('Mixed'), b.c('Unit'), T)
all_eq(b, T, 'unitLikeWrap20', f'{out}/good_renov_unitlike_wrap20.ndjson')
# ... and with Bool at the bottom it is not unit-like
b = B(); T = b.c('Bool')
for _ in range(20): T = b.app(b.c('Mixed'), b.c('Unit'), T)
all_eq(b, T, 'notUnitLikeWrap20', f'{out}/bad_renov_unitlike_wrap20_bool.ndjson')
# ... nor is a 17-argument function into Bool
b = B(); T = b.c('Bool')
for _ in range(17): T = b.pi(b.c('Bool'), T)
all_eq(b, T, 'notUnitLikePi17', f'{out}/bad_renov_unitlike_pi17_bool.ndjson')
# 3. a recursor missing its minor premise and its major premise:
# @Mixed.rec Unit Bool (fun _ => Bool) = fun m p => m p.1 p.2 p.3 p.4
for good in (True, False):
    b = B()
    U, Bo = b.c('Unit'), b.c('Bool')
    MT = b.app(b.c('Mixed'), U, Bo)
    eqUB = b.app(b.c('Eq', [2]), b.sort(1), U, Bo)
    mT = b.pi(Bo, b.pi(U, b.pi(b.c('True'), b.pi(eqUB, Bo))))
    FT = b.pi(mT, b.pi(MT, Bo))
    rec = b.app(b.c('Mixed.rec', [1]), U, Bo, b.lam(MT, Bo, 't'))
    if good:
        p = b.bv(0)
        body = b.app(b.bv(1), b.proj('Mixed', 0, p), b.proj('Mixed', 1, p), b.proj('Mixed', 2, p), b.proj('Mixed', 3, p))
    else:
        body = b.c('Bool.true')
    other = b.lam(mT, b.lam(MT, body, 'p'), 'm')
    ty = eq(b, FT, rec, other)
    b.thm('etaRecMinors' if good else 'etaRecMinorsBad', ty, refl(b, FT, rec), f'{out}/{"good" if good else "bad"}_renov_eta_rec_minors.ndjson')
    # the other orientation: drop the theorem, add the reversed one
    b.lines = [l for l in b.lines if not l.startswith('{"thm"') or '"etaRec' not in l and b.name('etaRecMinors' if good else 'etaRecMinorsBad') != json.loads(l)['thm']['name']]
    ty2 = eq(b, FT, other, rec)
    b.thm('etaRecMinorsR' if good else 'etaRecMinorsBadR', ty2, refl(b, FT, other), f'{out}/{"good" if good else "bad"}_renov_eta_rec_minors_r.ndjson')
