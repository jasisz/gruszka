#!/usr/bin/env python3
"""Milestone 59: a whnf memo across declarations, simulated per worker from
the cnt build's events (SK_WCNT=PREFIX writes PREFIX.w<i>.tsv).

A closed whnf of GHOST_TICKS or more (W line: decl, name epoch, name, ticks,
ns, start seq, end seq, result shape, result name closed, literal bytes)
hits when the same name was worked out earlier in this worker in an earlier
declaration (d < cur_decl) and stored by then; the whnfs nested in a hit are
not run. N lines: sampled name costs (1 in 64 misses of a closed value).
usage: m59_whnf.py PREFIX
"""
import glob, statistics, sys
from collections import Counter

REPRO = {"nat", "bignat", "str", "const", "capp", "sort", "lam"}


def pct(xs, q):
    if not xs:
        return 0
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(q * len(xs)))]


def worker(path):
    ev, names, total = [], [], 0
    for l in open(path):
        f = l.rstrip("\n").split("\t")
        if f[0] == "W":
            ev.append((int(f[6]), int(f[7]), int(f[1]), (int(f[2]), int(f[3])), int(f[4]), int(f[5]), f[8], f[9] == "1", int(f[10])))
        elif f[0] == "X":
            ev.append((int(f[6]), int(f[7]), int(f[1]), None, int(f[4]), int(f[5]), "open", False, 0))
        elif f[0] == "T":
            total = int(f[1])
        elif f[0] == "N":
            names.append((int(f[1]), int(f[2]), int(f[3]), int(f[4])))
    ev.sort()
    res = {}
    for mode in ("all", "repro"):
        stores = sorted(range(len(ev)), key=lambda i: ev[i][1])
        si, memo, skipped = 0, {}, set()
        hit_t, hit_ns, hits, skip_until = [], [], Counter(), -1
        top_t = 0
        for i, (s0, s1, d, key, dt, ns, shape, rcl, by) in enumerate(ev):
            while si < len(stores) and ev[stores[si]][1] <= s0:
                j = stores[si]
                si += 1
                e = ev[j]
                if j in skipped or e[3] is None:
                    continue
                if mode == "repro" and not (e[7] and e[6] in REPRO):
                    continue
                if e[3] not in memo or memo[e[3]][0] > e[2]:
                    memo[e[3]] = (e[2], e[8])
            if s0 <= skip_until:
                skipped.add(i)
                continue
            if key is not None and key in memo and memo[key][0] < d:
                hit_t.append(dt)
                hit_ns.append(ns)
                hits[shape] += 1
                skip_until = s1
        # ticks of the outermost events (nested ones counted in them)
        end = -1
        for (s0, s1, d, key, dt, *_r) in ev:
            if s0 > end:
                top_t += dt
                end = s1
        byts = sum(24 + v[1] for v in memo.values())
        res[mode] = dict(hits=len(hit_t), saved=sum(hit_t), saved_ns=sum(hit_ns), hit_t=hit_t, hit_ns=hit_ns, shapes=hits, bytes=byts, keys=len(memo))
    return ev, names, total, res


def main():
    pre = sys.argv[1]
    files = sorted(glob.glob(pre + ".w*.tsv"))
    print(f"# {pre}: {len(files)} workers")
    agg = {m: dict(hits=0, saved=0, saved_ns=0, hit_t=[], hit_ns=[], bytes=0, shapes=Counter()) for m in ("all", "repro")}
    tot_t, nev, nclosed, names, shapes = 0, 0, 0, [], Counter()
    per = []
    for p in files:
        ev, nm, total, res = worker(p)
        tot_t += total
        nev += len(ev)
        nclosed += sum(1 for e in ev if e[3] is not None)
        shapes.update(e[6] for e in ev)
        names += nm
        for m in agg:
            for k in ("hits", "saved", "saved_ns", "bytes"):
                agg[m][k] += res[m][k]
            agg[m]["hit_t"] += res[m]["hit_t"]
            agg[m]["hit_ns"] += res[m]["hit_ns"]
            agg[m]["shapes"].update(res[m]["shapes"])
        per.append((p.rsplit(".w", 1)[1], total, res["repro"]["saved"], res["all"]["saved"]))
    print(f"events >=GHOST: {nev} (closed named {nclosed}); worker ticks total {tot_t}")
    print(f"result shapes: {dict(shapes)}")
    name_ns = [n[0] for n in names]
    name_cost_total = 64 * sum(name_ns)
    print(f"name samples {len(names)}: median {pct(name_ns, .5)} ns, p90 {pct(name_ns, .9)} ns, mean {statistics.mean(name_ns) if names else 0:.0f} ns; median nodes {pct([n[2] for n in names], .5)}; closed {sum(1 for n in names if n[3] == 1)}/{len(names)}; est. all lookups {name_cost_total/1e9:.2f} s")
    for m in ("all", "repro"):
        a = agg[m]
        print(f"[{m}] hits {a['hits']}  saved ticks {a['saved']} = {100*a['saved']/max(tot_t,1):.2f}% of worker ticks; saved {a['saved_ns']/1e9:.2f} s;"
              f" hit ticks median {pct(a['hit_t'],.5)} p90 {pct(a['hit_t'],.9)} max {max(a['hit_t'], default=0)};"
              f" hit ns median {pct(a['hit_ns'],.5)}; memo bytes {a['bytes']}; shapes {dict(a['shapes'])}")
    print("per worker (worker, ticks, saved repro %, saved all %):")
    for w, t, r, al in per:
        print(f"  w{w}\t{t}\t{100*r/max(t,1):.2f}\t{100*al/max(t,1):.2f}")


main()
