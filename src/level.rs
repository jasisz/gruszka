//! Universe levels: a per-worker interner on top of the global (MAIN) level
//! table, Lean's simplifying constructors, normalization, equivalence and
//! `is_geq`. Equal structure means equal id, in both tables. The worker
//! table is never cleared, so memos keyed by level ids stay valid.

use rustc_hash::{FxHashMap, FxHashSet};

pub const ZERO: u32 = 0;
pub const K_ZERO: u8 = 0;
pub const K_SUCC: u8 = 1;
pub const K_MAX: u8 = 2;
pub const K_IMAX: u8 = 3;
pub const K_PARAM: u8 = 4;

pub struct Levels<'e> {
    g: &'e [(u8, u32, u32)],
    gmap: &'e FxHashMap<(u8, u32, u32), u32>,
    loc: Vec<(u8, u32, u32)>,
    lmap: FxHashMap<(u8, u32, u32), u32>,
    norm_memo: FxHashMap<u32, u32>,
    /// `geq_cases` results, per pair of normal forms
    cases_memo: FxHashMap<(u32, u32), bool>,
}

impl<'e> Levels<'e> {
    pub fn new(g: &'e [(u8, u32, u32)], gmap: &'e FxHashMap<(u8, u32, u32), u32>) -> Levels<'e> {
        Levels { g, gmap, loc: Vec::new(), lmap: FxHashMap::default(), norm_memo: FxHashMap::default(), cases_memo: FxHashMap::default() }
    }
    /// Milestone 37: bytes held (room included)
    pub fn held_bytes(&self) -> usize {
        self.loc.capacity() * 12 + self.lmap.capacity() * 17 + self.norm_memo.capacity() * 9 + self.cases_memo.capacity() * 9
    }
    /// Worker-made levels and memo entries.
    pub fn len(&self) -> usize {
        self.loc.len() + self.norm_memo.len() + self.cases_memo.len()
    }
    #[inline(always)]
    pub fn get(&self, l: u32) -> (u8, u32, u32) {
        let gl = self.g.len() as u32;
        if l < gl { self.g[l as usize] } else { self.loc[(l - gl) as usize] }
    }
    pub fn kind(&self, l: u32) -> u8 {
        self.get(l).0
    }
    pub fn mk(&mut self, k: u8, a: u32, b: u32) -> u32 {
        let key = (k, a, b);
        if let Some(&x) = self.gmap.get(&key) {
            return x;
        }
        if let Some(&x) = self.lmap.get(&key) {
            return x;
        }
        let id = self.g.len() as u32 + self.loc.len() as u32;
        self.loc.push(key);
        self.lmap.insert(key, id);
        id
    }
    pub fn succ(&mut self, l: u32) -> u32 {
        self.mk(K_SUCC, l, 0)
    }
    pub fn param(&mut self, canon_name: u32) -> u32 {
        self.mk(K_PARAM, canon_name, 0)
    }
    pub fn is_zero(&self, l: u32) -> bool {
        self.kind(l) == K_ZERO
    }
    /// Zero for every assignment, by the reference kernel's syntactic test
    /// (Pestka's `normalizesToZero`): an imax with a zero right side is zero.
    pub fn zeroish(&self, l: u32) -> bool {
        let (k, a, b) = self.get(l);
        match k {
            K_ZERO => true,
            K_MAX => self.zeroish(a) && self.zeroish(b),
            K_IMAX => self.zeroish(b),
            _ => false,
        }
    }
    pub fn is_not_zero(&self, l: u32) -> bool {
        let (k, a, b) = self.get(l);
        match k {
            K_ZERO | K_PARAM => false,
            K_SUCC => true,
            K_MAX => self.is_not_zero(a) || self.is_not_zero(b),
            _ => self.is_not_zero(b),
        }
    }
    pub fn to_offset(&self, mut l: u32) -> (u32, u32) {
        let mut k = 0;
        loop {
            let (kk, a, _) = self.get(l);
            if kk == K_SUCC {
                l = a;
                k += 1;
            } else {
                return (l, k);
            }
        }
    }
    pub fn is_explicit(&self, l: u32) -> bool {
        self.is_zero(self.to_offset(l).0)
    }
    pub fn succ_n(&mut self, mut l: u32, n: u32) -> u32 {
        for _ in 0..n {
            l = self.succ(l);
        }
        l
    }
    /// Lean's `mk_max` (with simplifications).
    pub fn max(&mut self, l1: u32, l2: u32) -> u32 {
        if self.is_explicit(l1) && self.is_explicit(l2) {
            return if self.to_offset(l1).1 >= self.to_offset(l2).1 { l1 } else { l2 };
        }
        if l1 == l2 {
            return l1;
        }
        if self.is_zero(l1) {
            return l2;
        }
        if self.is_zero(l2) {
            return l1;
        }
        let (k2, a2, b2) = self.get(l2);
        if k2 == K_MAX && (a2 == l1 || b2 == l1) {
            return l2;
        }
        let (k1, a1, b1) = self.get(l1);
        if k1 == K_MAX && (a1 == l2 || b1 == l2) {
            return l1;
        }
        let p1 = self.to_offset(l1);
        let p2 = self.to_offset(l2);
        if p1.0 == p2.0 {
            return if p1.1 > p2.1 { l1 } else { l2 };
        }
        self.mk(K_MAX, l1, l2)
    }
    /// Lean's `mk_imax` (with simplifications).
    pub fn imax(&mut self, l1: u32, l2: u32) -> u32 {
        if self.is_not_zero(l2) {
            self.max(l1, l2)
        } else if self.is_zero(l2) || self.is_zero(l1) || self.get(l1) == (K_SUCC, ZERO, 0) {
            l2
        } else if l1 == l2 {
            l1
        } else {
            self.mk(K_IMAX, l1, l2)
        }
    }

    fn push_max_args(&self, l: u32, out: &mut Vec<u32>) {
        let (k, a, b) = self.get(l);
        if k == K_MAX {
            self.push_max_args(a, out);
            self.push_max_args(b, out);
        } else {
            out.push(l);
        }
    }

    /// Lean's `is_norm_lt`: a total order on levels (parameters by
    /// canonical name id, which is consistent within one file).
    fn norm_cmp(&self, a: u32, b: u32) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        if a == b {
            return Equal;
        }
        let (l1, o1) = self.to_offset(a);
        let (l2, o2) = self.to_offset(b);
        if l1 != l2 {
            let (k1, a1, b1) = self.get(l1);
            let (k2, a2, b2) = self.get(l2);
            if k1 != k2 {
                return k1.cmp(&k2);
            }
            match k1 {
                K_PARAM => a1.cmp(&a2),
                K_MAX | K_IMAX => {
                    if a1 != a2 {
                        self.norm_cmp(a1, a2)
                    } else {
                        self.norm_cmp(b1, b2)
                    }
                }
                _ => Equal,
            }
        } else {
            o1.cmp(&o2)
        }
    }

    pub fn normalize(&mut self, l: u32) -> u32 {
        if let Some(&r) = self.norm_memo.get(&l) {
            return r;
        }
        let r = self.normalize_core(l);
        self.norm_memo.insert(l, r);
        r
    }

    fn normalize_core(&mut self, l: u32) -> u32 {
        let (r, k) = self.to_offset(l);
        let (kind, a, b) = self.get(r);
        match kind {
            K_ZERO | K_PARAM => l,
            K_IMAX => {
                let l1 = self.normalize(a);
                let l2 = self.normalize(b);
                let im = self.imax(l1, l2);
                // an imax that became a max (its right side is not zero) is
                // normalized as one: `imax u 1` and `max u 1` have one form
                let im = self.succ_n(im, k);
                if self.kind(self.to_offset(im).0) == K_MAX { self.normalize(im) } else { im }
            }
            _ => {
                // K_MAX
                let mut todo = Vec::new();
                self.push_max_args(r, &mut todo);
                let mut args = Vec::new();
                for x in todo {
                    let n = self.normalize(x);
                    self.push_max_args(n, &mut args);
                }
                args.sort_by(|x, y| self.norm_cmp(*x, *y));
                let mut rargs: Vec<u32> = Vec::new();
                let mut i = 0;
                if self.is_explicit(args[i]) {
                    while i + 1 < args.len() && self.is_explicit(args[i + 1]) {
                        i += 1;
                    }
                    let kk = self.to_offset(args[i]).1;
                    let mut j = i + 1;
                    while j < args.len() {
                        if self.to_offset(args[j]).1 >= kk {
                            break;
                        }
                        j += 1;
                    }
                    if j < args.len() {
                        i += 1;
                    }
                }
                rargs.push(args[i]);
                let mut prev = self.to_offset(args[i]);
                i += 1;
                while i < args.len() {
                    let cur = self.to_offset(args[i]);
                    if prev.0 == cur.0 {
                        if prev.1 < cur.1 {
                            prev = cur;
                            rargs.pop();
                            rargs.push(args[i]);
                        }
                    } else {
                        prev = cur;
                        rargs.push(args[i]);
                    }
                    i += 1;
                }
                for x in rargs.iter_mut() {
                    *x = self.succ_n(*x, k);
                }
                // mk_big_max
                let mut acc = *rargs.last().unwrap();
                for idx in (0..rargs.len() - 1).rev() {
                    acc = self.max(rargs[idx], acc);
                }
                acc
            }
        }
    }

    /// Equal by Lean's normal forms. `Some(false)` only when no `imax` is
    /// left in them, where the normal forms decide; `None` when an `imax`
    /// is left (complete comparison: `geq_cases` both ways).
    pub fn equiv3(&mut self, a: u32, b: u32) -> Option<bool> {
        if a == b {
            return Some(true);
        }
        let na = self.normalize(a);
        let nb = self.normalize(b);
        if na == nb {
            return Some(true);
        }
        if !self.has_imax(na) && !self.has_imax(nb) {
            return Some(false);
        }
        None
    }

    /// Lean's `is_def_eq` on levels (normal forms only): the cheap,
    /// incomplete test for shortcuts whose "no" only means "not shown".
    pub fn equiv_fast(&mut self, a: u32, b: u32) -> bool {
        self.equiv3(a, b) == Some(true)
    }

    /// `a >= b` by Lean's `is_geq`, which decides it when no `imax` is left
    /// in the normal forms; `None` otherwise (then `geq_cases`).
    pub fn geq3(&mut self, a: u32, b: u32) -> Option<bool> {
        let a = self.normalize(a);
        let b = self.normalize(b);
        if self.geq_core(a, b) {
            return Some(true);
        }
        if !self.has_imax(a) && !self.has_imax(b) {
            return Some(false);
        }
        None
    }

    fn geq_fast(&mut self, a: u32, b: u32) -> bool {
        let a = self.normalize(a);
        let b = self.normalize(b);
        self.geq_core(a, b)
    }

    fn has_imax(&self, l: u32) -> bool {
        let (k, a, b) = self.get(l);
        match k {
            K_IMAX => true,
            K_SUCC => self.has_imax(a),
            K_MAX => self.has_imax(a) || self.has_imax(b),
            _ => false,
        }
    }

    /// The parameters that decide whether `l` is zero: `None` when it never
    /// is (`is_not_zero`), else a set D with `l = 0` exactly when every
    /// parameter in D is 0 (empty: always zero). dec(p) = {p},
    /// dec(succ _) = never, dec(max c d) = dec(c) ∪ dec(d) (never when a
    /// side is), dec(imax c d) = dec(d), dec(0) = {}.
    fn dec_set(&self, l: u32, memo: &mut FxHashMap<u32, Option<Vec<u32>>>) -> Option<Vec<u32>> {
        if let Some(r) = memo.get(&l) {
            return r.clone();
        }
        let (k, a, b) = self.get(l);
        let r = match k {
            K_ZERO => Some(Vec::new()),
            K_PARAM => Some(vec![a]),
            K_SUCC => None,
            K_IMAX => self.dec_set(b, memo),
            _ => match (self.dec_set(a, memo), self.dec_set(b, memo)) {
                (Some(mut x), Some(y)) => {
                    x.extend(y);
                    x.sort_unstable();
                    x.dedup();
                    Some(x)
                }
                _ => None,
            },
        };
        memo.insert(l, r.clone());
        r
    }

    /// `l` as a max of guarded terms (`GTerm`): its value under every
    /// assignment is the largest term's (0 for none). p is the term p;
    /// succ l is 1 and every term of l one higher; max joins; imax c d is d's
    /// terms and c's with the clause dec(d) added (c counts only when d is
    /// not zero, and then imax is max); with dec(d) empty imax c d is 0.
    /// `None` on a tick's stop.
    fn gterms(&self, l: u32, memo: &mut FxHashMap<u32, Vec<GTerm>>, dm: &mut FxHashMap<u32, Option<Vec<u32>>>, tick: &mut dyn FnMut() -> bool) -> Option<Vec<GTerm>> {
        if let Some(r) = memo.get(&l) {
            return Some(r.clone());
        }
        if !tick() {
            return None;
        }
        let (k, a, b) = self.get(l);
        let r = match k {
            K_ZERO => Vec::new(),
            K_PARAM => vec![GTerm { guard: Vec::new(), base: Some(a), k: 0 }],
            K_SUCC => {
                let mut r = vec![GTerm { guard: Vec::new(), base: None, k: 1 }];
                for mut t in self.gterms(a, memo, dm, tick)? {
                    t.k += 1;
                    r.push(t);
                }
                gterms_simplify(r)
            }
            K_MAX => {
                let mut r = self.gterms(a, memo, dm, tick)?;
                r.extend(self.gterms(b, memo, dm, tick)?);
                gterms_simplify(r)
            }
            _ => match self.dec_set(b, dm) {
                Some(d) if d.is_empty() => Vec::new(),
                d => {
                    let mut r = self.gterms(b, memo, dm, tick)?;
                    for mut t in self.gterms(a, memo, dm, tick)? {
                        if let Some(d) = &d {
                            t.guard.push(d.clone());
                        }
                        r.push(t);
                    }
                    gterms_simplify(r)
                }
            },
        };
        memo.insert(l, r.clone());
        Some(r)
    }

    /// `a >= b` for every assignment of the parameters (complete). Both
    /// sides as guarded terms (`gterms`); `a >= b` exactly when `a` is at
    /// least each term of `b`, and that is decided by cases only on the
    /// parameters of that term's guard and base (`covers`): the parameters
    /// that decide `imax`es elsewhere, in other terms of `b`, are never split
    /// on, so independent `imax`es cost a sum, not a product (conformance
    /// hunt 2026-11-26, F2). `tick` is called at every step; when it says
    /// stop, the answer is `None` (the caller declines), never a "no".
    /// Results are memoized per pair of normal forms.
    pub fn geq_cases(&mut self, a: u32, b: u32, tick: &mut dyn FnMut() -> bool) -> Option<bool> {
        if !tick() {
            return None;
        }
        let a = self.normalize(a);
        let b = self.normalize(b);
        if let Some(&r) = self.cases_memo.get(&(a, b)) {
            return Some(r);
        }
        let r = if self.geq_core(a, b) {
            true
        } else {
            let mut memo = FxHashMap::default();
            let mut dm = FxHashMap::default();
            let ta = self.gterms(a, &mut memo, &mut dm, tick)?;
            let tb = self.gterms(b, &mut memo, &mut dm, tick)?;
            let mut ok = true;
            for t in &tb {
                if !covers(&ta, t, &mut Vec::new(), &mut Vec::new(), tick)? {
                    ok = false;
                    break;
                }
            }
            ok
        };
        self.cases_memo.insert((a, b), r);
        Some(r)
    }

    /// Moves the worker-made levels and memos out (into the returned
    /// interner), leaving an empty one on the same global table, so that a
    /// caller can tick while `geq_cases` runs; `attach` puts them back.
    pub fn detach(&mut self) -> Levels<'e> {
        Levels {
            g: self.g,
            gmap: self.gmap,
            loc: std::mem::take(&mut self.loc),
            lmap: std::mem::take(&mut self.lmap),
            norm_memo: std::mem::take(&mut self.norm_memo),
            cases_memo: std::mem::take(&mut self.cases_memo),
        }
    }
    pub fn attach(&mut self, other: Levels<'e>) {
        *self = other;
    }

    fn geq_core(&mut self, l1: u32, l2: u32) -> bool {
        if l1 == l2 || self.is_zero(l2) {
            return true;
        }
        let (k2, a2, b2) = self.get(l2);
        if k2 == K_MAX {
            return self.geq_fast(l1, a2) && self.geq_fast(l1, b2);
        }
        let (k1, a1, b1) = self.get(l1);
        if k1 == K_MAX && (self.geq_fast(a1, l2) || self.geq_fast(b1, l2)) {
            return true;
        }
        if k2 == K_IMAX {
            return self.geq_fast(l1, a2) && self.geq_fast(l1, b2);
        }
        if k1 == K_IMAX {
            return self.geq_fast(b1, l2);
        }
        let p1 = self.to_offset(l1);
        let p2 = self.to_offset(l2);
        // milestone 29: Lean's rule tests the base of `l2` (k >= n when `l2`
        // is the constant n); the base of `l1` was tested here, which
        // refused u+2 >= 1 and let n >= u+k through for n >= k
        if p1.0 == p2.0 || self.is_zero(p2.0) {
            return p1.1 >= p2.1;
        }
        if p1.1 == p2.1 && p1.1 > 0 {
            return self.geq_fast(p1.0, p2.0);
        }
        false
    }

    /// Milestone 23: `subst` without the memo while the level has at most
    /// `budget` nodes (levels are small trees); None past it (the caller
    /// then runs `subst`, whose memo bounds a shared DAG).
    pub fn subst_small(&mut self, l: u32, f: &dyn Fn(u32) -> Option<u32>, budget: &mut u32) -> Option<u32> {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let (k, a, b) = self.get(l);
        Some(match k {
            K_ZERO => l,
            K_PARAM => f(a).unwrap_or(l),
            K_SUCC => {
                let x = self.subst_small(a, f, budget)?;
                if x == a { l } else { self.succ(x) }
            }
            _ => {
                let x = self.subst_small(a, f, budget)?;
                let y = self.subst_small(b, f, budget)?;
                if x == a && y == b {
                    l
                } else if k == K_MAX {
                    self.max(x, y)
                } else {
                    self.imax(x, y)
                }
            }
        })
    }
    /// Substitutes parameters: `f(canon_name)` gives the replacement.
    pub fn subst(&mut self, l: u32, f: &dyn Fn(u32) -> Option<u32>, memo: &mut FxHashMap<u32, u32>) -> u32 {
        if let Some(&r) = memo.get(&l) {
            return r;
        }
        let (k, a, b) = self.get(l);
        let r = match k {
            K_ZERO => l,
            K_PARAM => f(a).unwrap_or(l),
            K_SUCC => {
                let x = self.subst(a, f, memo);
                if x == a { l } else { self.succ(x) }
            }
            _ => {
                let x = self.subst(a, f, memo);
                let y = self.subst(b, f, memo);
                if x == a && y == b {
                    l
                } else if k == K_MAX {
                    self.max(x, y)
                } else {
                    self.imax(x, y)
                }
            }
        };
        memo.insert(l, r);
        r
    }

    /// Calls `f` on every parameter name in `l` while it holds; true when
    /// it held for all. A level is a DAG (interned: a shared part has one
    /// id), so each max or imax node is walked once: as a tree, a closed
    /// level `l(i+1) = max (imax l(i) 1) (succ l(i))` of depth 36 has 2^36
    /// leaves (conformance hunt 2026-11-26, F1).
    pub fn params_in(&self, l: u32, f: &mut dyn FnMut(u32) -> bool) -> bool {
        let mut seen: FxHashSet<u32> = FxHashSet::default();
        self.params_in_go(l, f, &mut seen)
    }
    fn params_in_go(&self, l: u32, f: &mut dyn FnMut(u32) -> bool, seen: &mut FxHashSet<u32>) -> bool {
        let (k, a, b) = self.get(l);
        match k {
            K_ZERO => true,
            K_PARAM => f(a),
            K_SUCC => self.params_in_go(a, f, seen),
            // a node seen before held already (a failure ends the walk)
            _ => !seen.insert(l) || (self.params_in_go(a, f, seen) && self.params_in_go(b, f, seen)),
        }
    }
}

/// A guarded term of a level: `base + k` (base a parameter, or 0 for
/// `None`) when every clause of `guard` holds, else 0. A clause holds when
/// one of its parameters is not zero.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct GTerm {
    guard: Vec<Vec<u32>>,
    base: Option<u32>,
    k: u32,
}

/// Clause `c` follows from `guard` when it contains one of guard's clauses.
fn implied(guard: &[Vec<u32>], c: &[u32]) -> bool {
    guard.iter().any(|g| g.iter().all(|x| c.contains(x)))
}

/// Terms with sorted guards without clauses implied by others, no zero
/// terms, and none at most another one everywhere: `s` is at least `t`
/// when `t`'s guard implies `s`'s and `s` is as high on the same base (or
/// `t` is a constant).
fn gterms_simplify(mut ts: Vec<GTerm>) -> Vec<GTerm> {
    for t in ts.iter_mut() {
        let mut g = std::mem::take(&mut t.guard);
        for c in g.iter_mut() {
            c.sort_unstable();
            c.dedup();
        }
        g.sort_unstable_by(|x, y| x.len().cmp(&y.len()).then_with(|| x.cmp(y)));
        g.dedup();
        let mut kept: Vec<Vec<u32>> = Vec::new();
        for c in g {
            if !implied(&kept, &c) {
                kept.push(c);
            }
        }
        kept.sort_unstable();
        t.guard = kept;
    }
    ts.retain(|t| t.base.is_some() || t.k > 0);
    ts.sort_unstable();
    ts.dedup();
    let at_least = |s: &GTerm, t: &GTerm| {
        (s.base == t.base || t.base.is_none()) && s.k >= t.k && s.guard.iter().all(|c| implied(&t.guard, c))
    };
    let mut out: Vec<GTerm> = Vec::new();
    for (i, t) in ts.iter().enumerate() {
        // of two equal-strength terms the first is kept
        let beaten = ts.iter().enumerate().any(|(j, s)| j != i && at_least(s, t) && (!at_least(t, s) || j < i));
        if !beaten {
            out.push(t.clone());
        }
    }
    out
}

/// Whether the terms `a` are at least `t` for every assignment in which the
/// parameters `nz` are not zero and `z` are zero. Cases are taken only on a
/// parameter of `t`'s guard (an open clause) or base: `p = 0` or not. Once
/// `t`'s guard holds and its base is decided, `t` has one value (base + k,
/// the base unbounded when not zero) and `a`, which only grows with every
/// parameter (levels are monotone), is least with every other parameter 0
/// and the non-zero ones 1: `a` wins when a term alive there (every clause
/// meets `nz`) is on the same base at least as high, or, for a constant
/// `k`, is at least `k` there (its base, when in `nz`, counts as 1).
fn covers(a: &[GTerm], t: &GTerm, nz: &mut Vec<u32>, z: &mut Vec<u32>, tick: &mut dyn FnMut() -> bool) -> Option<bool> {
    if !tick() {
        return None;
    }
    let mut split = None;
    for c in &t.guard {
        if c.iter().any(|x| nz.contains(x)) {
            continue;
        }
        match c.iter().find(|x| !z.contains(x)) {
            // a clause with every parameter zero: `t` is 0 here
            None => return Some(true),
            Some(&x) => {
                if split.is_none() {
                    split = Some(x);
                }
            }
        }
    }
    if split.is_none()
        && let Some(p) = t.base
        && !nz.contains(&p)
        && !z.contains(&p)
    {
        split = Some(p);
    }
    if let Some(x) = split {
        nz.push(x);
        let r = covers(a, t, nz, z, tick);
        nz.pop();
        if !r? {
            return Some(false);
        }
        z.push(x);
        let r = covers(a, t, nz, z, tick);
        z.pop();
        return r;
    }
    let base = t.base.filter(|p| nz.contains(p));
    if base.is_none() && t.k == 0 {
        return Some(true);
    }
    Some(a.iter().any(|s| {
        s.guard.iter().all(|c| c.iter().any(|x| nz.contains(x)))
            && match base {
                Some(p) => s.base == Some(p) && s.k >= t.k,
                None => s.k >= t.k || (s.k + 1 >= t.k && s.base.is_some_and(|q| nz.contains(&q))),
            }
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Complete comparison, never stopped.
    fn geq(lv: &mut Levels, a: u32, b: u32) -> bool {
        match lv.geq3(a, b) {
            Some(r) => r,
            None => lv.geq_cases(a, b, &mut || true).unwrap(),
        }
    }
    fn equiv(lv: &mut Levels, a: u32, b: u32) -> bool {
        match lv.equiv3(a, b) {
            Some(r) => r,
            None => geq(lv, a, b) && geq(lv, b, a),
        }
    }

    /// Milestone 29: `geq` against Lean's is_geq_core (offsets compare when
    /// the bases are equal or the right side's base is zero).
    #[test]
    fn geq_offsets() {
        let g = vec![(K_ZERO, 0, 0)];
        let gmap: FxHashMap<(u8, u32, u32), u32> = [((K_ZERO, 0, 0), 0)].into_iter().collect();
        let mut lv = Levels::new(&g, &gmap);
        let z = 0;
        let one = lv.succ(z);
        let two = lv.succ(one);
        let three = lv.succ(two);
        let u = lv.param(1);
        let v = lv.param(2);
        let u1 = lv.succ(u);
        let u2 = lv.succ(u1);
        let v1 = lv.succ(v);
        let muv = lv.max(u, v);
        let muv1 = lv.succ(muv);
        let iuv1 = lv.imax(u, v1);
        let cases = [
            (u2, one, true), // FLT's DoubleComplex.Bounded: Sort (u+2) holds Nat
            (u2, two, true),
            (u1, two, false),
            (two, u2, false), // a constant does not bound a parameter
            (three, u1, false),
            (one, u, false),
            (u1, u, true),
            (u, u1, false),
            (three, one, true),
            (one, three, false),
            (u, z, true),
            (muv1, u1, true),
            (u1, muv, false),
            (iuv1, v1, true),
            (v1, iuv1, false),
        ];
        for (a, b, want) in cases {
            assert_eq!(geq(&mut lv, a, b), want, "geq({a}, {b})");
        }
    }

    /// Complete level comparison (the renovation's tests 100-116 of
    /// lean-kernel-arena-beta): the good equations hold for every assignment,
    /// the bad ones fail for some.
    #[test]
    fn equiv_complete() {
        let g = vec![(K_ZERO, 0, 0)];
        let gmap: FxHashMap<(u8, u32, u32), u32> = [((K_ZERO, 0, 0), 0)].into_iter().collect();
        let mut lv = Levels::new(&g, &gmap);
        let one = lv.succ(ZERO);
        let u = lv.param(1);
        let v = lv.param(2);
        let w = lv.param(3);
        let mx = |lv: &mut Levels, a, b| lv.mk(K_MAX, a, b);
        let im = |lv: &mut Levels, a, b| lv.mk(K_IMAX, a, b);
        let v1 = lv.succ(v);
        let w1 = lv.succ(w);
        let iuv = im(&mut lv, u, v);
        let muv = mx(&mut lv, u, v);
        let mvw = mx(&mut lv, v, w);
        let mvw1 = mx(&mut lv, v, w1);
        let iuw = im(&mut lv, u, w);
        let ivw = im(&mut lv, v, w);
        let ivu = im(&mut lv, v, u);
        let good = [
            (mx(&mut lv, u, one), im(&mut lv, u, one)),
            (mx(&mut lv, u, v1), im(&mut lv, u, v1)),
            (mx(&mut lv, u, mvw1), im(&mut lv, u, mvw1)),
            (iuv, im(&mut lv, iuv, v)),
            (iuv, im(&mut lv, v, iuv)),
            (im(&mut lv, iuw, w), iuw),
            (im(&mut lv, u, iuv), iuv),
            (im(&mut lv, muv, w), { let a = im(&mut lv, u, w); let b = im(&mut lv, v, w); mx(&mut lv, a, b) }),
            (im(&mut lv, u, mvw), { let a = im(&mut lv, u, v); let b = im(&mut lv, u, w); mx(&mut lv, a, b) }),
            (im(&mut lv, u, ivw), im(&mut lv, muv, w)),
        ];
        for (a, b) in good {
            assert!(equiv(&mut lv, a, b), "equiv({a}, {b})");
        }
        assert!(geq(&mut lv, muv, iuv), "imax u v <= max u v");
        let bad = [
            (iuv, muv),
            (iuv, ivu),
            (im(&mut lv, u, ivw), { let a = im(&mut lv, u, v); im(&mut lv, a, w) }),
            (mx(&mut lv, iuv, v), muv),
            (iuv, v),
        ];
        for (a, b) in bad {
            assert!(!equiv(&mut lv, a, b), "not equiv({a}, {b})");
        }
        assert!(!geq(&mut lv, iuv, u), "u <= imax u v is false");
    }

    /// Nine and more deciding parameters: no cap on the splits; a tick
    /// that says stop ends the comparison with no answer, never a "no".
    #[test]
    fn equiv_many_deciding_params() {
        let g = vec![(K_ZERO, 0, 0)];
        let gmap: FxHashMap<(u8, u32, u32), u32> = [((K_ZERO, 0, 0), 0)].into_iter().collect();
        let mut lv = Levels::new(&g, &gmap);
        let u = lv.param(100);
        let ps: Vec<u32> = (1..=10).map(|i| lv.param(i)).collect();
        // imax u (max p1 .. p10) = max (imax u p1) .. (imax u p10)
        let mut m = ps[0];
        for &p in &ps[1..] {
            m = lv.mk(K_MAX, m, p);
        }
        let left = lv.mk(K_IMAX, u, m);
        let mut right = lv.mk(K_IMAX, u, ps[0]);
        for &p in &ps[1..] {
            let ip = lv.mk(K_IMAX, u, p);
            right = lv.mk(K_MAX, right, ip);
        }
        assert!(equiv(&mut lv, left, right), "imax distributes over a max of ten");
        // imax u (max p1 .. p10) = max u p1 .. p10 is false (all p = 0, u = 1)
        let wrong = lv.mk(K_MAX, u, m);
        assert!(!equiv(&mut lv, left, wrong), "imax is not max");
        // nested: imax p1 (imax p2 (.. (imax p9 p10))) <= max p1 .. p10, and not >=
        let mut nest = ps[9];
        for &p in ps[..9].iter().rev() {
            nest = lv.mk(K_IMAX, p, nest);
        }
        assert!(geq(&mut lv, m, nest), "nested imax under the max");
        assert!(!geq(&mut lv, nest, m), "max not under the nested imax");
        // a stop is no answer
        let mut lv2 = Levels::new(&g, &gmap);
        let u = lv2.param(100);
        let ps: Vec<u32> = (1..=10).map(|i| lv2.param(i)).collect();
        let mut m = ps[0];
        for &p in &ps[1..] {
            m = lv2.mk(K_MAX, m, p);
        }
        let left = lv2.mk(K_IMAX, u, m);
        let mut right = lv2.mk(K_IMAX, u, ps[0]);
        for &p in &ps[1..] {
            let ip = lv2.mk(K_IMAX, u, p);
            right = lv2.mk(K_MAX, right, ip);
        }
        let mut n = 0;
        assert_eq!(lv2.geq_cases(left, right, &mut || { n += 1; n < 3 }), None);
    }

    fn value(lv: &Levels, l: u32, asg: &[u32]) -> u32 {
        let (k, a, b) = lv.get(l);
        match k {
            K_ZERO => 0,
            K_PARAM => asg[a as usize],
            K_SUCC => value(lv, a, asg) + 1,
            K_MAX => value(lv, a, asg).max(value(lv, b, asg)),
            _ => {
                let y = value(lv, b, asg);
                if y == 0 { 0 } else { value(lv, a, asg).max(y) }
            }
        }
    }

    fn random_level(lv: &mut Levels, np: u32, seed: &mut u64, depth: u32) -> u32 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let r = (*seed >> 33) % if depth == 0 { 3 } else { 6 };
        match r {
            0 => ZERO,
            1 | 2 => lv.param((((*seed >> 40) % np as u64) + 1) as u32),
            3 => {
                let a = random_level(lv, np, seed, depth - 1);
                lv.succ(a)
            }
            4 => {
                let a = random_level(lv, np, seed, depth - 1);
                let b = random_level(lv, np, seed, depth - 1);
                lv.mk(K_MAX, a, b)
            }
            _ => {
                let a = random_level(lv, np, seed, depth - 1);
                let b = random_level(lv, np, seed, depth - 1);
                lv.mk(K_IMAX, a, b)
            }
        }
    }

    /// The complete comparison against evaluation on every assignment of
    /// 0..=6 to three parameters (enough: offsets stay below 5 at depth 4).
    #[test]
    fn geq_against_evaluation() {
        let g = vec![(K_ZERO, 0, 0)];
        let gmap: FxHashMap<(u8, u32, u32), u32> = [((K_ZERO, 0, 0), 0)].into_iter().collect();
        let mut lv = Levels::new(&g, &gmap);
        let mut seed = 11u64;
        let (mut yes, mut no) = (0, 0);
        for _ in 0..30000 {
            let a = random_level(&mut lv, 3, &mut seed, 4);
            let b = random_level(&mut lv, 3, &mut seed, 4);
            let mut want = true;
            'all: for x in 0..=6u32 {
                for y in 0..=6u32 {
                    for z in 0..=6u32 {
                        let asg = [0, x, y, z];
                        if value(&lv, a, &asg) < value(&lv, b, &asg) {
                            want = false;
                            break 'all;
                        }
                    }
                }
            }
            assert_eq!(geq(&mut lv, a, b), want, "geq({a}, {b})");
            if want { yes += 1 } else { no += 1 }
        }
        assert!(yes > 3000 && no > 3000, "{yes} {no}");
    }

    /// Conformance hunt 2026-11-26, F2: n independent triples
    /// imax u (imax v w) = imax (max u v) w under one max; the cases on
    /// one triple's parameters never multiply with another's.
    #[test]
    fn independent_imaxes_add_up() {
        let g = vec![(K_ZERO, 0, 0)];
        let gmap: FxHashMap<(u8, u32, u32), u32> = [((K_ZERO, 0, 0), 0)].into_iter().collect();
        let mut lv = Levels::new(&g, &gmap);
        let n = 40;
        let (mut l, mut r, mut bad) = (ZERO, ZERO, ZERO);
        for i in 0..n {
            let u = lv.param(3 * i + 1);
            let v = lv.param(3 * i + 2);
            let w = lv.param(3 * i + 3);
            let ivw = lv.mk(K_IMAX, v, w);
            let a = lv.mk(K_IMAX, u, ivw);
            let muv = lv.mk(K_MAX, u, v);
            let b = lv.mk(K_IMAX, muv, w);
            let iuv = lv.mk(K_IMAX, u, v);
            let c = lv.mk(K_IMAX, iuv, w);
            l = if i == 0 { a } else { lv.mk(K_MAX, l, a) };
            r = if i == 0 { b } else { lv.mk(K_MAX, r, b) };
            // the last triple is imax (imax u v) w: not equal (v = 0)
            bad = if i == 0 { a } else if i + 1 == n { lv.mk(K_MAX, bad, c) } else { lv.mk(K_MAX, bad, a) };
        }
        let mut steps = 0;
        assert_eq!(lv.geq_cases(l, r, &mut || { steps += 1; true }), Some(true));
        assert_eq!(lv.geq_cases(r, l, &mut || { steps += 1; true }), Some(true));
        assert!(!equiv(&mut lv, l, bad));
        assert!(steps < 100_000, "{steps} steps");
    }
}
