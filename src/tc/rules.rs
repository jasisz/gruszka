//! Milestone 53: derived rules for hot definitions (docs/architecture.md,
//! Derived rules; nano-lean's `derive.rs`, Pestka's DerivedRules and
//! RulesThatSave).
//!
//! Reduction commutes with substitution: if `f x1 .. xn` reduces to `r` with
//! the `xi` variables, `f a1 .. an` reduces to `r` with the `ai` put in. A
//! definition unfolded `HOT` times in whnf's loop within a session is
//! applied to fresh variables and brought to weak head normal form; where a
//! recursor in the result waits on one of the variables, the variable is
//! split into each constructor applied to fresh variables and the same done
//! again. The tree of splits is the definition's rule: a call whose
//! arguments, brought to weak head normal form where the tree asks, match a
//! path gets that leaf with the arguments and fields put in; any other call
//! unfolds as before.
//!
//! A leaf is kept as a *template*: the value's shape with every arena id
//! replaced by what makes it again (terms, level ids, constants, small Nat
//! literals, slots for the variables). A rule names no value of the arena,
//! so a region's rollback cannot cut it; it lives for the session (level
//! ids and block terms are session facts) and is never used in a scratch
//! declaration.
use super::*;
use smallvec::SmallVec;

/// Unfoldings in whnf's loop, per constant and level list in a session,
/// before a rule is derived (nano-lean's and Pestka's 32; SK_RULE_HOT).
pub(super) const RULE_HOT: u32 = 32;
/// Ticks one derivation may take (nano-lean's budget).
const BUDGET: u32 = 1 << 16;
/// A derivation's whole cost is bounded by the work it serves: all
/// derivations of the worker take at most 1/RULE_SHARE of its ticks (plus
/// one budget, so that the first one can run).
const RULE_SHARE: u64 = 8;
const MAX_ARITY: u32 = 16;
const MAX_SPLITS: u32 = 3;
const MAX_CTORS: usize = 8;
const MAX_NODES: usize = 64;
const TEMPLATE_NODES: usize = 256;
const BLOCKER_DEPTH: u32 = 8;
/// How far `rule_reaches` follows definitions to a recursor.
const REACH_DEPTH: u32 = 8;

const SH_RULE_KNOWN: u8 = 16;
const SH_RULE_SOME: u8 = 32;

#[derive(Clone, Copy)]
pub(super) enum Hot {
    Count(u32),
    Rule(u32),
    Never,
}

#[derive(Clone, Copy)]
enum Node {
    /// a reduct's template (None: too large; the call unfolds as before)
    Leaf(Option<u32>),
    /// the slot whose whnf picks the branch, the branches' range
    Split { slot: u16, start: u32, len: u16 },
}

#[derive(Clone, Copy)]
struct Branch {
    /// the constructor's canonical name and level list
    canon: u32,
    llr: u32,
    /// parameters and fields: they take the next slots
    nargs: u16,
    slot0: u16,
    node: u32,
}

#[derive(Clone, Copy)]
struct Rule {
    arity: u16,
    root: u32,
}

/// A template node.
#[derive(Clone, Copy)]
enum Tn {
    Slot(u16),
    Hole,
    Const(u32, u32),
    Sort(u32),
    Nat(u64),
    /// a literal of the file (MAIN's literal table)
    Lit(u32),
    /// a head (node) applied to the elims `tel[s..s + n]` (a projection as
    /// in a spine, else a node)
    Neu { head: u32, s: u32, n: u32 },
    /// `Val::Clo` (0), `Val::CloI` (1), a thunk (2) over the environment
    /// `tel[s..s + n]` (oldest entry first)
    Clo { kind: u8, term: u32, ls: u32, s: u32, n: u32 },
}

#[derive(Default)]
pub(super) struct Rules {
    state: FxHashMap<(u32, u32), Hot>,
    rules: Vec<Rule>,
    nodes: Vec<Node>,
    branches: Vec<Branch>,
    tn: Vec<Tn>,
    tel: Vec<u32>,
    /// a derivation is running (none starts inside one, nothing is counted)
    deriving: bool,
    /// a derivation unfolded a Nat operation the kernel computes on
    /// literals: no rule (with literals the operation is computed, not
    /// unfolded, so its reduct is not the reference's)
    nat_unfolded: bool,
    /// the worker's ticks seen and the ticks spent deriving (RULE_SHARE)
    work: u64,
    spent: u64,
    last_tick: u32,
    /// states of the whnf loops in progress that a rule fired on (each
    /// loop's from its call's base up), given the loop's result as their
    /// whnf when it ends (`fstates_settle`)
    pub(super) fstates: Vec<V>,
}

impl Rules {
    pub(super) fn clear(&mut self) {
        self.state.clear();
        self.rules.clear();
        self.nodes.clear();
        self.branches.clear();
        self.tn.clear();
        self.tel.clear();
        self.fstates.clear();
        // a panic inside a derivation leaves these set (after_panic starts
        // a new session)
        self.deriving = false;
        self.nat_unfolded = false;
    }
    pub(super) fn bytes(&self) -> usize {
        self.state.len() * 16 + self.rules.len() * 8 + self.nodes.len() * 12 + self.branches.len() * 20 + self.tn.len() * 24 + self.tel.len() * 4
    }
}

struct Slot {
    var: V,
    fv: u32,
    /// split into a constructor: (the constructor, the first of the slots
    /// its arguments take, how many)
    split: Option<(V, usize, usize)>,
}

impl Worker {
    #[inline(always)]
    pub(super) fn rl_nat_unfolded(&mut self) {
        if self.rl.deriving {
            self.rl.nat_unfolded = true;
        }
    }

    /// Milestone 53: the unfolding step of whnf's loop. A constant
    /// application whose unfolding is not memoized may go by its rule
    /// (several steps at once) or count towards one; anything else unfolds
    /// as before. Lazy delta's steps never take rules (it compares states
    /// with the same head by their arguments) and a fired result is not
    /// kept as the value's unfolding, which lazy delta reads.
    #[inline(always)]
    pub(super) fn unfold_w(&mut self, c: V) -> R<Option<V>> {
        if self.rules_on && !self.scratch && self.memo_at(c).unfold() == UF_NONE {
            if let Some((row, _, _)) = self.const_head(c) {
                if self.shape_flag(row) & SH_RULE_KNOWN == 0 || self.shape_flag(row) & SH_RULE_SOME != 0 {
                    if let Some(r) = self.rule_step(c)? {
                        return Ok(Some(r));
                    }
                }
            }
        }
        self.unfold(c)
    }

    #[inline(never)]
    fn rule_step(&mut self, c: V) -> R<Option<V>> {
        let Some((row, llr, spine)) = self.const_head(c) else { return Ok(None) };
        if !self.rule_cand(row) {
            return Ok(None);
        }
        let Some(args) = self.app_args(spine) else { return Ok(None) };
        if !self.visible(row) || self.ll_get(llr).len() != self.consts[row as usize].lparams.len() {
            return Ok(None);
        }
        let key = (row, llr);
        let h = match self.rl.state.get_mut(&key) {
            Some(Hot::Count(n)) => {
                if self.rl.deriving {
                    return Ok(None);
                }
                *n += 1;
                if *n < self.rule_hot {
                    return Ok(None);
                }
                self.rule_derive(row, llr)?
            }
            Some(h) => *h,
            None => {
                if !self.rl.deriving {
                    self.rl.state.insert(key, Hot::Count(1));
                }
                return Ok(None);
            }
        };
        let Hot::Rule(i) = h else { return Ok(None) };
        // a state a rule fired on before: its loop's result
        let m = self.memo_at(c).whnf;
        if m != NONE {
            return Ok(Some(m));
        }
        let r = self.rule_fire(i, args)?;
        if let Some(x) = r {
            if !self.rl.deriving {
                self.rl.fstates.push(c);
            }
            if KNOBS && self.rule_check && !self.attempting() {
                // SK_RULE_CHECK=1 (knobs, gates): every fired result is
                // compared with the state's plain unfolding (outside
                // attempts: there `false` may only mean "not within the
                // budget")
                let u = self.unfold(c)?.expect("a fired state unfolds");
                if !self.defeq(x, u)? {
                    let (wx, wu) = (self.whnf(x)?, self.whnf(u)?);
                    eprintln!("RULECHECK state {}\n  fired {}\n  unfold {}\n  whnf fired {}\n  whnf unfold {}", self.vshow(c, 6), self.vshow(x, 6), self.vshow(u, 6), self.vshow(wx, 6), self.vshow(wu, 6));
                    panic!("derived rule of {} disagrees with its unfolding", self.env.name_str(self.consts[row as usize].name));
                }
            }
        }
        Ok(r)
    }

    /// The loop whose fired states are noted past `fb` ended at `r`: each
    /// gets `r` as its whnf (all of them reduce to it by head steps). A
    /// fired result is not kept as the state's unfolding (lazy delta reads
    /// that one step at a time), so without this a later loop that comes to
    /// the same state fires again where an unfolding would have found its
    /// memo (magma-list-deep-n36: 3.37 M fires for 0.84 M distinct steps).
    /// Not for a big literal result (it would be held by every state).
    pub(super) fn fstates_settle(&mut self, fb: usize, r: V) {
        if self.rl.fstates.len() == fb {
            return;
        }
        if !(matches!(self.val(r), Val::Lit(_)) && !self.is_small_nat(r)) {
            for i in fb..self.rl.fstates.len() {
                let c = self.rl.fstates[i];
                if c != r && self.memo_at(c).whnf == NONE {
                    self.memo_w(c).whnf = r;
                }
            }
        }
        self.rl.fstates.truncate(fb);
    }

    /// Can definition `row` have a rule: a safe definition of MAIN with one
    /// to MAX_ARITY leading lambdas, not a casesOn (`cases_direct` takes
    /// those) nor a Nat operation the kernel computes, whose body under the
    /// lambdas is headed, past projections, by something that reaches a
    /// recursor applied to one of those lambdas' variables (Pestka's
    /// reachesRecursor). Read from the value once per row.
    fn rule_cand(&mut self, row: u32) -> bool {
        let f = self.shape_flag(row);
        if f & SH_RULE_KNOWN != 0 {
            return f & SH_RULE_SOME != 0;
        }
        let r = self.rule_cand_of(row, 0);
        self.shared.shape[row as usize].fetch_or(SH_RULE_KNOWN | if r { SH_RULE_SOME } else { 0 }, Ordering::Relaxed);
        r
    }
    fn rule_cand_of(&mut self, row: u32, depth: u32) -> bool {
        let CKind::Defn { value, safety: 0, .. } = self.consts[row as usize].kind else { return false };
        if value >= self.mlen || self.env.nat_op[row as usize] != 0 || self.cases_shape(row).is_some() {
            return false;
        }
        let (n, b) = self.lams(value);
        if n == 0 || n > MAX_ARITY {
            return false;
        }
        self.rule_reaches(b, n, depth)
    }
    /// `t` (under `n` lambdas) is headed, past projections, by a recursor,
    /// a casesOn or a candidate definition, with one of the lambdas'
    /// variables among the arguments.
    fn rule_reaches(&mut self, t: u32, n: u32, depth: u32) -> bool {
        let mut f = t;
        let mut var = false;
        loop {
            match self.tk(f) {
                APP => {
                    let a = self.tb(f);
                    if self.tk(a) == BVAR && self.ta(a) < n {
                        var = true;
                    }
                    f = self.ta(f);
                }
                PROJ => {
                    f = self.ta(f);
                }
                _ => break,
            }
        }
        if !var || self.tk(f) != CONST || depth >= REACH_DEPTH {
            return false;
        }
        let c = self.row_of(self.ta(f));
        if c == NONE {
            return false;
        }
        match self.consts[c as usize].kind {
            CKind::Rec { .. } => true,
            CKind::Defn { .. } => {
                if self.cases_shape(c).is_some() {
                    return true;
                }
                let fl = self.shape_flag(c);
                if fl & SH_RULE_KNOWN != 0 {
                    return fl & SH_RULE_SOME != 0;
                }
                self.rule_cand_of(c, depth + 1)
            }
            _ => false,
        }
    }
    fn lams(&self, value: u32) -> (u32, u32) {
        let mut b = value;
        let mut n = 0u32;
        while is_lam(self.tk(b)) {
            b = self.tb(b);
            n += 1;
        }
        (n, b)
    }

    /// Derives the rule of `row` at `llr` (or finds it has none).
    #[cold]
    #[inline(never)]
    fn rule_derive(&mut self, row: u32, llr: u32) -> R<Hot> {
        let key = (row, llr);
        let t = self.ticks;
        self.rl.work += t.wrapping_sub(self.rl.last_tick) as u64;
        self.rl.last_tick = t;
        // past half of where work is handed up from (`deep_at`) a
        // derivation does not start: it would only end at Stop::Deep
        let deep = self.deep_at != 0 && {
            let x = 0u8;
            let sp = std::hint::black_box(&x) as *const u8 as usize;
            self.stack_base.saturating_sub(sp) > self.deep_at / 2 || self.wdepth >= self.deep_cur / 2
        };
        if deep || self.ground_busy || self.rl.spent > self.rl.work / RULE_SHARE + BUDGET as u64 {
            // not now: counted again from zero
            self.rl.state.insert(key, Hot::Count(0));
            return Ok(Hot::Count(0));
        }
        let CKind::Defn { value, .. } = self.consts[row as usize].kind else { return Ok(Hot::Never) };
        let (arity, _) = self.lams(value);
        self.rl.state.insert(key, Hot::Never);
        let (n0, b0, t0, l0) = (self.rl.nodes.len(), self.rl.branches.len(), self.rl.tn.len(), self.rl.tel.len());
        let (a0, d0) = (self.argstack.len(), self.vdepth);
        let u0 = self.stats.unfolds;
        self.rl.deriving = true;
        self.rl.nat_unfolded = false;
        let mut forms = 0usize;
        let r = self.attempt(Att::Derive, BUDGET, |s| s.rule_explore_root(row, llr, arity, &mut forms));
        self.rl.deriving = false;
        let spent = self.ticks.wrapping_sub(t) as u64;
        self.rl.spent += spent;
        self.rl.work += spent;
        self.rl.last_tick = self.ticks;
        let unfolds = self.stats.unfolds - u0;
        let root = match r {
            Ok(Some(Some(root))) => Some(root),
            Ok(_) => None,
            Err(Stop::Reject) | Err(Stop::Decline) | Err(Stop::Deep) if !self.arena_full => {
                // a step that fails on variables: no rule (the call does
                // the reference's steps and fails there if it must); work
                // handed up from too deep is not handed past the
                // derivation either (it would run outside its budget and
                // RULE_SHARE): no rule
                self.argstack.truncate(a0);
                self.vdepth_to(d0);
                None
            }
            Err(e) => {
                // an enclosing stop or work handed up: counted again later
                self.rl.nodes.truncate(n0);
                self.rl.branches.truncate(b0);
                self.rl.tn.truncate(t0);
                self.rl.tel.truncate(l0);
                self.rl.state.insert(key, Hot::Count(0));
                return Err(e);
            }
        };
        // RulesThatSave: a rule replaces the steps of its derivation; one
        // that unfolds once per form it met saves nothing and costs its guards
        // and one whose form waits on none of its variables (a single leaf)
        // only jumps steps ahead: its leaf's closures are made at every
        // fire, where the unfolding's beta walks lambdas without making
        // them (Pestka's DerivedRules: such leaves saved nothing on Init;
        // CFSG's m6c: +13% instructions)
        let keep = root.is_some_and(|r| matches!(self.rl.nodes[r as usize], Node::Split { .. })) && !self.rl.nat_unfolded && unfolds as usize > forms;
        if !keep {
            self.rl.nodes.truncate(n0);
            self.rl.branches.truncate(b0);
            self.rl.tn.truncate(t0);
            self.rl.tel.truncate(l0);
            if STATS { self.stats.rules[1] += 1; }
            return Ok(Hot::Never);
        }
        if STATS { self.stats.rules[0] += 1; }
        if KNOBS && std::env::var_os("SK_RULE_TRACE").is_some() {
            let leaves: Vec<String> = self.rl.nodes[n0..].iter().map(|n| match n {
                Node::Leaf(Some(t)) => format!("{}", self.rule_show(*t, 3)),
                Node::Leaf(None) => "-".into(),
                Node::Split { slot, len, .. } => format!("split#{slot}/{len}"),
            }).collect();
            eprintln!("RULE {} arity {arity} unfolds {unfolds} forms {forms} ticks {spent}: {}", self.env.name_str(self.consts[row as usize].name), leaves.join(" | "));
        }
        self.rl.rules.push(Rule { arity: arity as u16, root: root.unwrap() });
        let h = Hot::Rule(self.rl.rules.len() as u32 - 1);
        self.rl.state.insert(key, h);
        Ok(h)
    }

    fn rule_explore_root(&mut self, row: u32, llr: u32, arity: u32, forms: &mut usize) -> R<Option<u32>> {
        // the variables' type: a variable of `Type`, from which nothing
        // can be read (no K, no structure eta, no literal). Not of `Prop`:
        // the variables would be proofs, and proof irrelevance would find
        // any two of them equal (a K-like step on `f x y : x = y` would
        // compare x with y and take the rule)
        let one = self.lv.succ(ZERO);
        let s0 = self.intern(Val::Sort(one))?;
        let ty = self.fresh(s0)?;
        let mut slots: Vec<Slot> = Vec::with_capacity(arity as usize);
        for _ in 0..arity {
            let x = self.fresh(ty)?;
            let Val::Neu { head: Head::FVar(i), .. } = self.val(x) else { unreachable!() };
            slots.push(Slot { var: x, fv: i, split: None });
        }
        let base = self.rl.nodes.len();
        let f = self.mk_const(row, llr)?;
        self.rule_explore(f, arity as usize, &mut slots, ty, 0, base, forms)
    }

    #[allow(clippy::too_many_arguments)]
    fn rule_explore(&mut self, f: V, arity: usize, slots: &mut Vec<Slot>, ty: V, depth: u32, base: usize, forms: &mut usize) -> R<Option<u32>> {
        if self.rl.nodes.len() - base >= MAX_NODES {
            return Ok(None);
        }
        *forms += 1;
        let mut args: SmallVec16 = SmallVec16::new();
        for i in 0..arity {
            args.push(self.rule_resolve(slots, i)?);
        }
        let app = self.apply_many(f, &args)?;
        let r = self.whnf(app)?;
        let split = if depth < MAX_SPLITS { self.rule_blocker(r, slots)? } else { None };
        // the form as a leaf: where no split is made
        macro_rules! leaf {
            () => {{
                let t = self.rule_tmpl_root(r, slots)?;
                return Ok(Some(self.rule_node(Node::Leaf(t))));
            }};
        }
        let Some((s, rrow, rllr)) = split else { leaf!() };
        let CKind::Rec { rules, .. } = &self.env.consts[rrow as usize].kind else { leaf!() };
        let rules: SmallVec<[u32; 8]> = rules.iter().map(|r| r.0).collect();
        // renovation: a flagged recursor without rules never reduces (no
        // large elimination, lean4#16595); a split would wait on nothing
        if rules.len() > MAX_CTORS || (rules.is_empty() && self.env.flagged) {
            leaf!();
        }
        // the constructors' level list: the recursor's, past the motive's
        // universe when it has one more
        let rl = self.ll_get(rllr).to_vec();
        let mut bs: SmallVec<[Branch; 8]> = SmallVec::new();
        for &cname in &rules {
            let crow = self.row_of(cname);
            if crow == NONE || !self.visible(crow) {
                leaf!();
            }
            let CKind::Ctor { nparams, nfields, .. } = self.consts[crow as usize].kind else { leaf!() };
            let nl = self.consts[crow as usize].lparams.len();
            let cl = match rl.len() {
                n if n == nl => self.ll_intern(&rl),
                n if n == nl + 1 => self.ll_intern(&rl[1..]),
                _ => leaf!(),
            };
            let n = (nparams + nfields) as usize;
            let k = slots.len();
            if k + n > u16::MAX as usize {
                leaf!();
            }
            for _ in 0..n {
                let x = self.fresh(ty)?;
                let Val::Neu { head: Head::FVar(i), .. } = self.val(x) else { unreachable!() };
                slots.push(Slot { var: x, fv: i, split: None });
            }
            let head = self.mk_const(crow, cl)?;
            slots[s].split = Some((head, k, n));
            let node = self.rule_explore(f, arity, slots, ty, depth + 1, base, forms);
            slots[s].split = None;
            slots.truncate(k);
            let Some(node) = node? else { return Ok(None) };
            bs.push(Branch { canon: self.canon_of_row(crow), llr: cl, nargs: n as u16, slot0: k as u16, node });
        }
        let start = self.rl.branches.len() as u32;
        let len = bs.len() as u16;
        self.rl.branches.extend(bs);
        Ok(Some(self.rule_node(Node::Split { slot: s as u16, start, len })))
    }

    fn rule_node(&mut self, n: Node) -> u32 {
        self.rl.nodes.push(n);
        self.rl.nodes.len() as u32 - 1
    }

    /// The value slot `i` stands for on the current path: its variable, or
    /// its constructor applied to the values of its arguments' slots.
    fn rule_resolve(&mut self, slots: &[Slot], i: usize) -> R<V> {
        match slots[i].split {
            None => Ok(slots[i].var),
            Some((head, k, n)) => {
                let mut vs: SmallVec16 = SmallVec16::new();
                for j in k..k + n {
                    vs.push(self.rule_resolve(slots, j)?);
                }
                self.apply_many(head, &vs)
            }
        }
    }

    /// The unsplit slot whose variable is the major premise a recursor in
    /// `r` waits on (through recursors waiting on recursors), with the
    /// recursor. Not K-like recursors and not structures: they reduce
    /// without bringing the major to a constructor (K, structure eta), and
    /// a guard would bring it there.
    fn rule_blocker(&mut self, r: V, slots: &[Slot]) -> R<Option<(usize, u32, u32)>> {
        let mut r = r;
        for _ in 0..BLOCKER_DEPTH {
            let Some((row, llr, spine)) = self.const_head(r) else { return Ok(None) };
            let CKind::Rec { nparams, nindices, nmotives, nminors, k, .. } = self.consts[row as usize].kind else { return Ok(None) };
            let mi = (nparams + nmotives + nminors + nindices) as usize;
            let elims = self.spine_in(spine);
            if elims.len() <= mi || elims[..=mi].iter().any(|&e| e & PROJ_BIT != 0) {
                return Ok(None);
            }
            if self.ll_get(llr).len() != self.consts[row as usize].lparams.len() {
                return Ok(None);
            }
            // every recursor of the chain, not only the innermost: an outer
            // K-like or structure recursor reduces without its major brought
            // to a constructor (`Eq.rec … (Bool.rec h₁ h₂ b)`: K never
            // forces `b`), and a guard on the inner one would force it
            if k {
                return Ok(None);
            }
            let Some(&ind) = self.env.rec_major.get(&row) else { return Ok(None) };
            let irow = self.env.known_row(ind);
            if irow == NONE || !self.visible(irow) || self.structure_like(irow) {
                return Ok(None);
            }
            let m = self.whnf(elims[mi])?;
            if let Val::Neu { head: Head::FVar(i), spine: EMPTY } = self.val(m) {
                let s = slots.iter().position(|s| s.fv == i && s.split.is_none());
                return Ok(s.map(|s| (s, row, llr)));
            }
            r = m;
        }
        Ok(None)
    }

    /// The template of `r`: every slot's variable, and every split slot's
    /// constructor application, is that slot (the call's argument itself
    /// where the reference would hold it), the rest made again from terms,
    /// levels and literals. None past TEMPLATE_NODES nodes or at anything
    /// that cannot be made again (a variable of no slot, a literal of the
    /// session).
    fn rule_tmpl_root(&mut self, r: V, slots: &[Slot]) -> R<Option<u32>> {
        let mut cx: FxHashMap<V, u32> = FxHashMap::default();
        for i in 0..slots.len() {
            cx.insert(slots[i].var, i as u32);
            if slots[i].split.is_some() {
                let v = self.rule_resolve(slots, i)?;
                cx.insert(v, i as u32);
            }
        }
        let fv: FxHashMap<u32, u32> = slots.iter().enumerate().map(|(i, s)| (s.fv, i as u32)).collect();
        let (t0, l0) = (self.rl.tn.len(), self.rl.tel.len());
        let mut memo: FxHashMap<V, u32> = FxHashMap::default();
        let mut count = 0usize;
        let t = self.rule_tmpl(r, &cx, &fv, &mut memo, &mut count);
        if t.is_none() {
            self.rl.tn.truncate(t0);
            self.rl.tel.truncate(l0);
        }
        Ok(t)
    }
    fn rule_tn(&mut self, n: Tn) -> u32 {
        self.rl.tn.push(n);
        self.rl.tn.len() as u32 - 1
    }
    fn rule_tmpl(&mut self, v: V, cx: &FxHashMap<V, u32>, fv: &FxHashMap<u32, u32>, memo: &mut FxHashMap<V, u32>, count: &mut usize) -> Option<u32> {
        if let Some(&s) = cx.get(&v) {
            return Some(self.rule_tn(Tn::Slot(s as u16)));
        }
        if let Some(&t) = memo.get(&v) {
            return Some(t);
        }
        *count += 1;
        if *count > TEMPLATE_NODES {
            return None;
        }
        let t = match self.val(v) {
            Val::Sort(l) => self.rule_tn(Tn::Sort(l)),
            Val::Lit(i) => {
                let small = match self.lit(i) {
                    LitVal::Nat(n) => n.to_u64(),
                    _ => None,
                };
                match small {
                    Some(k) => self.rule_tn(Tn::Nat(k)),
                    // MAIN's literals and the blocks' (they live with the session)
                    None if (i as usize) < self.env.lits.len() || i >= BLIT_BASE => self.rule_tn(Tn::Lit(i)),
                    None => return None,
                }
            }
            Val::Neu { head, spine } => {
                let h = match head {
                    Head::Const(r, l) => self.rule_tn(Tn::Const(r, l)),
                    Head::FVar(i) => {
                        let s = *fv.get(&i)?;
                        self.rule_tn(Tn::Slot(s as u16))
                    }
                    Head::Stuck(x) => self.rule_tmpl(x, cx, fv, memo, count)?,
                };
                if spine == EMPTY {
                    h
                } else {
                    let es = SpineVec::from_slice(self.sp.args(spine));
                    let mut out: SmallVec16 = SmallVec16::new();
                    for &e in es.iter() {
                        out.push(if e & PROJ_BIT != 0 { e } else { self.rule_tmpl(e, cx, fv, memo, count)? });
                    }
                    let s = self.rl.tel.len() as u32;
                    self.rl.tel.extend_from_slice(&out);
                    self.rule_tn(Tn::Neu { head: h, s, n: out.len() as u32 })
                }
            }
            Val::Clo { term, env, ls } | Val::CloI { term, env, ls } | Val::Thunk { term, env, ls } => {
                let kind = match self.val(v) {
                    Val::Clo { .. } => 0u8,
                    Val::CloI { .. } => 1,
                    _ => 2,
                };
                let mut out: SmallVec16 = SmallVec16::new();
                if let Some((s, l)) = self.env_run(env) {
                    for k in s..s + l {
                        let x = self.eslot(k);
                        out.push(if x == HOLE { self.rule_tn(Tn::Hole) } else { self.rule_tmpl(x, cx, fv, memo, count)? });
                    }
                }
                let s = self.rl.tel.len() as u32;
                self.rl.tel.extend_from_slice(&out);
                self.rule_tn(Tn::Clo { kind, term, ls, s, n: out.len() as u32 })
            }
        };
        memo.insert(v, t);
        Some(t)
    }

    /// Fires rule `i` on a call's arguments: the leaf its guards pick, made
    /// with the arguments and fields put in, applied to the arguments past
    /// the rule's; None when a guard finds no branch (the call unfolds).
    #[inline(never)]
    fn rule_fire(&mut self, i: u32, args: &[V]) -> R<Option<V>> {
        let Rule { arity, root } = self.rl.rules[i as usize];
        let arity = arity as usize;
        if args.len() < arity {
            return Ok(None);
        }
        let mut bind: SmallVec<[V; 32]> = SmallVec::from_slice(&args[..arity]);
        let mut node = root;
        loop {
            match self.rl.nodes[node as usize] {
                Node::Leaf(None) => break,
                Node::Leaf(Some(t)) => {
                    let v = self.rule_inst(t, &bind)?;
                    if STATS { self.stats.rules[2] += 1; }
                    if KNOBS && self.stats.rules[2] & 0x3ffff == 0 && std::env::var_os("SK_RULE_TRACE").is_some() {
                        eprintln!("FIRE rule {i} args {} arity {arity} leaf {}", args.len(), self.rule_show(t, 3));
                    }
                    return Ok(Some(self.apply_many(v, &args[arity..])?));
                }
                Node::Split { slot, start, len } => {
                    let n0 = bind.len();
                    let Some(b) = self.rule_guard(bind[slot as usize], start, len, &mut bind)? else { break };
                    let br = self.rl.branches[b as usize];
                    // the fields take the slots the derivation gave them
                    debug_assert_eq!(n0, br.slot0 as usize);
                    debug_assert_eq!(bind.len(), n0 + br.nargs as usize);
                    let _ = n0;
                    node = br.node;
                }
            }
        }
        if STATS { self.stats.rules[3] += 1; }
        Ok(None)
    }

    /// The branch the whnf of `v` takes among `start..start + len`, as the
    /// recursor's rule finds its constructor (a Nat literal as `Nat.zero` or
    /// `Nat.succ` of the literal before, as `nat_lit_ctor` makes it; a
    /// string literal expanded); the constructor's arguments are pushed on
    /// `bind`.
    fn rule_guard(&mut self, v: V, start: u32, len: u16, bind: &mut SmallVec<[V; 32]>) -> R<Option<u32>> {
        let mut w = self.whnf(v)?;
        if let Val::Lit(i) = self.val(w) {
            let k = self.env.known;
            let (canon, pred) = match self.lit(i) {
                LitVal::Nat(n) if n.is_zero() => (k.nat_zero, None),
                LitVal::Nat(n) => (k.nat_succ, Some(n - 1u32)),
                LitVal::Str(s) => {
                    let s = s.clone();
                    match self.str_lit_expand(&s)? {
                        Some(x) => {
                            w = self.whnf(x)?;
                            return self.rule_guard_ctor(w, start, len, bind);
                        }
                        None => return Ok(None),
                    }
                }
            };
            if self.known_visible(canon) == NONE {
                self.known_missing();
                return Ok(None);
            }
            for b in start..start + len as u32 {
                let br = self.rl.branches[b as usize];
                if br.canon == canon {
                    if br.nargs as usize != pred.is_some() as usize || !self.ll_get(br.llr).is_empty() {
                        return Ok(None);
                    }
                    if let Some(p) = pred {
                        let p = self.mk_nat(p)?;
                        bind.push(p);
                    }
                    return Ok(Some(b));
                }
            }
            return Ok(None);
        }
        self.rule_guard_ctor(w, start, len, bind)
    }
    fn rule_guard_ctor(&mut self, w: V, start: u32, len: u16, bind: &mut SmallVec<[V; 32]>) -> R<Option<u32>> {
        let Some((crow, cllr, spine)) = self.const_head(w) else { return Ok(None) };
        let Some(cargs) = self.app_args(spine) else { return Ok(None) };
        let canon = self.canon_of_row(crow);
        for b in start..start + len as u32 {
            let br = self.rl.branches[b as usize];
            if br.canon == canon {
                if cargs.len() != br.nargs as usize || (cllr != br.llr && self.ll_get(cllr) != self.ll_get(br.llr)) {
                    return Ok(None);
                }
                bind.extend_from_slice(cargs);
                return Ok(Some(b));
            }
        }
        Ok(None)
    }

    /// The environment of content `c` (oldest entry first, HOLE where the
    /// term reads nothing): one frame hash-consed by content, as
    /// `prune_build` makes them (one probe, not a push per entry); past 63
    /// entries (no exact mask) pushed one by one.
    fn rule_env(&mut self, c: &[u32]) -> u32 {
        if c.is_empty() {
            return EMPTY;
        }
        if c.len() > 63 {
            let mut env = EMPTY;
            for &x in c {
                env = self.push_env(x, env);
            }
            return env;
        }
        let mut u = 0u64;
        for (j, &x) in c.iter().rev().enumerate() {
            if x != HOLE {
                u |= 1u64 << j;
            }
        }
        let h = frames::fhash(c);
        let (eloc, eslots) = (&self.eloc, &self.eslots);
        let run = |e: u32| {
            let (s, l, _) = eloc[e as usize];
            &eslots[s as usize..(s + l) as usize]
        };
        match self.ftab.find(h, c, run) {
            Ok(e) => e,
            Err(slot) => {
                let e = self.eloc.len() as u32;
                self.eloc.push((self.eslots.len() as u32, c.len() as u32, u));
                self.eslots.extend_from_slice(c);
                self.ft_insert(h, slot, e);
                e
            }
        }
    }

    fn rule_show(&self, t: u32, d: u32) -> String {
        match self.rl.tn[t as usize] {
            Tn::Slot(s) => format!("${s}"),
            Tn::Hole => "_".into(),
            Tn::Const(r, _) => self.env.name_str(self.consts[r as usize].name).to_string(),
            Tn::Sort(_) => "Sort".into(),
            Tn::Nat(k) => format!("{k}"),
            Tn::Lit(i) => format!("lit{i}"),
            Tn::Neu { head, s, n } => {
                if d == 0 { return "..".into(); }
                let mut o = format!("({}", self.rule_show(head, d - 1));
                for j in s..s + n {
                    let e = self.rl.tel[j as usize];
                    if e & PROJ_BIT != 0 { o += &format!(" .{}", self.projs[(e & !PROJ_BIT) as usize].1); } else { o += " "; o += &self.rule_show(e, d - 1); }
                }
                o + ")"
            }
            Tn::Clo { kind, term, n, .. } => format!("{}[t{term} env{n}]", ["clo", "cloi", "th"][kind as usize]),
        }
    }

    /// Makes template node `t` with the slots bound to `bind`.
    fn rule_inst(&mut self, t: u32, bind: &[V]) -> R<V> {
        match self.rl.tn[t as usize] {
            Tn::Slot(s) => Ok(bind[s as usize]),
            Tn::Hole => Ok(HOLE),
            Tn::Const(r, l) => self.mk_const(r, l),
            Tn::Sort(l) => self.intern(Val::Sort(l)),
            Tn::Nat(k) => self.mk_nat(BigUint::from(k)),
            Tn::Lit(i) => self.lit_value(i),
            Tn::Neu { head, s, n } => {
                let h = self.rule_inst(head, bind)?;
                let mut es: SmallVec16 = SmallVec16::new();
                for j in s..s + n {
                    let e = self.rl.tel[j as usize];
                    es.push(if e & PROJ_BIT != 0 { e } else { self.rule_inst(e, bind)? });
                }
                self.apply_elims(h, &es)
            }
            Tn::Clo { kind, term, ls, s, n } => {
                let mut c: SmallVec16 = SmallVec16::new();
                for j in s..s + n {
                    let e = self.rl.tel[j as usize];
                    c.push(self.rule_inst(e, bind)?);
                }
                let env = self.rule_env(&c);
                match kind {
                    0 => {
                        let env = self.prune(term, env);
                        self.intern(Val::Clo { term, env, ls })
                    }
                    1 => {
                        let env = self.prune(term, env);
                        self.intern(Val::CloI { term, env, ls })
                    }
                    _ => self.thunk(term, env, ls),
                }
            }
        }
    }
}
