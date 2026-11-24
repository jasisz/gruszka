//! Milestone 59 (feature `cnt` only): counters for Nat operations and for
//! closed whnfs across declarations. No effect on verdicts; release builds
//! do not compile this file.
use crate::nat::BigUint;
#[allow(unused_imports)]
use crate::nat::NatExt;
use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::sync::Mutex;

pub const NB: usize = 8;
pub const NOPS: usize = 14;
const NAMES: [&str; NOPS] =
    ["add", "sub", "mul", "div", "mod", "gcd", "beq", "ble", "land", "lor", "xor", "shiftLeft", "shiftRight", "pow"];

#[cfg(target_os = "macos")]
pub fn counts() -> (u64, u64) {
    unsafe extern "C" {
        fn thread_selfcounts(kind: i32, buf: *mut u64, n: usize) -> i32;
    }
    let mut b = [0u64; 2];
    unsafe {
        thread_selfcounts(1, b.as_mut_ptr(), 16);
    }
    (b[0], b[1])
}
#[cfg(not(target_os = "macos"))]
pub fn counts() -> (u64, u64) {
    (0, 0)
}

fn bucket(limbs: usize) -> usize {
    match limbs {
        0 | 1 => 0,
        2 => 1,
        3..=4 => 2,
        5..=16 => 3,
        17..=64 => 4,
        65..=256 => 5,
        257..=1024 => 6,
        _ => 7,
    }
}
const BNAMES: [&str; NB] = ["1", "2", "3-4", "5-16", "17-64", "65-256", "257-1K", ">1K"];

#[derive(Default, Clone, Copy)]
pub struct Cell {
    pub n: u64,
    pub ins: u64,
    pub cyc: u64,
    /// the same (op, a, b) by content earlier in this declaration
    pub rep_n: u64,
    pub rep_ins: u64,
    /// ... earlier in this worker, an earlier declaration (not this one)
    pub xrep_n: u64,
    pub xrep_ins: u64,
    /// the result equals an operand
    pub same_n: u64,
    pub same_ins: u64,
}
impl Cell {
    fn add(&mut self, o: &Cell) {
        self.n += o.n;
        self.ins += o.ins;
        self.cyc += o.cyc;
        self.rep_n += o.rep_n;
        self.rep_ins += o.rep_ins;
        self.xrep_n += o.xrep_n;
        self.xrep_ins += o.xrep_ins;
        self.same_n += o.same_n;
        self.same_ins += o.same_ins;
    }
}

pub struct T {
    pub cells: Vec<Cell>,
    seen: HashMap<(u8, u64, u64), u32>,
    decl: u32,
    over: (u64, u64),
    /// mk_nat after an operation of reduce_nat: small hit, big hit, new small, new big
    pub mk: [u64; 4],
    pub mk_ins: u64,
    /// whnf events (closed, >= GHOST_TICKS)
    pub wev: Vec<String>,
    pub wseq: u64,
    pub name_samples: Vec<(u64, u64, u64, u8)>, // ns, ins, nodes, closed
    pub wi: usize,
    pub from_reduce: bool,
    pub ticks_total: u64,
    pub last_ticks: u32,
    /// land over shiftRight (mask 2^w-1: ok), mod over shiftRight (2^w: ok)
    pub pat: [u64; 4],
    /// instructions of the shiftRight operand's whnf where ok
    pub pat_ins: u64,
}
impl Default for T {
    fn default() -> Self {
        // the counter call's own cost, subtracted from each measurement
        let mut best = (u64::MAX, u64::MAX);
        for _ in 0..64 {
            let a = counts();
            let b = counts();
            best = (best.0.min(b.0 - a.0), best.1.min(b.1.wrapping_sub(a.1)));
        }
        T {
            cells: vec![Cell::default(); NOPS * NB * NB],
            seen: HashMap::new(),
            decl: u32::MAX,
            over: best,
            mk: [0; 4],
            mk_ins: 0,
            wev: Vec::new(),
            wseq: 0,
            name_samples: Vec::new(),
            wi: 0,
            from_reduce: false,
            ticks_total: 0,
            last_ticks: 0,
            pat: [0; 4],
            pat_ins: 0,
        }
    }
}
thread_local! {
    pub static TL: RefCell<T> = RefCell::new(T::default());
}

pub fn on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SK_NATCNT").is_some())
}
pub fn won() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SK_WCNT").is_some())
}

pub fn set_decl_t(d: u32, ticks: u32) {
    TL.with(|t| {
        let mut t = t.borrow_mut();
        t.decl = d;
        t.ticks_total += ticks.wrapping_sub(t.last_ticks) as u64;
        t.last_ticks = ticks;
    });
}
pub fn set_worker(wi: usize) {
    TL.with(|t| t.borrow_mut().wi = wi);
}

fn chash(n: &BigUint) -> u64 {
    let mut h = rustc_hash::FxHasher::default();
    for d in n.iter_u64_digits() {
        d.hash(&mut h);
    }
    n.bits().hash(&mut h);
    h.finish()
}

/// One Nat operation measured: `f` computes it.
pub fn fold<R>(op: usize, x: &BigUint, y: &BigUint, f: impl FnOnce() -> R, res: impl Fn(&R) -> Option<&BigUint>) -> R {
    let a = counts();
    let r = f();
    let b = counts();
    TL.with(|t| {
        let mut t = t.borrow_mut();
        let (ins, cyc) = ((b.0 - a.0).saturating_sub(t.over.0), (b.1.wrapping_sub(a.1)).saturating_sub(t.over.1));
        let la = x.iter_u64_digits().len();
        let lb = y.iter_u64_digits().len();
        let i = (op * NB + bucket(la)) * NB + bucket(lb);
        let key = (op as u8, chash(x), chash(y));
        let decl = t.decl;
        let prev = t.seen.insert(key, decl);
        let same = res(&r).is_some_and(|z| z == x || z == y);
        let c = &mut t.cells[i];
        c.n += 1;
        c.ins += ins;
        c.cyc += cyc;
        match prev {
            Some(d) if d == decl => {
                c.rep_n += 1;
                c.rep_ins += ins;
            }
            Some(_) => {
                c.xrep_n += 1;
                c.xrep_ins += ins;
            }
            None => {}
        }
        if same {
            c.same_n += 1;
            c.same_ins += ins;
        }
        if t.seen.len() > 1 << 24 {
            t.seen.clear();
        }
    });
    r
}

pub struct Agg {
    cells: Vec<Cell>,
    mk: [u64; 4],
    mk_ins: u64,
    pat: [u64; 4],
    pat_ins: u64,
}
pub static ALL: Mutex<Option<Agg>> = Mutex::new(None);

/// At a worker's end: its counters into the total, its whnf events to
/// SK_WCNT.w<i>.tsv.
pub fn flush() {
    TL.with(|t| {
        let t = t.borrow();
        let mut g = ALL.lock().unwrap();
        let a = g.get_or_insert_with(|| Agg { cells: vec![Cell::default(); NOPS * NB * NB], mk: [0; 4], mk_ins: 0, pat: [0; 4], pat_ins: 0 });
        for (x, y) in a.cells.iter_mut().zip(&t.cells) {
            x.add(y);
        }
        for k in 0..4 {
            a.mk[k] += t.mk[k];
        }
        a.mk_ins += t.mk_ins;
        for k in 0..4 {
            a.pat[k] += t.pat[k];
        }
        a.pat_ins += t.pat_ins;
        if won() {
            let p = std::env::var("SK_WCNT").unwrap();
            let mut f = std::io::BufWriter::new(std::fs::File::create(format!("{p}.w{}.tsv", t.wi)).unwrap());
            for l in &t.wev {
                writeln!(f, "{l}").unwrap();
            }
            writeln!(f, "T\t{}", t.ticks_total).unwrap();
            for &(ns, ins, nodes, cl) in &t.name_samples {
                writeln!(f, "N\t{ns}\t{ins}\t{nodes}\t{cl}").unwrap();
            }
        }
    });
}

pub fn report() {
    let g = ALL.lock().unwrap();
    let Some(a) = g.as_ref() else { return };
    eprintln!("NATCNT mk_nat after reduce_nat: small hit {} big hit {} small new {} big new {} ins {}", a.mk[0], a.mk[1], a.mk[2], a.mk[3], a.mk_ins);
    eprintln!("NATCNT land/shiftRight {} (mask {}) mod/shiftRight {} (2^w {}) shift whnf ins {}", a.pat[0] + a.pat[1], a.pat[1], a.pat[2] + a.pat[3], a.pat[3], a.pat_ins);
    eprintln!("NATCNT op\ta\tb\tn\tins\tcyc\trep_n\trep_ins\txrep_n\txrep_ins\tsame_n\tsame_ins");
    for op in 0..NOPS {
        for ba in 0..NB {
            for bb in 0..NB {
                let c = &a.cells[(op * NB + ba) * NB + bb];
                if c.n > 0 {
                    eprintln!(
                        "NATCNT {}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                        NAMES[op], BNAMES[ba], BNAMES[bb], c.n, c.ins, c.cyc, c.rep_n, c.rep_ins, c.xrep_n, c.xrep_ins, c.same_n, c.same_ins
                    );
                }
            }
        }
    }
}
