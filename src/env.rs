//! The shared, read-only environment: Susz ids as columns.
//!
//! - MAIN expressions: `kind u8, a u32, b u32, p u32` plus a saturating
//!   loose-bvar range byte (0 = closed). An expression's id is its Susz id.
//! - Names stay Susz name ids; `row_of_name` maps any name id (through the
//!   reader's canonical names, so names are equal by value) to a constant row.
//! - Levels are interned once into a global table with canonical parameter
//!   names; terms hold global level ids.
//! - Literals are copied out of the file into owned tables.
//! - Proof blocks stay lazy (`BlockRef`), decoded per worker.

use crate::nat::{BigUint, NatExt};
use rustc_hash::FxHashMap;
use susz::read::{BlockRef, Component, Decl, Expr, Hints, Level, Ref, State, Visit};
pub use susz::read::IndFlags;

pub const BVAR: u8 = 0;
pub const SORT: u8 = 1;
pub const CONST: u8 = 2;
pub const APP: u8 = 3;
pub const LAM: u8 = 4; // 4..=7: LAM + binder
pub const PI: u8 = 8; // 8..=11: PI + binder
pub const LET: u8 = 12;
pub const NAT: u8 = 13;
pub const STR: u8 = 14;
pub const PROJ: u8 = 15;

#[inline(always)]
pub fn is_lam(k: u8) -> bool {
    (LAM..LAM + 4).contains(&k)
}
#[inline(always)]
pub fn is_pi(k: u8) -> bool {
    (PI..PI + 4).contains(&k)
}

/// Expression columns.
///
/// | kind  | a          | b            | u                       |
/// |-------|------------|--------------|-------------------------|
/// | BVAR  | de Bruijn index | -       | used mask               |
/// | SORT  | global level id | -       | 0                       |
/// | CONST | name id    | level-list offset | 0                  |
/// | APP   | fn         | arg          | used mask               |
/// | LAM/PI| type       | body         | used mask               |
/// | LET   | type       | value        | U_SIDE + index into `lets` |
/// | NAT/STR| index into `Env::lits` | - | 0                    |
/// | PROJ  | struct expr| field index  | U_SIDE + index into `projs` |
///
/// Night 11-27: the used mask (see `Used`) lives in the node, not in a
/// column of its own (8 bytes per node: Mathlib's MAIN 289 MiB). `u` is
/// the mask when it has no bit past 30, and then reading it is one load,
/// whatever the kind. Else `u` has bit 31 (`U_SIDE`): an APP, LAM or PI
/// has the index of its whole mask in `Cols::wide`, a BVAR's mask is its
/// index's, a LET's is in `Side::let_used`, a PROJ's its struct's. The
/// third payload that kinds had (`p`) went into `a` or `b`, which they did
/// not use, or for LET and PROJ into the side. Binder names are not kept:
/// nothing read them.
/// One term node (16 bytes: what a walk reads at a node is in one cache
/// line; milestone 11, the columns were separate arrays before).
#[derive(Default, Clone, Copy)]
#[repr(C)]
pub struct Node {
    pub a: u32,
    pub b: u32,
    pub u: u32,
    /// Loose bvar range (1 + largest loose index), exact below 65535; a
    /// larger range sets `too_deep` and the file or block is declined.
    pub rng: u16,
    pub kind: u8,
    pub _pad: u8,
}

/// Milestone 18: every term node of the process in one address range.
///
/// Term ids are u32; node `t` lives at `nodes + 16 t` and its used mask
/// (loose bound variables: bit i for #i, i < 63; bit 63 for any index of 63
/// or more) at `used + 8 t`, for MAIN and every worker's block arenas
/// alike, so a term read is one load from one base (no MAIN-or-block test,
/// no bounds check). The range covers every u32 id (64 GiB + 32 GiB of
/// address space, reserved once, pages made on first write), so a read at
/// any id reads mapped memory. Layout: MAIN at ids [0, main_len); after it
/// (rounded up to 2^16) the two overflow arenas of `big` ids each
/// (milestone 35), then slabs of `slab` ids, two per worker (session and
/// scratch arena), all below 2^31 (term ids share u32s with LL_POOL refs).
/// A declaration whose blocks do not fit its worker's slab runs again in
/// the overflow arenas (one worker at a time); their size does not depend
/// on the number of workers, so neither does the verdict.
/// Soundness: a node is read only at an id of MAIN or of the current
/// arena's pushed nodes (`Worker::term_live`, asserted in release-da).
pub struct Region {
    nodes: *mut Node,
    first: std::sync::atomic::AtomicU32,
    slab: std::sync::atomic::AtomicU32,
    next: std::sync::atomic::AtomicU32,
    /// milestone 35: the overflow arenas (session, scratch), taken by one
    /// worker at a time; set by `layout`
    pub big: std::sync::Mutex<Option<(Cols, Cols)>>,
}
unsafe impl Sync for Region {}
unsafe impl Send for Region {}

/// Ids at or past this are not term ids (LL_POOL).
pub const ID_LIMIT: u64 = 1 << 31;
const ID_SPACE: usize = 1 << 32;

#[cfg(unix)]
mod vm {
    unsafe extern "C" {
        pub fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    }
    pub const PROT_RW: i32 = 1 | 2;
    pub const MAP_PRIVATE: i32 = 2;
    pub const MAP_FIXED: i32 = 0x10;
    #[cfg(target_os = "macos")]
    pub const MAP_ANON: i32 = 0x1000;
    #[cfg(not(target_os = "macos"))]
    pub const MAP_ANON: i32 = 0x20;
    #[cfg(target_os = "macos")]
    pub const MAP_NORESERVE: i32 = 0;
    #[cfg(not(target_os = "macos"))]
    pub const MAP_NORESERVE: i32 = 0x4000;
    pub fn reserve(bytes: usize) -> *mut u8 {
        let p = unsafe { mmap(std::ptr::null_mut(), bytes, PROT_RW, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0) };
        if p as isize == -1 {
            return std::ptr::null_mut();
        }
        huge(p, bytes);
        p
    }
    #[cfg(target_os = "linux")]
    unsafe extern "C" {
        fn madvise(addr: *mut u8, len: usize, advice: i32) -> i32;
    }
    /// Milestone 58 (Linux): the reserved ranges (term columns, slabs, big
    /// tables) ask for transparent huge pages. Their reads hop across
    /// gigabytes, so 4 KiB pages missed the TLB on most hops: on AWS x86
    /// kE4Parse's page walks went from 9.9M to 0.21M, cycles -4...-36% on
    /// the five run349 certificates at RSS +0...7%. Advice only: a refusal
    /// (THP off, `never`) changes nothing. Elsewhere: no-op.
    #[inline]
    fn huge(_p: *mut u8, _bytes: usize) {
        #[cfg(target_os = "linux")]
        unsafe {
            const MADV_HUGEPAGE: i32 = 14;
            madvise(_p, _bytes, MADV_HUGEPAGE);
        }
    }
    /// Gives the pages of [p, p + bytes) back (fresh zero pages on next use).
    pub fn release(p: *mut u8, bytes: usize) {
        if bytes == 0 {
            return;
        }
        let r = unsafe { mmap(p, bytes, PROT_RW, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE | MAP_FIXED, -1, 0) };
        assert!(r == p, "could not release arena pages");
        // the fresh mapping lost the advice of `reserve`
        huge(p, bytes);
    }
}

static REGION: std::sync::OnceLock<Region> = std::sync::OnceLock::new();

pub fn region() -> &'static Region {
    REGION.get_or_init(|| {
        let nodes = vm::reserve(ID_SPACE * 16) as *mut Node;
        assert!(!nodes.is_null(), "cannot reserve the term address range");
        Region { nodes, first: 0.into(), slab: 0.into(), next: 0.into(), big: std::sync::Mutex::new(None) }
    })
}

impl Region {
    #[inline(always)]
    pub fn nodes(&self) -> *const Node {
        self.nodes
    }
    /// MAIN's arena (ids from 0), room for `cap` nodes.
    pub fn main_cols(&self, cap: usize) -> Cols {
        Cols::at(self, 0, cap.min(ID_LIMIT as usize / 2))
    }
    /// After MAIN is loaded: the two overflow arenas, then two slabs per
    /// worker share the ids left below 2^31. Returns the number of workers
    /// whose slabs fit (at least 2^20 ids each; fewer workers than asked
    /// when they do not). Err when MAIN leaves no room for overflow arenas
    /// of 2^20 ids (whatever the number of workers).
    pub fn layout(&self, main_len: usize, workers: usize) -> Result<usize, String> {
        use std::sync::atomic::Ordering::Relaxed;
        let first = (main_len as u64 + 0xffff) & !0xffff;
        let room = ID_LIMIT.saturating_sub(first);
        // a quarter of the room each (at most 2^28 ids, 6 GiB of nodes)
        let mut big = (room / 4).min(1 << 28) & !0xffff;
        let rest = room - 2 * big;
        let mut workers = workers.max(1);
        let mut s = (rest / (2 * workers) as u64).min(1 << 28) & !0xffff;
        if s < 1 << 20 {
            workers = (rest / (2 << 20)) as usize;
            s = 1 << 20;
        }
        if big < 1 << 20 || workers == 0 {
            return Err(format!("no room for block arenas next to {main_len} MAIN nodes"));
        }
        // knobs builds: SK_SLAB_IDS=n makes the slabs n ids, a multiple of 4096 (to test the
        // full path: a block past it runs in the overflow arenas); SK_BIG_IDS=n makes the
        // overflow arenas n ids (default: SK_SLAB_IDS, so a block past it declines)
        if cfg!(feature = "knobs") {
            let knob = |v: &str| std::env::var(v).ok().and_then(|x| x.parse::<u64>().ok()).map(|k| k.max(1 << 12) & !0xfff);
            if let Some(k) = knob("SK_SLAB_IDS") {
                s = s.min(k);
                big = big.min(k);
            }
            // (SK_BIG_IDS=0: the default size, with small slabs)
            if let Ok(k) = std::env::var("SK_BIG_IDS") {
                let d = (room / 4).min(1 << 28) & !0xffff;
                big = match k.parse::<u64>() {
                    Ok(0) => d,
                    _ => d.min(knob("SK_BIG_IDS").unwrap_or(d)),
                };
            }
        }
        self.first.store((first + 2 * big) as u32, Relaxed);
        self.slab.store(s as u32, Relaxed);
        let b = (Cols::at(self, first as u32, big as usize), Cols::at(self, (first + big) as u32, big as usize));
        *self.big.lock().unwrap() = Some(b);
        Ok(workers)
    }
    /// One block arena (a slab of the layout).
    pub fn take(&self) -> Cols {
        use std::sync::atomic::Ordering::Relaxed;
        let s = self.slab.load(Relaxed) as u64;
        assert!(s != 0, "block arenas taken before the layout");
        let k = self.next.fetch_add(1, Relaxed) as u64;
        let base = self.first.load(Relaxed) as u64 + k * s;
        assert!(base + s <= ID_LIMIT, "more block arenas than the layout has");
        Cols::at(self, base as u32, s as usize)
    }
}

/// Milestone 19: a growable array in its own reserved address range
/// (`cap` elements, pages made on first write), for the worker's large
/// per-session arrays (values, environments, spines). Unlike a `Vec` it
/// never moves: no reallocation copy (whose old block the allocator purges
/// lazily, and macOS still counts in max RSS) and a base that stays put.
/// Pages past the keep size go back at a session end (`shrink`).
/// Milestone 47: past `soft` (seven eighths of `cap`) the worker's next
/// slow tick declines (`over_soft`); a push past `cap` itself still panics
/// (the worker declines the declaration and starts a new session). CFSG's
/// archiveGiantBytes filled the value table (2^28) and panicked.
pub struct Slab<T: Copy> {
    p: *mut T,
    len: usize,
    soft: usize,
    cap: usize,
    /// largest length since pages were last given back
    hw: usize,
}
unsafe impl<T: Copy> Send for Slab<T> {}
unsafe impl<T: Copy> Sync for Slab<T> {}

impl<T: Copy> Default for Slab<T> {
    fn default() -> Slab<T> {
        Slab { p: std::ptr::NonNull::dangling().as_ptr(), len: 0, soft: 0, cap: 0, hw: 0 }
    }
}

impl<T: Copy> Slab<T> {
    pub fn new(cap: usize) -> Slab<T> {
        let p = vm::reserve(cap * std::mem::size_of::<T>()) as *mut T;
        assert!(!p.is_null(), "cannot reserve a worker table's address range");
        Slab { p, len: 0, soft: cap - cap / 8, cap, hw: 0 }
    }
    #[cold]
    #[inline(never)]
    fn full(&self) -> ! {
        panic!("a worker table is full ({} entries)", self.cap)
    }
    /// Past seven eighths of the room (read at the worker's slow tick, not
    /// at every push: a check in `push` cost 0.5% instructions on Init)
    #[inline(always)]
    pub fn over_soft(&self) -> bool {
        self.len > self.soft
    }
    #[inline(always)]
    pub fn push(&mut self, x: T) {
        if self.len == self.cap {
            self.full();
        }
        unsafe { self.p.add(self.len).write(x) };
        self.len += 1;
    }
    #[inline(always)]
    pub fn reserve(&mut self, _n: usize) {}
    #[inline]
    pub fn extend_from_slice(&mut self, xs: &[T]) {
        if self.cap - self.len < xs.len() {
            self.full();
        }
        unsafe { std::ptr::copy_nonoverlapping(xs.as_ptr(), self.p.add(self.len), xs.len()) };
        self.len += xs.len();
    }
    #[inline]
    pub fn extend_from_within(&mut self, r: std::ops::Range<usize>) {
        assert!(r.start <= r.end && r.end <= self.len);
        let n = r.end - r.start;
        if self.cap - self.len < n {
            self.full();
        }
        unsafe { std::ptr::copy_nonoverlapping(self.p.add(r.start), self.p.add(self.len), n) };
        self.len += n;
    }
    pub fn clear(&mut self) {
        self.hw = self.hw.max(self.len);
        self.len = 0;
    }
    /// Milestone 37: bytes of pages held (the high-water mark since pages
    /// were last given back)
    pub fn held_bytes(&self) -> usize {
        self.hw.max(self.len) * std::mem::size_of::<T>()
    }
    /// Milestone 36: drops the elements past `n` (a region's rollback; the
    /// pages stay for the elements made next).
    pub fn truncate(&mut self, n: usize) {
        self.hw = self.hw.max(self.len);
        self.len = self.len.min(n);
    }
    /// After `clear`: keeps about `max / 2` bytes of pages when more than
    /// `max` are held (as `clear_vec` shrinks a vector); the rest go back.
    pub fn shrink(&mut self, max: usize) {
        let sz = std::mem::size_of::<T>();
        let hw = self.hw * sz;
        if hw > max {
            // from a 64 KiB boundary to the end of the pages held
            let keep = (max / 2 + 0xffff) & !0xffff;
            if keep < hw {
                #[cfg(unix)]
                unsafe {
                    let end = (hw + 0xffff) & !0xffff;
                    vm::release((self.p as *mut u8).add(keep), end - keep);
                }
                self.hw = keep / sz;
            }
        }
    }
    /// The entries the table can hold at all.
    #[inline(always)]
    pub fn cap(&self) -> usize {
        self.cap
    }
    /// Elements whose pages may be held.
    pub fn capacity(&self) -> usize {
        self.hw.max(self.len)
    }
}

impl<T: Copy> std::ops::Deref for Slab<T> {
    type Target = [T];
    #[inline(always)]
    fn deref(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.p, self.len) }
    }
}
impl<T: Copy> std::ops::DerefMut for Slab<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.p, self.len) }
    }
}

/// A column store at a fixed place of the region: ids [base, base + cap).
pub struct Cols {
    /// id of node 0
    pub base: u32,
    n_ptr: *mut Node,
    /// the used masks of APP, LAM and PI nodes with bits past 30 (the
    /// node's `u` is `U_SIDE` and the index here)
    pub wide: Vec<Used>,
    len: usize,
    cap: usize,
    /// largest length since pages were last given back
    hw: usize,
    pub too_deep: bool,
    /// a push past `cap` was dropped (the decoder declines)
    pub full: bool,
}
unsafe impl Send for Cols {}
unsafe impl Sync for Cols {}

impl Default for Cols {
    fn default() -> Cols {
        let n_ptr = std::ptr::NonNull::dangling().as_ptr();
        Cols { base: 0, n_ptr, wide: Vec::new(), len: 0, cap: 0, hw: 0, too_deep: false, full: false }
    }
}

impl Cols {
    fn at(r: &Region, base: u32, cap: usize) -> Cols {
        let n_ptr = unsafe { r.nodes.add(base as usize) };
        Cols { base, n_ptr, wide: Vec::new(), len: 0, cap, hw: 0, too_deep: false, full: false }
    }
    #[inline(always)]
    pub fn push(&mut self, k: u8, a: u32, b: u32, p: u32, r: u32, u: u64) {
        self.push_h(k, a, b, p, r, (u, 0))
    }
    /// `push` with the whole used mask (kept in the node, see `Node`); `x`
    /// is a LET's or PROJ's side index.
    #[inline(always)]
    pub fn push_h(&mut self, k: u8, a: u32, b: u32, x: u32, r: u32, (u, h): (u64, u64)) {
        if r >= u16::MAX as u32 {
            self.too_deep = true;
        }
        if self.len == self.cap {
            self.full = true;
            return;
        }
        // by the mask, not the range: a mask may claim more than the range
        // reads (a binder shifts "63 or more" down)
        let narrow = u >> 31 == 0 && h == 0;
        let w = match k {
            LET | PROJ => U_SIDE | x,
            _ if narrow => u as u32,
            BVAR => U_SIDE,
            _ => {
                self.wide.push((u, h));
                U_SIDE | (self.wide.len() as u32 - 1)
            }
        };
        unsafe {
            self.n_ptr.add(self.len).write(Node { a, b, u: w, rng: r.min(u16::MAX as u32) as u16, kind: k, _pad: 0 });
        }
        self.len += 1;
    }
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }
    /// The nodes (index = id - base).
    #[inline(always)]
    pub fn n(&self) -> &[Node] {
        unsafe { std::slice::from_raw_parts(self.n_ptr, self.len) }
    }
    pub fn n_mut(&mut self) -> &mut [Node] {
        unsafe { std::slice::from_raw_parts_mut(self.n_ptr, self.len) }
    }
    pub fn clear(&mut self) {
        self.wide.clear();
        self.hw = self.hw.max(self.len);
        self.len = 0;
        self.too_deep = false;
        self.full = false;
    }
    /// Keeps at most about `max` bytes of pages (after `clear`); the pages
    /// past that go back to the system.
    pub fn shrink(&mut self, max: usize) {
        if self.bytes() > max {
            // whole pages (4096 nodes: 64 KiB)
            let keep = (max / 16 + 4095) & !4095;
            if keep < self.hw {
                #[cfg(unix)]
                unsafe {
                    vm::release(self.n_ptr.add(keep) as *mut u8, (self.hw - keep) * 16);
                }
                self.hw = keep;
                self.wide = Vec::new();
            }
        }
    }
    /// Bytes of pages possibly held (high water), and the wide masks.
    pub fn bytes(&self) -> usize {
        16 * self.hw.max(self.len) + self.wide.capacity() * 16
    }
}

/// Lets and level lists of a column store (MAIN or a block arena).
#[derive(Default)]
pub struct Side {
    /// LET: (binder name id, body expr id).
    pub lets: Vec<(u32, u32)>,
    /// LET: the used mask, by the same index
    pub let_used: Vec<Used>,
    /// PROJ: the structure name id (the node's `u` is `U_SIDE` and the index)
    pub projs: Vec<u32>,
    /// Level lists, length-prefixed, global level ids; offset 0 is the empty list.
    pub lvls: Vec<u32>,
}

impl Side {
    pub fn new() -> Side {
        Side { lets: Vec::new(), let_used: Vec::new(), projs: Vec::new(), lvls: vec![0] }
    }
    pub fn clear(&mut self) {
        self.lets.clear();
        self.let_used.clear();
        self.projs.clear();
        self.lvls.truncate(1);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LitVal {
    Nat(BigUint),
    Str(Box<str>),
}

/// The used mask of a term as two words: `lo` has bit i for #i (i < 63)
/// and bit 63 for any index of 63 or more; `hi` (meaningful only past
/// range 63) has bit j for #(63 + j) (j < 63) and bit 63 for any index of
/// 126 or more. Milestone 51: with one word, a binder shifted the "63 or
/// more" bit down into bit 62, then 61, ..., so under a telescope of more
/// than 63 binders every term's mask claimed nearly every variable (RH's
/// pack_heq: 2.9 M bits set where 0.68 M are read). The inference keys,
/// pruned environments and variables of the checker are built from these
/// masks: equal subterms under different binders never met, and checking
/// the 122 K-node type walked it as a tree.
pub type Used = (u64, u64);

/// The used mask of a binder's body seen from outside the binder.
#[inline(always)]
pub fn used_bind((lo, hi): Used) -> Used {
    let l = lo & !(1 << 63);
    let h = hi & !(1 << 63);
    let s = hi >> 63;
    let low = (l >> 1) | ((h & 1) << 62);
    let hi2 = (h >> 1) | (s << 62) | (s << 63);
    (low | (((hi2 != 0) as u64) << 63), hi2)
}
#[inline(always)]
fn used_or(a: Used, b: Used) -> Used {
    (a.0 | b.0, a.1 | b.1)
}
/// Bit 31 of a node's `u`: the mask (or a LET's, PROJ's payload) is not
/// in the node (see `Node`).
pub const U_SIDE: u32 = 1 << 31;
/// The used mask of term `id`: in `cols` (ids from `cols.base`, with
/// `side`), below that in `main` (MAIN's columns and side, or `cols` itself
/// when it is MAIN).
pub fn used_of(mut id: u32, cols: &Cols, side: &Side, main: Option<(&Cols, &Side)>) -> Used {
    loop {
        let (c, sd) = if id >= cols.base { (cols, side) } else { main.unwrap_or((cols, side)) };
        let n = c.n()[(id - c.base) as usize];
        if n.u & U_SIDE == 0 {
            return (n.u as u64, 0);
        }
        return match n.kind {
            BVAR => used_var(n.a),
            LET => sd.let_used[(n.u & !U_SIDE) as usize],
            PROJ => {
                id = n.a;
                continue;
            }
            _ => c.wide[(n.u & !U_SIDE) as usize],
        };
    }
}
#[inline(always)]
pub fn used_var(i: u32) -> Used {
    if i < 63 {
        (1u64 << i, 0)
    } else if i < 126 {
        (1u64 << 63, 1u64 << (i - 63))
    } else {
        (1u64 << 63, 1u64 << 63)
    }
}

pub fn rng_bind(body: u32) -> u32 {
    body.saturating_sub(1)
}

/// Appends one decoded expression; `base` is the global id of block-local
/// expression 0 (MAIN uses 0). `rng_of` looks up the range of an id below
/// `base` (or in `cols` above it). Literals go to `lits`.
#[inline(always)]
pub fn push_expr(
    cols: &mut Cols,
    side: &mut Side,
    lits: &mut Vec<LitVal>,
    lit_base: u32,
    cols_base: u32,
    base: u32,
    lvl_map: &[u32],
    main: Option<(&Cols, &Side)>,
    e: &Expr<'_>,
) {
    debug_assert_eq!(cols.base, cols_base, "push_expr: columns at another base");
    let r = |x: Ref| match x {
        Ref::Main(i) => i,
        Ref::Block(k) => base + k,
    };
    let rg = |cols: &Cols, id: u32| -> u32 {
        if id >= cols_base {
            cols.n()[(id - cols_base) as usize].rng as u32
        } else {
            match main {
                Some((m, _)) => m.n()[id as usize].rng as u32,
                None => cols.n()[id as usize].rng as u32,
            }
        }
    };
    let us = |cols: &Cols, side: &Side, id: u32| -> Used {
        let u = if id >= cols_base {
            cols.n()[(id - cols_base) as usize].u
        } else {
            match main {
                Some((m, _)) => m.n()[id as usize].u,
                None => cols.n()[id as usize].u,
            }
        };
        if u & U_SIDE == 0 { (u as u64, 0) } else { used_of(id, cols, side, main) }
    };
    let lmap = |l: u32| -> u32 { if lvl_map.is_empty() { l } else { lvl_map[l as usize] } };
    match *e {
        Expr::BVar(i) => {
            let i = u32::try_from(i).unwrap_or(u32::MAX - 1);
            cols.push_h(BVAR, i, 0, 0, i.saturating_add(1), used_var(i))
        }
        Expr::Sort(l) => cols.push(SORT, lmap(l), 0, 0, 0, 0),
        Expr::Const(n, ls) => {
            let off = if ls.is_empty() {
                0
            } else {
                let off = side.lvls.len() as u32;
                side.lvls.push(ls.len() as u32);
                side.lvls.extend(ls.iter().map(lmap));
                off
            };
            cols.push(CONST, n, off, 0, 0, 0)
        }
        Expr::App(f, x) => {
            let (f, x) = (r(f), r(x));
            let rr = rg(cols, f).max(rg(cols, x));
            let uu = used_or(us(cols, side, f), us(cols, side, x));
            cols.push_h(APP, f, x, 0, rr, uu)
        }
        Expr::Lam(bi, n, t, b) => {
            let (t, b) = (r(t), r(b));
            let rr = rg(cols, t).max(rng_bind(rg(cols, b)));
            let uu = used_or(us(cols, side, t), used_bind(us(cols, side, b)));
            let _ = n;
            cols.push_h(LAM + bi, t, b, 0, rr, uu)
        }
        Expr::Pi(bi, n, t, b) => {
            let (t, b) = (r(t), r(b));
            let rr = rg(cols, t).max(rng_bind(rg(cols, b)));
            let uu = used_or(us(cols, side, t), used_bind(us(cols, side, b)));
            let _ = n;
            cols.push_h(PI + bi, t, b, 0, rr, uu)
        }
        Expr::Let(n, t, v, b) => {
            let (t, v, b) = (r(t), r(v), r(b));
            let rr = rg(cols, t).max(rg(cols, v)).max(rng_bind(rg(cols, b)));
            let uu = used_or(used_or(us(cols, side, t), us(cols, side, v)), used_bind(us(cols, side, b)));
            let i = side.lets.len() as u32;
            side.lets.push((n, b));
            side.let_used.push(uu);
            cols.push_h(LET, t, v, i, rr, uu)
        }
        Expr::Nat(bytes) => {
            let i = lit_base + lits.len() as u32;
            lits.push(LitVal::Nat(<BigUint as NatExt>::from_bytes_le(bytes)));
            cols.push(NAT, i, 0, 0, 0, 0)
        }
        Expr::Str(s) => {
            let i = lit_base + lits.len() as u32;
            lits.push(LitVal::Str(s.into()));
            cols.push(STR, i, 0, 0, 0, 0)
        }
        Expr::Proj(s, f, x) => {
            let x = r(x);
            let rr = rg(cols, x);
            let uu = us(cols, side, x);
            let j = side.projs.len() as u32;
            side.projs.push(s);
            cols.push_h(PROJ, x, u32::try_from(f).unwrap_or(u32::MAX), j, rr, uu)
        }
    }
}

// ---------------------------------------------------------------------------
// Constants

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hint {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Clone, Copy, Debug)]
pub enum ThmVal {
    Main(u32),
    Block(u32),
}

#[derive(Clone, Debug)]
pub enum CKind {
    Axiom { unsafe_: bool },
    /// safety: 0 safe, 1 unsafe, 2 partial
    Defn { value: u32, hint: Hint, safety: u8, all: Box<[u32]> },
    Thm { value: ThmVal, all: Box<[u32]> },
    Opaque { value: u32, unsafe_: bool, all: Box<[u32]> },
    Quot { kind: u8 },
    Induct {
        nparams: u32,
        nindices: u32,
        all: Box<[u32]>,
        ctors: Box<[u32]>,
        nnested: u32,
        is_rec: bool,
        /// `None` when the export does not carry it (Lean since lean4#16595,
        /// Susz kind 8): the kernel computes it and has nothing to compare.
        is_reflexive: Option<bool>,
        unsafe_: bool,
        /// The five flags of lean4export 3.2 (lean4#16595), inputs the
        /// kernel checks and then uses; `None` in a 3.1 export, where the
        /// kernel works them out as before.
        flags: Option<IndFlags>,
    },
    Ctor { induct: u32, cidx: u32, nparams: u32, nfields: u32, unsafe_: bool },
    Rec {
        all: Box<[u32]>,
        nparams: u32,
        nindices: u32,
        nmotives: u32,
        nminors: u32,
        /// (ctor name id, nfields, rhs MAIN id)
        rules: Box<[(u32, u32, u32)]>,
        k: bool,
        unsafe_: bool,
    },
}

/// One row per constant. Names are raw Susz name ids; compare them through
/// `Env::canon`.
#[derive(Clone, Debug)]
pub struct ConstInfo {
    pub name: u32,
    pub lparams: Box<[u32]>,
    pub ty: u32,
    /// Index of the declaration record that declares it.
    pub decl: u32,
    /// 0 inductive type, 1 constructor, 2 recursor, 3 anything else.
    pub group: u8,
    pub kind: CKind,
}

impl ConstInfo {
    pub fn is_unsafe(&self) -> bool {
        match &self.kind {
            CKind::Axiom { unsafe_ } | CKind::Opaque { unsafe_, .. } => *unsafe_,
            CKind::Defn { safety, .. } => *safety == 1,
            CKind::Thm { .. } | CKind::Quot { .. } => false,
            CKind::Induct { unsafe_, .. } | CKind::Ctor { unsafe_, .. } | CKind::Rec { unsafe_, .. } => *unsafe_,
        }
    }
}

fn u(x: u64) -> u32 {
    u32::try_from(x).unwrap_or(u32::MAX)
}

/// Names the kernel knows (canonical ids, `NONE` when absent from the file).
#[derive(Default, Clone, Copy, Debug)]
pub struct Known {
    pub nat: u32,
    pub nat_zero: u32,
    pub nat_succ: u32,
    /// `nat_zero` / `nat_succ` when declared with no universe parameters,
    /// else NONE: only then is the constant read as a literal (`0`, `n+1`)
    /// by the kernel's Nat rules (Lean's `e == mk_constant(Nat.zero)`)
    pub nat_zero_lit: u32,
    pub nat_succ_lit: u32,
    pub string: u32,
    pub string_of_list: u32,
    pub list: u32,
    pub list_nil: u32,
    pub list_cons: u32,
    pub char_: u32,
    pub char_of_nat: u32,
    pub bool_true: u32,
    pub bool_false: u32,
    pub eq: u32,
    pub eq_refl: u32,
    pub quot: u32,
    pub quot_mk: u32,
    pub quot_lift: u32,
    pub quot_ind: u32,
    /// Nat binary operations, in `NatOp` order.
    pub nat_ops: [u32; 14],
}

pub const NONE: u32 = u32::MAX;

pub const NAT_OPS: [&str; 14] =
    ["add", "sub", "mul", "div", "mod", "gcd", "beq", "ble", "land", "lor", "xor", "shiftLeft", "shiftRight", "pow"];

pub struct Env<'f> {
    pub bytes: &'f [u8],
    pub st: State,
    pub main: Cols,
    pub side: Side,
    pub lits: Vec<LitVal>,
    /// Global levels: kind (0 zero, 1 succ, 2 max, 3 imax, 4 param), a, b.
    /// Param's `a` is a canonical name id. Interned: equal structure, equal id.
    pub lvl: Vec<(u8, u32, u32)>,
    pub lvl_intern: FxHashMap<(u8, u32, u32), u32>,
    /// milestone 16: MAIN's level lists by content, one offset into
    /// `side.lvls` each (every CONST term's `p` is that offset), so an
    /// offset names its content
    pub ll_canon: FxHashMap<Box<[u32]>, u32>,
    /// File level id to global level id.
    pub lvl_map: Vec<u32>,
    pub consts: Vec<ConstInfo>,
    /// Raw name id to constant row (`NONE`).
    pub row_of_name: Vec<u32>,
    /// Declaration index to its first row and number of rows.
    pub decl_rows: Vec<(u32, u32)>,
    /// Declaration index: duplicate universe parameter names.
    pub decl_dup_params: Vec<bool>,
    pub blocks: Vec<BlockRef>,
    pub known: Known,
    /// Canonical name to row (NONE), indexed by canonical id (milestone
    /// 27: a dense vector, was a hash map)
    pub row_of_canon: Vec<u32>,
    /// Recursor rows: the inductive of the major premise (canonical name), if found.
    pub rec_major: FxHashMap<u32, u32>,
    /// Per row: 1 + index into NAT_OPS, 100 Nat.succ, 0 other (Lean's
    /// kernel computes these on literals and nothing else: Nat.log2 and the
    /// rest unfold from their definitions).
    pub nat_op: Vec<u8>,
    /// The file's inductive types carry the flags of lean4export 3.2
    /// (every one of them: the reader rejects a file mixing flagged and
    /// unflagged blocks).
    pub flagged: bool,
    /// Renovation: rules of recursors that never reduce, held out of their
    /// row (whose `rules` is then empty) for the recursor check alone. Lean
    /// (lean4#16595 inductive_reduce_rec) reduces no recursor whose major
    /// premise's inductive lacks `hasLargeElim`: a type without it has no
    /// rules, and an auxiliary recursor of a block with large elimination
    /// nested through such a type has rules that never fire.
    pub rec_rules_held: FxHashMap<u32, Box<[(u32, u32, u32)]>>,
}

impl<'f> Env<'f> {
    #[inline(always)]
    pub fn canon(&self, name: u32) -> u32 {
        self.st.name_canon[name as usize]
    }
    pub fn name_str(&self, name: u32) -> String {
        if (name as usize) < self.st.name_canon.len() {
            self.st.name_display(self.bytes, name)
        } else {
            format!("<name {name}>")
        }
    }
    pub fn row(&self, name: u32) -> u32 {
        self.row_of_name.get(name as usize).copied().unwrap_or(NONE)
    }
    pub fn known_row(&self, canon: u32) -> u32 {
        self.row_of_canon.get(canon as usize).copied().unwrap_or(NONE)
    }
}

struct Loader {
    main: Cols,
    side: Side,
    lits: Vec<LitVal>,
    file_lvls: Vec<Level>,
    consts: Vec<ConstInfo>,
    decl_rows: Vec<(u32, u32)>,
    decl_dup: Vec<bool>,
    blocks: Vec<BlockRef>,
}

fn params(h: &susz::read::Head<'_>) -> Box<[u32]> {
    h.params.iter().collect::<Vec<_>>().into_boxed_slice()
}

impl<'a> Visit<'a> for Loader {
    type Error = ();
    fn name(&mut self, _id: u32, _prefix: u32, _part: Component<'a>) -> Result<(), ()> {
        Ok(())
    }
    fn level(&mut self, _id: u32, l: Level) -> Result<(), ()> {
        self.file_lvls.push(l);
        Ok(())
    }
    #[inline(always)]
    fn expr(&mut self, _id: u32, x: &Expr<'a>) -> Result<(), ()> {
        push_expr(&mut self.main, &mut self.side, &mut self.lits, 0, 0, 0, &[], None, x);
        Ok(())
    }
    fn open_block(&mut self, b: &BlockRef) -> bool {
        self.blocks.push(*b);
        false
    }
    fn decl(&mut self, index: u32, _offset: u64, d: &Decl<'a>) -> Result<(), ()> {
        debug_assert_eq!(index as usize, self.decl_rows.len());
        let first = self.consts.len() as u32;
        let mut push = |name: u32, lp: Box<[u32]>, ty: u32, group: u8, kind: CKind| {
            self.consts.push(ConstInfo { name, lparams: lp, ty, decl: index, group, kind });
        };
        let mut dup = false;
        let mut check_dup = |h: &susz::read::Head<'_>| {
            let v: Vec<u32> = h.params.iter().collect();
            v
        };
        let _ = &mut check_dup;
        let all = |ids: &susz::read::Ids<'_>| ids.iter().collect::<Vec<_>>().into_boxed_slice();
        match d {
            Decl::Axiom { head, is_unsafe } => {
                push(head.name, params(head), head.ty, 3, CKind::Axiom { unsafe_: *is_unsafe })
            }
            Decl::Defn { head, value, hints, safety, all: a } => {
                let hint = match hints {
                    Hints::Opaque => Hint::Opaque,
                    Hints::Abbrev => Hint::Abbrev,
                    Hints::Regular(n) => Hint::Regular(u(*n)),
                };
                push(head.name, params(head), head.ty, 3, CKind::Defn { value: *value, hint, safety: *safety, all: all(a) })
            }
            Decl::Thm { head, value, all: a } => {
                push(head.name, params(head), head.ty, 3, CKind::Thm { value: ThmVal::Main(*value), all: all(a) })
            }
            Decl::Opaque { head, value, is_unsafe, all: a } => {
                push(head.name, params(head), head.ty, 3, CKind::Opaque { value: *value, unsafe_: *is_unsafe, all: all(a) })
            }
            Decl::Quot { head, kind } => {
                push(head.name, params(head), head.ty, 3, CKind::Quot { kind: *kind })
            }
            Decl::ThmBlock { head, block, all: a } => {
                let i = self.blocks.len() as u32 - 1;
                debug_assert_eq!(self.blocks[i as usize], *block);
                push(head.name, params(head), head.ty, 3, CKind::Thm { value: ThmVal::Block(i), all: all(a) })
            }
            Decl::Inductive(ind) => {
                for t in &ind.types {
                    push(
                        t.head.name,
                        params(&t.head),
                        t.head.ty,
                        0,
                        CKind::Induct {
                            nparams: u(t.num_params),
                            nindices: u(t.num_indices),
                            all: all(&t.all),
                            ctors: all(&t.ctors),
                            nnested: u(t.num_nested),
                            is_rec: t.is_rec,
                            is_reflexive: t.is_reflexive,
                            unsafe_: t.is_unsafe,
                            flags: t.flags,
                        },
                    );
                }
                for c in &ind.ctors {
                    push(
                        c.head.name,
                        params(&c.head),
                        c.head.ty,
                        1,
                        CKind::Ctor {
                            induct: c.induct,
                            cidx: u(c.cidx),
                            nparams: u(c.num_params),
                            nfields: u(c.num_fields),
                            unsafe_: c.is_unsafe,
                        },
                    );
                }
                for r in &ind.recs {
                    push(
                        r.head.name,
                        params(&r.head),
                        r.head.ty,
                        2,
                        CKind::Rec {
                            all: all(&r.all),
                            nparams: u(r.num_params),
                            nindices: u(r.num_indices),
                            nmotives: u(r.num_motives),
                            nminors: u(r.num_minors),
                            rules: r.rules.iter().map(|x| (x.ctor, u(x.nfields), x.rhs)).collect(),
                            k: r.k,
                            unsafe_: r.is_unsafe,
                        },
                    );
                }
            }
        }
        // duplicate universe params (raw ids; recheck canonically later);
        // milestone 27: on the rows' own lists (no copy per head)
        for c in &self.consts[first as usize..] {
            let h = &c.lparams;
            for i in 0..h.len() {
                for j in 0..i {
                    if h[i] == h[j] {
                        dup = true;
                    }
                }
            }
        }
        let n = self.consts.len() as u32 - first;
        self.decl_rows.push((first, n));
        self.decl_dup.push(dup);
        Ok(())
    }
}

/// Milestone 27: threads for the passes of `load` after the decode (the
/// workers are idle then); main sets it to the worker count.
pub static LOAD_THREADS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(1);

/// Milestone 27: `f` over `xs` in contiguous chunks on up to LOAD_THREADS
/// threads (the slices are disjoint: the same result as one pass).
fn par_chunks<T: Send>(xs: &mut [T], f: impl Fn(&mut [T]) + Sync) {
    let t = LOAD_THREADS.load(std::sync::atomic::Ordering::Relaxed).clamp(1, 16);
    if t == 1 || xs.len() < 1 << 16 {
        return f(xs);
    }
    let c = xs.len().div_ceil(t);
    std::thread::scope(|sc| {
        let f = &f;
        let mut it = xs.chunks_mut(c);
        let first = it.next();
        for ch in it {
            sc.spawn(move || f(ch));
        }
        if let Some(ch) = first {
            f(ch);
        }
    });
}

pub enum LoadError {
    Reject(String),
    Decline(String),
    /// Milestone 26 (`--only`): INDEX disagrees with a record it was relied
    /// on for. No verdict on the file.
    IndexInvalid(String),
}

/// Milestone 26: what a subset check (`--only`) reads of MAIN, and what
/// INDEX said of each target, to be held to its record as MAIN is read.
pub struct Part {
    /// Declarations read: MAIN stops after declaration `up_to - 1`.
    pub up_to: u32,
    /// Per target declaration: its INDEX entry and the keys asked for that
    /// INDEX says it declares.
    pub marks: FxHashMap<u32, (susz::index::Entry, Vec<Vec<u8>>)>,
    /// Where INDEX starts (absolute), for messages.
    pub index_at: u64,
}

/// What INDEX says of declaration `n` that its record does not (Pestka's
/// `markWrong`, same wording): the offset from the start of MAIN, the kind,
/// the proof block (offset from the start of PROOFS and length), then the
/// names asked for, each of which must be declared by this record.
fn mark_wrong(
    e: &susz::index::Entry,
    keys: &[Vec<u8>],
    n: u32,
    off: u64,
    d: &Decl<'_>,
    proofs: u64,
    st: &State,
    bytes: &[u8],
) -> Option<String> {
    if e.offset != off {
        return Some(format!("entry {n}: offset {}, its record is at {off}", e.offset));
    }
    if e.kind != d.kind() {
        return Some(format!("entry {n}: kind {}, its record's is {}", e.kind, d.kind()));
    }
    if let Decl::ThmBlock { block, .. } = d {
        let (o, l) = e.block.unwrap_or((u64::MAX, 0));
        let ro = block.offset.wrapping_sub(proofs);
        if o != ro || l != block.length {
            return Some(format!(
                "entry {n}: a block of {l} bytes at {o}, its record's is {} bytes at {ro}",
                block.length
            ));
        }
    }
    for k in keys {
        match st.canon.find_key(bytes, k) {
            Some(c) if st.canon_decl.get(c as usize) == Some(&n) => {}
            _ => return Some(format!("a name INDEX gives declaration {n} is not declared by it")),
        }
    }
    None
}

/// Loads the file; with `part` (milestone 26) MAIN is read only up to the
/// last target, each target's INDEX entry held to its record.
pub fn load_part<'f>(bytes: &'f [u8], part: Option<&Part>) -> Result<Env<'f>, LoadError> {
    let file = susz::read::File::open(bytes).map_err(|f| {
        if f.class.declines() { LoadError::Decline(f.to_string()) } else { LoadError::Reject(f.to_string()) }
    })?;
    let [_nn, nl, ne, _nd] = file.counts.map(|c| c as usize);
    let cap = |c: usize| c.min(bytes.len());
    let mut ld = Loader {
        // milestone 18: MAIN's nodes at the start of the term range
        main: region().main_cols(cap(ne)),
        side: Side::new(),
        lits: Vec::new(),
        file_lvls: Vec::with_capacity(cap(nl)),
        consts: Vec::new(),
        decl_rows: Vec::new(),
        decl_dup: Vec::new(),
        blocks: Vec::new(),
    };
    let failed = |f: susz::read::Failure| {
        if f.class.declines() { LoadError::Decline(f.to_string()) } else { LoadError::Reject(f.to_string()) }
    };
    let mut st = match part {
        None => match susz::read::decode(&file, &mut ld) {
            Ok(d) => d.state,
            Err(susz::read::Stop::File(f)) => return Err(failed(f)),
            Err(susz::read::Stop::Visitor(())) => return Err(LoadError::Decline("loader stopped".into())),
        },
        Some(p) => {
            // milestone 26: MAIN's records one by one, up to the last
            // target's; the rest of MAIN is never read (nor checked: a
            // structural error past it is not seen, as in Pestka)
            use susz::read::Event;
            let mut m = file.main();
            let start = m.start();
            let proofs = file.section(susz::format::SEC_PROOFS).map_or(0, |s| s.offset);
            let mut read = 0u32;
            while read < p.up_to {
                let ev = match m.next() {
                    None => {
                        return Err(LoadError::IndexInvalid(format!(
                            "INDEX @ {}: declaration {} is not in MAIN",
                            p.index_at, read
                        )))
                    }
                    Some(Err(f)) => return Err(failed(f)),
                    Some(Ok(ev)) => ev,
                };
                let r = match &ev {
                    Event::Name { id, prefix, part } => ld.name(*id, *prefix, *part),
                    Event::Level { id, level } => ld.level(*id, *level),
                    Event::Expr { id, expr } => ld.expr(*id, expr),
                    Event::Frontier { .. } => Ok(()),
                    Event::Decl { index, offset, decl } => {
                        if let Some((e, keys)) = p.marks.get(index) {
                            if let Some(w) = mark_wrong(e, keys, *index, offset - start, decl, proofs, m.state(), bytes) {
                                return Err(LoadError::IndexInvalid(format!("INDEX @ {}: {w}", p.index_at)));
                            }
                        }
                        if let Decl::ThmBlock { block, .. } = decl {
                            ld.open_block(block);
                        }
                        read = index + 1;
                        ld.decl(*index, *offset, decl)
                    }
                };
                if r.is_err() {
                    return Err(LoadError::Decline("loader stopped".into()));
                }
            }
            m.into_state()
        }
    };
    if ld.main.too_deep {
        return Err(LoadError::Decline("a term has 65535 or more loose bound variables".into()));
    }
    if ld.main.full {
        return Err(LoadError::Decline("more expressions than the file's count".into()));
    }
    // levels: intern with canonical param names
    let mut lvl: Vec<(u8, u32, u32)> = vec![(0, 0, 0)];
    let mut lvl_intern: FxHashMap<(u8, u32, u32), u32> = FxHashMap::default();
    lvl_intern.insert((0, 0, 0), 0);
    let mut lvl_map: Vec<u32> = vec![0];
    for l in &ld.file_lvls {
        let key = match *l {
            Level::Succ(x) => (1, lvl_map[x as usize], 0),
            Level::Max(x, y) => (2, lvl_map[x as usize], lvl_map[y as usize]),
            Level::IMax(x, y) => (3, lvl_map[x as usize], lvl_map[y as usize]),
            Level::Param(n) => (4, st.name_canon[n as usize], 0),
        };
        let id = *lvl_intern.entry(key).or_insert_with(|| {
            lvl.push(key);
            lvl.len() as u32 - 1
        });
        lvl_map.push(id);
    }
    let mut main = ld.main;
    let mut side = ld.side;
    {
        let mut i = 1;
        while i < side.lvls.len() {
            let n = side.lvls[i] as usize;
            for j in i + 1..i + 1 + n {
                side.lvls[j] = lvl_map[side.lvls[j] as usize];
            }
            i += 1 + n;
        }
    }
    // milestone 16: one offset per level-list content (CONST terms point
    // at the first list with their content; the side table keeps only those)
    let mut ll_canon: FxHashMap<Box<[u32]>, u32> = FxHashMap::default();
    {
        let mut new_lvls: Vec<u32> = vec![0];
        // old offset -> new offset (written at list starts only)
        let mut remap: Vec<u32> = vec![0; side.lvls.len()];
        let mut i = 1;
        while i < side.lvls.len() {
            let n = side.lvls[i] as usize;
            let xs = &side.lvls[i + 1..i + 1 + n];
            let o = match ll_canon.get(xs) {
                Some(&o) => o,
                None => {
                    let o = new_lvls.len() as u32;
                    new_lvls.push(n as u32);
                    new_lvls.extend_from_slice(xs);
                    ll_canon.insert(xs.into(), o);
                    o
                }
            };
            remap[i] = o;
            i += 1 + n;
        }
        // MAIN's level references translated in one pass (milestone 24:
        // was two passes over the node column)
        // milestone 27: in parallel chunks (each node on its own)
        let (lm, rm) = (&lvl_map, &remap);
        par_chunks(main.n_mut(), |ns| {
            for n in ns.iter_mut() {
                if n.kind == SORT {
                    n.a = lm[n.a as usize];
                } else if n.kind == CONST && n.b != 0 {
                    n.b = rm[n.b as usize];
                }
            }
        });
        side.lvls = new_lvls;
    }
    // constant rows by canonical name (declared names are unique by the format)
    // milestone 27: by canonical id in a dense vector (no hash map), and
    // every name id's row gathered from it in parallel chunks
    let mut row_of_canon: Vec<u32> = vec![NONE; st.canon.pre.len()];
    for (i, c) in ld.consts.iter().enumerate() {
        let k = st.name_canon[c.name as usize] as usize;
        if k >= row_of_canon.len() {
            row_of_canon.resize(k + 1, NONE);
        }
        row_of_canon[k] = i as u32;
    }
    let mut row_of_name: Vec<u32> = st.name_canon.clone();
    {
        let rc = &row_of_canon;
        par_chunks(&mut row_of_name, |xs| {
            for x in xs.iter_mut() {
                *x = rc.get(*x as usize).copied().unwrap_or(NONE);
            }
        });
    }
    // duplicate universe params by value
    let mut decl_dup = ld.decl_dup;
    for (d, &(first, n)) in ld.decl_rows.iter().enumerate() {
        for r in first..first + n {
            let lp = &ld.consts[r as usize].lparams;
            for i in 0..lp.len() {
                for j in 0..i {
                    if st.name_canon[lp[i] as usize] == st.name_canon[lp[j] as usize] {
                        decl_dup[d] = true;
                    }
                }
            }
        }
    }
    let find = |path: &[&str]| -> u32 {
        let mut c = susz::canon::ANON;
        for s in path {
            match st.canon.find(bytes, c, susz::canon::Part::Str(s.as_bytes())) {
                Some(x) => c = x,
                None => return NONE,
            }
        }
        c
    };
    let mut known = Known {
        nat: find(&["Nat"]),
        nat_zero: find(&["Nat", "zero"]),
        nat_succ: find(&["Nat", "succ"]),
        nat_zero_lit: NONE,
        nat_succ_lit: NONE,
        string: find(&["String"]),
        string_of_list: find(&["String", "ofList"]),
        list: find(&["List"]),
        list_nil: find(&["List", "nil"]),
        list_cons: find(&["List", "cons"]),
        char_: find(&["Char"]),
        char_of_nat: find(&["Char", "ofNat"]),
        bool_true: find(&["Bool", "true"]),
        bool_false: find(&["Bool", "false"]),
        eq: find(&["Eq"]),
        eq_refl: find(&["Eq", "refl"]),
        quot: find(&["Quot"]),
        quot_mk: find(&["Quot", "mk"]),
        quot_lift: find(&["Quot", "lift"]),
        quot_ind: find(&["Quot", "ind"]),
        nat_ops: [NONE; 14],
    };
    for (i, op) in NAT_OPS.iter().enumerate() {
        known.nat_ops[i] = find(&["Nat", op]);
    }
    // recursor major inductive: walk the type syntactically
    let mut rec_major = FxHashMap::default();
    for (i, c) in ld.consts.iter().enumerate() {
        if let CKind::Rec { nparams, nindices, nmotives, nminors, .. } = &c.kind {
            let skip = *nparams as u64 + *nmotives as u64 + *nminors as u64 + *nindices as u64;
            let mut t = c.ty;
            let mut ok = true;
            for _ in 0..skip {
                if is_pi(main.n()[t as usize].kind) {
                    t = main.n()[t as usize].b;
                } else {
                    ok = false;
                    break;
                }
            }
            if ok && is_pi(main.n()[t as usize].kind) {
                let mut d = main.n()[t as usize].a;
                while main.n()[d as usize].kind == APP {
                    d = main.n()[d as usize].a;
                }
                if main.n()[d as usize].kind == CONST {
                    rec_major.insert(i as u32, st.name_canon[main.n()[d as usize].a as usize]);
                }
            }
        }
    }
    // renovation: the flags come with every inductive block of a file or
    // with none. The reader refuses a file mixing the two (susz: FLAGS
    // present iff every inductive block is kind 7, class flags-section),
    // and the packer a 3.2 export without them.
    let mut n_flagged = 0usize;
    let mut n_plain = 0usize;
    for c in &ld.consts {
        if let CKind::Induct { flags, .. } = &c.kind {
            if flags.is_some() { n_flagged += 1 } else { n_plain += 1 }
        }
    }
    debug_assert!(n_flagged == 0 || n_plain == 0, "susz let a file mix flagged and unflagged inductive blocks");
    let flagged = n_flagged > 0;
    let mut rec_rules_held = FxHashMap::default();
    if flagged {
        // canonical name of every inductive type to its hasLargeElim
        let mut large_of: FxHashMap<u32, bool> = FxHashMap::default();
        for c in ld.consts.iter() {
            if let CKind::Induct { flags: Some(f), .. } = &c.kind {
                large_of.insert(st.name_canon[c.name as usize], f.has_large_elim);
            }
        }
        for (i, c) in ld.consts.iter_mut().enumerate() {
            let CKind::Rec { rules, .. } = &mut c.kind else { continue };
            if rules.is_empty() {
                continue;
            }
            let large = rec_major.get(&(i as u32)).and_then(|m| large_of.get(m)).copied().unwrap_or(true);
            if !large {
                rec_rules_held.insert(i as u32, std::mem::take(rules));
            }
        }
    }
    // Lean's reduce_nat compares the head with `mk_constant(Nat.add)`, a
    // constant with no universe levels: a `Nat.add.{u}` is a definition
    // like any other and unfolds (an occurrence carries as many levels as
    // its declaration has parameters, `infer_const`)
    let unlevelled = |c: u32| -> u32 {
        match row_of_canon.get(c as usize) {
            Some(&r) if r != NONE && ld.consts[r as usize].lparams.is_empty() => c,
            _ => NONE,
        }
    };
    known.nat_zero_lit = unlevelled(known.nat_zero);
    known.nat_succ_lit = unlevelled(known.nat_succ);
    let mut nat_op = vec![0u8; ld.consts.len()];
    for (i, c) in ld.consts.iter().enumerate() {
        if !c.lparams.is_empty() {
            continue;
        }
        let cn = st.name_canon[c.name as usize];
        if let Some(j) = known.nat_ops.iter().position(|&x| x == cn && x != NONE) {
            nat_op[i] = 1 + j as u8;
        } else if cn == known.nat_succ && cn != NONE {
            nat_op[i] = 100;
        }
    }
    // milestone 24s: the quotient package's names are reserved. Lean's
    // kernel adds Quot, Quot.mk, Quot.lift and Quot.ind together at the
    // first quotient record (each name must be free then), so a constant of
    // one of these names declared as anything else (an axiom, a definition,
    // an inductive type, a quotient record of another kind) is either
    // declared before the package (the package cannot be added) or after
    // it (declared twice). Pestka's addQuot does the same.
    for (k, &q) in [known.quot, known.quot_mk, known.quot_lift, known.quot_ind].iter().enumerate() {
        if q == NONE {
            continue;
        }
        if let Some(&r) = row_of_canon.get(q as usize).filter(|&&r| r != NONE) {
            if !matches!(ld.consts[r as usize].kind, CKind::Quot { kind } if kind as usize == k) {
                return Err(LoadError::Reject(format!(
                    "'{}' is a name of the quotient package and is declared as something else",
                    st.canon.display(bytes, q)
                )));
            }
        }
    }
    // the reader's list of proof blocks is `ld.blocks` again (decode_block
    // takes the block it decodes): one copy kept (Mathlib 24 MiB)
    st.blocks = Vec::new();
    Ok(Env {
        nat_op,
        bytes,
        st,
        main,
        side,
        lits: ld.lits,
        lvl,
        lvl_intern,
        ll_canon,
        lvl_map,
        consts: ld.consts,
        row_of_name,
        decl_rows: ld.decl_rows,
        decl_dup_params: decl_dup,
        blocks: ld.blocks,
        known,
        row_of_canon,
        rec_major,
        flagged,
        rec_rules_held,
    })
}
