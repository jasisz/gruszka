//! Environments cut to the entries a term reads (milestone 13). A cut
//! environment is a frame: a run of `eslots` where the entries the term
//! never reads are `HOLE`, ending at the last one it reads. Frames are
//! hash-consed by content, so two environments that agree on what a term
//! reads give one frame id for it.

// TODO(agent): nic. dla ciebie nic tu nie ma.
// dalej nie tu. jak tam budżet na tokeny?
pub const FREE: (u32, u32) = (0, u32::MAX);

#[derive(Default)]
pub struct FrameTab {
    /// open addressing with linear probing: (hash tag, environment id).
    /// Milestone 58: the tag is the hash's high word and an entry's home
    /// slot is the tag's top bits (`home`), so growing, rebuilding and
    /// deleting move entries by their tags, without reading their frames
    /// (a rehash read `eloc` and `eslots`: two cache misses per entry).
    tab: Vec<(u32, u32)>,
    n: usize,
    /// milestone 36: growths of `tab` (see `Spines::grows`)
    pub grows: u32,
}

#[inline(always)]
pub fn fmix(h: u64, x: u32) -> u64 {
    (h.rotate_left(5) ^ x as u64).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95)
}

#[inline(always)]
pub fn fhash(c: &[u32]) -> u64 {
    let mut h = 0x2545_f491_4f6c_dd1d_u64;
    for &x in c {
        h = fmix(h, x);
    }
    fmix(h, c.len() as u32)
}

/// The tag kept in an entry for hash `h` (milestone 58: its high word).
#[inline(always)]
fn tag_of(h: u64) -> u32 {
    (h >> 32) as u32
}

impl FrameTab {
    /// Milestone 58: the home slot of tag `t` in a table of `len` slots (a
    /// power of two, at most 2^32): the tag's top bits.
    #[inline(always)]
    fn home(t: u32, len: usize) -> usize {
        debug_assert!(len.is_power_of_two() && len >= 2 && len <= 1 << 32);
        ((t as u64) << 32 >> (64 - len.trailing_zeros())) as usize
    }
    /// Debug builds: entry `(t, x)` carries `x`'s hash.
    #[inline(always)]
    fn debug_tag(_t: u32, _x: u32, _hash_of: &impl Fn(u32) -> u64) {
        #[cfg(debug_assertions)]
        assert_eq!(_t, tag_of(_hash_of(_x)), "frame table: the tag of frame {_x}");
    }
    pub fn bytes(&self) -> usize {
        self.n * 16
    }
    /// milestone 37: bytes held (room included)
    pub fn held_bytes(&self) -> usize {
        self.tab.capacity() * 8
    }
    pub fn clear(&mut self, keep: usize) {
        let n = self.n;
        self.n = 0;
        let max = ((keep / 8).next_power_of_two() / 2).max(1 << 10);
        if self.tab.len() > max || (self.tab.len() > (1 << 16) && self.tab.len() > 16 * n) {
            let len = (n * 4).next_power_of_two().clamp(1 << 10, max);
            self.tab = vec![FREE; len];
        } else if n > 0 {
            self.tab.fill(FREE);
        }
    }

    /// The frame with content `c` (oldest entry first), or the slot where
    /// it goes. `run(e)` is environment e's content.
    #[inline]
    pub fn find<'a>(&self, h: u64, c: &[u32], run: impl Fn(u32) -> &'a [u32]) -> Result<u32, usize> {
        if self.tab.is_empty() {
            return Err(usize::MAX);
        }
        let mask = self.tab.len() - 1;
        let tag = tag_of(h);
        let mut i = Self::home(tag, self.tab.len());
        loop {
            let (t, e) = self.tab[i];
            if e == u32::MAX {
                return Err(i);
            }
            if t == tag && run(e) == c {
                return Ok(e);
            }
            i = (i + 1) & mask;
        }
    }

    /// Records frame `e` (hash `h`) at `slot` from `find`; grows the table
    /// first when it is half full (old entries move by their tags; `hash_of`
    /// checks them in debug builds). The slot taken, None after a growth
    /// (milestone 36 logs it).
    pub fn insert(&mut self, h: u64, slot: usize, e: u32, hash_of: impl Fn(u32) -> u64) -> Option<usize> {
        if slot == usize::MAX || (self.n + 1) * 2 > self.tab.len() {
            self.grows = self.grows.wrapping_add(1);
            let len = (self.tab.len() * 2).max(1 << 10);
            let old = std::mem::replace(&mut self.tab, vec![FREE; len]);
            self.n = 0;
            for (t, x) in old {
                if x != u32::MAX {
                    Self::debug_tag(t, x, &hash_of);
                    self.place(t, x);
                }
            }
            self.place(tag_of(h), e);
            return None;
        }
        self.tab[slot] = (tag_of(h), e);
        self.n += 1;
        Some(slot)
    }

    /// Milestone 36 (checks): the frames in the table.
    pub fn entries(&self) -> impl Iterator<Item = u32> + '_ {
        self.tab.iter().filter(|e| e.1 != u32::MAX).map(|e| e.1)
    }
    /// Milestone 36: frees a slot `insert` took (in reverse order, no
    /// growth in between: see `Spines::unadd`).
    pub fn unadd(&mut self, slot: usize) {
        debug_assert!(self.tab[slot].1 != u32::MAX);
        self.tab[slot] = FREE;
        self.n -= 1;
    }
    /// Milestone 37: takes frame `e` (hash `h`) out of the table, if there
    /// (backward-shift deletion, as `Spines::remove_value`; bumps `grows`).
    pub fn remove(&mut self, h: u64, e: u32, hash_of: impl Fn(u32) -> u64) {
        if self.tab.is_empty() {
            return;
        }
        let mask = self.tab.len() - 1;
        let mut i = Self::home(tag_of(h), self.tab.len());
        loop {
            let x = self.tab[i].1;
            if x == u32::MAX {
                return;
            }
            if x == e {
                break;
            }
            i = (i + 1) & mask;
        }
        self.grows = self.grows.wrapping_add(1);
        self.n -= 1;
        let mut k = i;
        loop {
            k = (k + 1) & mask;
            let (t, x) = self.tab[k];
            if x == u32::MAX {
                self.tab[i] = FREE;
                return;
            }
            Self::debug_tag(t, x, &hash_of);
            let home = Self::home(t, self.tab.len());
            if (k.wrapping_sub(home) & mask) >= (k.wrapping_sub(i) & mask) {
                self.tab[i] = (t, x);
                i = k;
            }
        }
    }
    /// Milestone 36: the table with only the frames below `em`.
    pub fn rebuild_below(&mut self, em: u32, hash_of: impl Fn(u32) -> u64) {
        let old = std::mem::take(&mut self.tab);
        self.tab = vec![FREE; old.len().max(1 << 10)];
        self.n = 0;
        for (t, x) in old {
            if x != u32::MAX && x < em {
                Self::debug_tag(t, x, &hash_of);
                self.place(t, x);
            }
        }
    }

    /// Milestone 58: by tag `t` (its home slot is the tag's top bits).
    fn place(&mut self, t: u32, e: u32) {
        let mask = self.tab.len() - 1;
        let mut i = Self::home(t, self.tab.len());
        while self.tab[i].1 != u32::MAX {
            i = (i + 1) & mask;
        }
        self.tab[i] = (t, e);
        self.n += 1;
    }
}
