// Verus spike: verified core + thin extern "C" shim, compiled to wasm32.
#![no_std]
use vstd::prelude::*;

verus! {

// ---------- (a) surrogate code points (LAWS.bend lines 117-131) ----------

/// Spec: surrogates are U+D800..U+DFFF.
pub open spec fn is_surrogate_spec(cp: int) -> bool {
    0xD800 <= cp && cp <= 0xDFFF
}

pub fn is_surrogate_impl(cp: u32) -> (r: bool)
    ensures r == is_surrogate_spec(cp as int),
{
    cp >= 0xD800 && cp <= 0xDFFF
}

proof fn is_surrogate_examples()
    ensures
        !is_surrogate_spec(0x0000),
        !is_surrogate_spec(0xD7FF),
        is_surrogate_spec(0xD800),
        is_surrogate_spec(0xDC00),
        is_surrogate_spec(0xDFFF),
        !is_surrogate_spec(0xE000),
{
}

// ---------- (b) count_non_ascii ----------

/// Spec: number of bytes >= 0x80, by recursion on the sequence.
pub open spec fn count_spec(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_spec(s.drop_last()) + (if s.last() >= 0x80 { 1nat } else { 0nat })
    }
}

pub fn count_non_ascii_core(buf: &[u8]) -> (r: u32)
    requires buf.len() <= u32::MAX,
    ensures r == count_spec(buf@),
{
    let mut i: usize = 0;
    let mut n: u32 = 0;
    while i < buf.len()
        invariant
            i <= buf.len(),
            buf.len() <= u32::MAX,
            n == count_spec(buf@.take(i as int)),
            n <= i,
        decreases buf.len() - i,
    {
        assert(buf@.take((i + 1) as int).drop_last() =~= buf@.take(i as int));
        if buf[i] >= 0x80 {
            n = n + 1;
        }
        i = i + 1;
    }
    assert(buf@.take(buf.len() as int) =~= buf@);
    n
}

// ---------- existential / uniqueness style lemma ----------

/// Relational spec: c is the number of elements >= 0x80 (via Seq::filter).
pub open spec fn count_rel(s: Seq<u8>, c: nat) -> bool {
    s.filter(|b: u8| b >= 0x80).len() == c
}

proof fn count_spec_is_filter_len(s: Seq<u8>)
    ensures count_spec(s) == s.filter(|b: u8| b >= 0x80).len(),
    decreases s.len(),
{
    if s.len() > 0 {
        count_spec_is_filter_len(s.drop_last());
        reveal_with_fuel(Seq::filter, 2);
        let p = |b: u8| b >= 0x80;
        assert(s.drop_last().push(s.last()) =~= s);
        s.drop_last().lemma_filter_push(s.last(), p) ;
    }
}

/// "There exists a count c such that c counts the non-ASCII bytes, and it is unique."
proof fn count_exists_unique(s: Seq<u8>)
    ensures
        exists|c: nat| #[trigger] count_rel(s, c) && forall|d: nat| count_rel(s, d) ==> d == c,
{
    count_spec_is_filter_len(s);
    let c = count_spec(s);
    assert(count_rel(s, c));
}

} // verus!

// ---------- export shim (outside verification) ----------

#[no_mangle]
pub extern "C" fn is_surrogate_code_point(cp: u32) -> u32 {
    is_surrogate_impl(cp) as u32
}

/// Unverified shim: turns (ptr,len) into a slice and calls the verified core.
#[no_mangle]
pub extern "C" fn count_non_ascii(ptr: *const u8, len: usize) -> u32 {
    // usize is 32 bits on wasm32 so len <= u32::MAX holds (checked below for other targets).
    if len > u32::MAX as usize { return 0; }
    let buf = unsafe { core::slice::from_raw_parts(ptr, len) };
    count_non_ascii_core(buf)
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
