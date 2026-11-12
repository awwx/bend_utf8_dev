#![no_std]
//! Streaming UTF-8 decoder.  The safe core (everything outside `mod shim`)
//! is translated to Lean by Charon + Aeneas and proved; it mirrors the
//! reference decoder `Utf8Pure.step` of candidates/pure-lean byte by byte.
//!
//! State: the pending bytes (0..3 bytes of a valid-sequence prefix),
//! packed into a u32 as  n + 256*b0 + 65536*b1 + 16777216*b2  (unused bytes 0).
//! Output: code points (u32), at most 2 per input byte.

// ---- Byte classes (Unicode Table 3-7), as in Utf8Ref.lean ----

pub fn is_cont(b: u8) -> bool { 0x80 <= b && b <= 0xBF }
pub fn is_lead1(b: u8) -> bool { b <= 0x7F }
pub fn is_lead2(b: u8) -> bool { 0xC2 <= b && b <= 0xDF }
pub fn is_lead3(b: u8) -> bool { 0xE0 <= b && b <= 0xEF }
pub fn is_lead4(b: u8) -> bool { 0xF0 <= b && b <= 0xF4 }

/// Allowed second byte after lead byte `b1`.
pub fn second_ok(b1: u8, b2: u8) -> bool {
    if b1 == 0xE0 { 0xA0 <= b2 && b2 <= 0xBF }
    else if b1 == 0xED { 0x80 <= b2 && b2 <= 0x9F }
    else if b1 == 0xF0 { 0x90 <= b2 && b2 <= 0xBF }
    else if b1 == 0xF4 { 0x80 <= b2 && b2 <= 0x8F }
    else { 0x80 <= b2 && b2 <= 0xBF }
}

#[derive(Clone, Copy)]
pub struct Pend { pub n: u8, pub b0: u8, pub b1: u8, pub b2: u8 }

/// Result of one step: new pending bytes and 0..2 emitted code points.
#[derive(Clone, Copy)]
pub struct Out { pub p: Pend, pub n: u8, pub c0: u32, pub c1: u32 }

const EMPTY: Pend = Pend { n: 0, b0: 0, b1: 0, b2: 0 };
pub const REPLACEMENT: u32 = 0xFFFD;

/// `isVSP [b]` for a non-ASCII byte: lead byte of a 2..4-byte sequence.
pub fn is_lead_multi(b: u8) -> bool { is_lead2(b) || is_lead3(b) || is_lead4(b) }

// Whole valid sequence / valid sequence prefix of 2, 3 and 4 bytes
// (`Utf8Pure.isVS`, `Utf8Pure.isVSP`).
pub fn vs2(b0: u8, b1: u8) -> bool { is_lead2(b0) && second_ok(b0, b1) }
pub fn vsp2(b0: u8, b1: u8) -> bool { is_lead_multi(b0) && second_ok(b0, b1) }
pub fn vs3(b0: u8, b1: u8, b2: u8) -> bool { is_lead3(b0) && second_ok(b0, b1) && is_cont(b2) }
pub fn vsp3(b0: u8, b1: u8, b2: u8) -> bool {
    (is_lead3(b0) || is_lead4(b0)) && second_ok(b0, b1) && is_cont(b2)
}
pub fn vs4(b0: u8, b1: u8, b2: u8, b3: u8) -> bool {
    is_lead4(b0) && second_ok(b0, b1) && is_cont(b2) && is_cont(b3)
}

// Code point of a valid sequence (`Utf8Pure.cpOf`, in its `%`/`*` form).
pub fn cp2(b0: u8, b1: u8) -> u32 { (b0 as u32 % 32) * 64 + b1 as u32 % 64 }
pub fn cp3(b0: u8, b1: u8, b2: u8) -> u32 {
    (b0 as u32 % 16) * 4096 + (b1 as u32 % 64) * 64 + b2 as u32 % 64
}
pub fn cp4(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32 % 8) * 262144 + (b1 as u32 % 64) * 4096 + (b2 as u32 % 64) * 64 + b3 as u32 % 64
}

fn emit(c: u32) -> Out { Out { p: EMPTY, n: 1, c0: c, c1: 0 } }
fn hold(p: Pend) -> Out { Out { p, n: 0, c0: 0, c1: 0 } }

/// One byte with no pending bytes (`Utf8Pure.stepFresh`).
pub fn step_fresh(b: u8) -> Out {
    if is_lead1(b) {
        emit(b as u32)
    } else if is_lead_multi(b) {
        hold(Pend { n: 1, b0: b, b1: 0, b2: 0 })
    } else {
        emit(REPLACEMENT)
    }
}

/// Pending bytes were not completable by `b`: U+FFFD for them, then `b` afresh.
pub fn bad_pending(b: u8) -> Out {
    let f = step_fresh(b);
    Out { p: f.p, n: f.n + 1, c0: REPLACEMENT, c1: f.c0 }
}

/// One byte `b` with pending bytes `p` (`Utf8Pure.step`).
pub fn step(p: Pend, b: u8) -> Out {
    if p.n == 0 {
        step_fresh(b)
    } else if p.n == 1 {
        if vs2(p.b0, b) {
            emit(cp2(p.b0, b))
        } else if vsp2(p.b0, b) {
            hold(Pend { n: 2, b0: p.b0, b1: b, b2: 0 })
        } else {
            bad_pending(b)
        }
    } else if p.n == 2 {
        if vs3(p.b0, p.b1, b) {
            emit(cp3(p.b0, p.b1, b))
        } else if vsp3(p.b0, p.b1, b) {
            hold(Pend { n: 3, b0: p.b0, b1: p.b1, b2: b })
        } else {
            bad_pending(b)
        }
    } else if vs4(p.b0, p.b1, p.b2, b) {
        // (for 4 bytes, isVSP = isVS, so there is no "hold" case)
        emit(cp4(p.b0, p.b1, p.b2, b))
    } else {
        bad_pending(b)
    }
}

pub fn unpack(s: u32) -> Pend {
    Pend {
        n: (s % 256) as u8,
        b0: (s / 256 % 256) as u8,
        b1: (s / 65536 % 256) as u8,
        b2: (s / 16777216) as u8,
    }
}

pub fn pack(p: Pend) -> u32 {
    p.n as u32 + (p.b0 as u32) * 256 + (p.b1 as u32) * 65536 + (p.b2 as u32) * 16777216
}

pub fn decode_start_state() -> u32 { 0 }

/// Writes the `o.n` (0..2) code points of `o` to `out[k..]`; returns the new count.
fn write_out(out: &mut [u32], k: usize, o: Out) -> usize {
    match o.n {
        0 => k,
        1 => {
            out[k] = o.c0;
            k + 1
        }
        _ => {
            out[k] = o.c0;
            out[k + 1] = o.c1;
            k + 2
        }
    }
}

/// Decode `input` from `state`; writes the code points to the front of
/// `out` (needs `out.len() >= 2 * input.len()`), returns the new state and
/// the number of code points written.
pub fn decode_buffer(state: u32, input: &[u8], out: &mut [u32]) -> (u32, usize) {
    let mut p = unpack(state);
    let mut i: usize = 0;
    let mut k: usize = 0;
    while i < input.len() {
        let o = step(p, input[i]);
        k = write_out(out, k, o);
        p = o.p;
        i += 1;
    }
    (pack(p), k)
}

/// End of input: writes U+FFFD to `out[0]` if bytes are pending
/// (needs `out.len() >= 1`), returns the number of code points written.
pub fn decode_done(state: u32, out: &mut [u32]) -> usize {
    if state % 256 == 0 {
        0
    } else {
        out[0] = REPLACEMENT;
        1
    }
}

// ---- Unsafe export shim: excluded from translation (charon --exclude crate::shim). ----
// Logic: build slices from (ptr, len) and call the core; decode_buffer stores the new
// state at `*state_out`.  Nothing else.
mod shim {
    #[no_mangle]
    pub extern "C" fn utf8_start() -> u32 {
        super::decode_start_state()
    }

    /// Safety: (in_ptr, in_len) and (out_ptr, out_len) are valid, disjoint, and
    /// `state_out` is a valid aligned u32 outside both.
    #[no_mangle]
    pub unsafe extern "C" fn utf8_decode_buffer(
        state: u32, in_ptr: *const u8, in_len: usize, out_ptr: *mut u32, out_len: usize,
        state_out: *mut u32,
    ) -> usize {
        let input = core::slice::from_raw_parts(in_ptr, in_len);
        let out = core::slice::from_raw_parts_mut(out_ptr, out_len);
        let (s, k) = super::decode_buffer(state, input, out);
        *state_out = s;
        k
    }

    /// Safety: (out_ptr, out_len) is valid.
    #[no_mangle]
    pub unsafe extern "C" fn utf8_decode_done(state: u32, out_ptr: *mut u32, out_len: usize) -> usize {
        let out = core::slice::from_raw_parts_mut(out_ptr, out_len);
        super::decode_done(state, out)
    }

    /// Trap (Wasm `unreachable`) on a panic, e.g. an out-of-contract call that fails a
    /// bounds check.  (On other targets, used only for Charon's host translation, loop.)
    #[panic_handler]
    fn panic(_: &core::panic::PanicInfo) -> ! {
        #[cfg(target_arch = "wasm32")]
        core::arch::wasm32::unreachable();
        #[cfg(not(target_arch = "wasm32"))]
        loop {}
    }
}
