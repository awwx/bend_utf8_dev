#![no_std]

// ---- Safe core: this part is translated by Charon/Aeneas. ----

pub fn is_surrogate_code_point(cp: u32) -> bool {
    cp >= 0xD800 && cp <= 0xDFFF
}

/// Number of bytes >= 0x80.
pub fn count_non_ascii(bytes: &[u8]) -> u32 {
    let mut n: u32 = 0;
    let mut i: usize = 0;
    while i < bytes.len() {
        if bytes[i] >= 0x80 {
            n += 1;
        }
        i += 1;
    }
    n
}

/// Variant with early `return`: index of first byte >= 0x80, or len if none.
pub fn first_non_ascii_return(bytes: &[u8]) -> usize {
    let mut i: usize = 0;
    while i < bytes.len() {
        if bytes[i] >= 0x80 {
            return i;
        }
        i += 1;
    }
    bytes.len()
}

/// Variant with `break` and `continue`.
pub fn first_non_ascii_break(bytes: &[u8]) -> usize {
    let mut i: usize = 0;
    loop {
        if i >= bytes.len() {
            break;
        }
        if bytes[i] < 0x80 {
            i += 1;
            continue;
        }
        break;
    }
    i
}

// ---- Unsafe export shim: excluded from translation (charon --exclude crate::shim). ----

mod shim {
    use super::*;

    #[no_mangle]
    pub extern "C" fn spike_is_surrogate_code_point(cp: u32) -> u32 {
        is_surrogate_code_point(cp) as u32
    }

    /// Safety: caller guarantees `ptr` is valid for `len` bytes.
    #[no_mangle]
    pub unsafe extern "C" fn spike_count_non_ascii(ptr: *const u8, len: usize) -> u32 {
        let s = core::slice::from_raw_parts(ptr, len);
        count_non_ascii(s)
    }

    #[panic_handler]
    fn panic(_: &core::panic::PanicInfo) -> ! {
        loop {}
    }
}
