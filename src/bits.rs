use std::mem::size_of;

pub fn next_one(blocks: &[u32], offset: usize) -> Option<usize> {
    const BITS: usize = size_of::<u32>() * 8;

    let mut mask = !((1u32 << (offset % BITS)) - 1);
    let mut offset = offset / BITS * BITS;

    for block in blocks[offset / BITS..].iter() {
        let masked = block & mask;

        if masked != 0 {
            return Some(offset + masked.trailing_zeros() as usize);
        }

        offset += BITS;
        mask = !0;
    }

    None
}
