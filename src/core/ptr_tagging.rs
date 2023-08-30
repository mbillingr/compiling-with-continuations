pub fn make_tag(x: usize) -> usize {
    x * 2 + 1
}

pub fn untag(x: usize) -> usize {
    (x - 1) / 2
}

pub fn maybe_tag(x: usize) -> bool {
    (x & 0x1) == 1
}

pub fn maybe_pointer(x: usize) -> bool {
    (x & 0x1) == 0
}
