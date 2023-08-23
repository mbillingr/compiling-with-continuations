use crate::core::reference::Ref;

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Answer(usize);

impl Answer {
    pub fn from_int(i: i64) -> Self {
        unsafe { Answer(std::mem::transmute(i)) }
    }

    pub fn from_float(f: f64) -> Self {
        unsafe { Answer(std::mem::transmute(f)) }
    }

    pub fn from_str(s: Ref<String>) -> Self {
        unsafe { Answer(std::mem::transmute(s)) }
    }

    pub fn from_ref<T>(r: Ref<T>) -> Self {
        unsafe { Answer(std::mem::transmute(r.as_ptr())) }
    }

    pub fn tag(t: usize) -> Self {
        Answer(t * 2 + 1)
    }

    pub fn tuple(fields: Vec<Answer>) -> Self {
        let obj = Box::leak(fields.into_boxed_slice());
        let fst = &obj[0] as *const _;
        unsafe { Answer(std::mem::transmute(fst)) }
    }

    pub fn maybe_tag(&self) -> bool {
        (self.0 & 0x1) == 1
    }

    pub fn maybe_pointer(&self) -> bool {
        (self.0 & 0x1) == 0
    }

    pub fn as_int(&self) -> i64 {
        unsafe { std::mem::transmute(self.0) }
    }

    pub fn as_float(&self) -> f64 {
        unsafe { std::mem::transmute(self.0) }
    }

    pub fn as_str(&self) -> &String {
        unsafe { std::mem::transmute(self.0) }
    }

    pub fn as_tag(&self) -> usize {
        self.0 / 2
    }

    pub unsafe fn as_ref<T>(self) -> &'static T {
        let ptr: *const T = std::mem::transmute(self.0);
        &*ptr
    }

    pub unsafe fn get_item(self, idx: isize) -> Answer {
        let fst: *const Answer = std::mem::transmute(self.0);
        *fst.offset(idx)
    }
}
