use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug, Clone, Default)]
pub struct Clicker(Rc<AtomicUsize>);

impl Clicker {
    pub fn new() -> Self {
        Clicker(Rc::new(AtomicUsize::new(0)))
    }

    pub fn reset(&self) {
        self.0.store(0, Ordering::SeqCst);
    }

    pub fn click(&self) {
        self.0.fetch_add(1, Ordering::Relaxed);
    }

    pub fn count(&self) -> usize {
        self.0.load(Ordering::Relaxed)
    }
}
