//! String interning for symbols

pub use lasso::Spur as Symbol;
use lasso::ThreadedRodeo;
use std::sync::{Arc, Mutex};

/// Thread-safe string interner
#[derive(Clone)]
pub struct Interner {
    inner: Arc<Mutex<ThreadedRodeo>>,
}

impl Interner {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(ThreadedRodeo::new())),
        }
    }

    pub fn intern(&self, s: &str) -> Symbol {
        self.inner.lock().unwrap().get_or_intern(s)
    }

    pub fn resolve(&self, sym: &Symbol) -> String {
        self.inner.lock().unwrap().resolve(sym).to_string()
    }

    pub fn try_resolve(&self, sym: &Symbol) -> Option<String> {
        self.inner
            .lock()
            .unwrap()
            .try_resolve(sym)
            .map(|s| s.to_string())
    }
}

impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}
