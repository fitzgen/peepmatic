//! Fuzz testing utilities related to AST pattern matching.

use std::path::Path;
use std::str;

/// Attempt to interpret the given bytes as UTF-8 and then compile them as if
/// they were source text of our DSL.
pub fn compile(data: &[u8]) {
    let source = match str::from_utf8(data) {
        Err(_) => return,
        Ok(s) => s,
    };

    let _ = peepmatic::compile_str(source, Path::new("fuzz"));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_compile() {
        crate::check(|s: String| compile(s.as_bytes()));
    }
}
