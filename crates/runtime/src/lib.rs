//! Runtime support for peepmatic.
//!
//! This crate contains everything required to use a peepmatic-generated
//! peephole optimizer.

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]

pub mod linear;
pub mod paths;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
