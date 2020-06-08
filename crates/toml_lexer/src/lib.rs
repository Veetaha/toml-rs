// TODO: uncomment:
// #![deny(missing_docs)]
#![warn(rust_2018_idioms)]
// Makes rustc abort compilation if there are any unsafe blocks in the crate.
// Presence of this annotation is picked up by tools such as cargo-geiger
// and lets them ensure that there is indeed no unsafe code as opposed to
// something they couldn't detect (e.g. unsafe added via macro expansion, etc).
#![forbid(unsafe_code)]

mod cursor;
mod unescape;

// TODO: gate by a feature flag
pub mod error_reluctant_lexer;
pub mod error_resilient_lexer;

pub use unescape::*;

/// A span, designating a range of bytes where a token is located.
#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub struct Span {
    /// The start of the range.
    pub start: usize,
    /// The end of the range (exclusive).
    pub end: usize,
}

impl From<Span> for (usize, usize) {
    fn from(Span { start, end }: Span) -> (usize, usize) {
        (start, end)
    }
}

/// Kind of toml string literal
#[derive(Eq, PartialEq, Debug, Clone, Copy)]
#[repr(u8)]
pub enum StringKind {
    /// Single-quoted strings that don't support escape sequences.
    Literal = b'\'',
    /// Double-quoted strings that support escape sequences.
    Basic = b'"',
}

impl StringKind {
    pub const fn to_quote(self) -> char {
        self as u8 as char
    }
    pub fn from_quote(quote: char) -> Option<StringKind> {
        match quote {
            '\'' => Some(StringKind::Literal),
            '"' => Some(StringKind::Basic),
            _ => None,
        }
    }
}
