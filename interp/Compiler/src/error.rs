use super::range::Range;

pub enum LexError {
    InvalidKeyword(Range, String),
}
