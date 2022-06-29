mod error;
mod pos;
mod range;
mod state;
mod token;

use self::{error::LexError, pos::Pos, state::State, token::Token};
use std::{ffi::CStr, os::raw::c_char};

struct Lex<I>
where
    I: Iterator<Item = (Pos, char)>,
{
    iter: I,
    state: State,
}

impl<I> Iterator for Lex<I>
where
    I: Iterator<Item = (Pos, char)>,
{
    type Item = Vec<Result<Token, LexError>>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!();
    }
}

#[no_mangle]
pub extern "C" fn compile(c_string: *const c_char) {
    let s = unsafe { CStr::from_ptr(c_string) }
        .to_string_lossy()
        .into_owned();
    println!("length: {}", s.chars().count())
}
