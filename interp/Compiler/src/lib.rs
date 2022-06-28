use std::{ffi::CStr, os::raw::c_char};

#[no_mangle]
pub extern "C" fn compile(c_string: *const c_char) {
    let s = unsafe { CStr::from_ptr(c_string) }
        .to_string_lossy()
        .into_owned();
    println!("length: {}", s.chars().count())
}
