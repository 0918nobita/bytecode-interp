pub struct Pos {
    line: u32,
    character: u32,
}

impl Pos {
    pub fn next_char(&mut self) {
        self.character += 1;
    }

    pub fn next_line(&mut self) {
        self.line += 1;
        self.character = 0;
    }
}
