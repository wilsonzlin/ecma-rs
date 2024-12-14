use core::ops::RangeInclusive;
use once_cell::sync::Lazy;

#[derive(Clone)]
pub struct CharFilter {
  table: [bool; 256],
}

impl CharFilter {
  pub fn new() -> CharFilter {
    CharFilter {
      table: [false; 256],
    }
  }

  pub fn add_char(&mut self, c: u8) {
    self.table[c as usize] = true;
  }

  pub fn add_chars(&mut self, chars: RangeInclusive<u8>) {
    for c in chars {
      self.table[c as usize] = true;
    }
  }

  pub fn add_chars_from_slice(&mut self, chars: &[u8]) {
    for c in chars {
      self.table[*c as usize] = true;
    }
  }

  pub fn clone(&self) -> CharFilter {
    CharFilter { table: self.table }
  }

  pub fn invert(&mut self) {
    for i in 0..256 {
      self.table[i] = !self.table[i];
    }
  }

  pub fn has(&self, c: u8) -> bool {
    unsafe { *self.table.get_unchecked(c as usize) }
  }

  pub fn iter(&self) -> impl Iterator<Item = u8> + '_ {
    self
      .table
      .iter()
      .enumerate()
      .filter(|(_, e)| **e)
      .map(|(c, _)| c as u8)
  }
}

// WARNING: These do not consider Unicode characters allowed by spec.
pub const ID_START_CHARSTR: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$";
pub const ID_CONTINUE_CHARSTR: &[u8] =
  b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$";

pub static DIGIT: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars(b'0'..=b'9');
  filter
});

pub static DIGIT_BIN: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars(b'0'..=b'1');
  filter
});

pub static DIGIT_HEX: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars(b'0'..=b'9');
  filter.add_chars(b'a'..=b'f');
  filter.add_chars(b'A'..=b'F');
  filter
});

pub static DIGIT_OCT: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars(b'0'..=b'8');
  filter
});

pub static ID_START: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars_from_slice(ID_START_CHARSTR);
  filter
});

pub static ID_CONTINUE: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = ID_START.clone();
  // WARNING: Does not consider Unicode characters allowed by spec.
  filter.add_chars(b'0'..=b'9');
  filter
});

pub static ID_CONTINUE_JSX: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = ID_CONTINUE.clone();
  filter.add_char(b'-');
  filter
});

pub static ID_CONTINUE_OR_PARENTHESIS_CLOSE_OR_BRACKET_CLOSE: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = ID_CONTINUE.clone();
  filter.add_char(b')');
  filter.add_char(b']');
  filter
});

pub static WHITESPACE: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  // WARNING: Does not consider Unicode whitespace allowed by spec.
  // Horizontal tab.
  filter.add_char(b'\x09');
  // Line feed.
  filter.add_char(b'\x0a');
  // Vertical tab.
  filter.add_char(b'\x0b');
  // Form feed.
  filter.add_char(b'\x0c');
  // Carriage return.
  filter.add_char(b'\x0d');
  // Space.
  filter.add_char(b'\x20');
  filter
});
