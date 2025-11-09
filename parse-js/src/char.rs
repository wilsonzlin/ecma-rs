use core::ops::RangeInclusive;
use once_cell::sync::Lazy;
use ahash::HashSet;
use ahash::HashSetExt;

#[derive(Clone)]
pub struct CharFilter {
  chars: HashSet<char>,
  inverted: bool,
}

impl CharFilter {
  pub fn new() -> CharFilter {
    CharFilter {
      chars: HashSet::new(),
      inverted: false,
    }
  }

  pub fn add_char(&mut self, c: char) {
    self.chars.insert(c);
  }

  pub fn add_chars(&mut self, chars: RangeInclusive<char>) {
    for c in chars {
      self.chars.insert(c);
    }
  }

  pub fn add_chars_from_slice(&mut self, chars: &str) {
    for c in chars.chars() {
      self.chars.insert(c);
    }
  }

  pub fn clone(&self) -> CharFilter {
    CharFilter {
      chars: self.chars.clone(),
      inverted: self.inverted,
    }
  }

  pub fn invert(&mut self) {
    self.inverted = !self.inverted;
  }

  pub fn has(&self, c: char) -> bool {
    let contains = self.chars.contains(&c);
    if self.inverted {
      !contains
    } else {
      contains
    }
  }

  pub fn iter(&self) -> impl Iterator<Item = char> + '_ {
    self.chars.iter().copied()
  }
}

// WARNING: These do not consider Unicode characters allowed by spec.
pub const ID_START_CHARSTR: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$";
pub const ID_CONTINUE_CHARSTR: &str =
  "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$";

pub static DIGIT: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars('0'..='9');
  filter
});

pub static DIGIT_BIN: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars('0'..='1');
  filter
});

pub static DIGIT_HEX: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars('0'..='9');
  filter.add_chars('a'..='f');
  filter.add_chars('A'..='F');
  filter
});

pub static DIGIT_OCT: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  filter.add_chars('0'..='8');
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
  filter.add_chars('0'..='9');
  filter
});

pub static ID_CONTINUE_JSX: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = ID_CONTINUE.clone();
  filter.add_char('-');
  filter
});

pub static ID_CONTINUE_OR_PARENTHESIS_CLOSE_OR_BRACKET_CLOSE: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = ID_CONTINUE.clone();
  filter.add_char(')');
  filter.add_char(']');
  filter
});

pub static WHITESPACE: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  // Horizontal tab.
  filter.add_char('\x09');
  // Line feed.
  filter.add_char('\x0a');
  // Vertical tab.
  filter.add_char('\x0b');
  // Form feed.
  filter.add_char('\x0c');
  // Carriage return.
  filter.add_char('\x0d');
  // Space.
  filter.add_char('\x20');
  // Unicode whitespace characters
  filter.add_char('\u{00A0}'); // NO-BREAK SPACE
  filter.add_char('\u{1680}'); // OGHAM SPACE MARK
  filter.add_char('\u{2000}'); // EN QUAD
  filter.add_char('\u{2001}'); // EM QUAD
  filter.add_char('\u{2002}'); // EN SPACE
  filter.add_char('\u{2003}'); // EM SPACE
  filter.add_char('\u{2004}'); // THREE-PER-EM SPACE
  filter.add_char('\u{2005}'); // FOUR-PER-EM SPACE
  filter.add_char('\u{2006}'); // SIX-PER-EM SPACE
  filter.add_char('\u{2007}'); // FIGURE SPACE
  filter.add_char('\u{2008}'); // PUNCTUATION SPACE
  filter.add_char('\u{2009}'); // THIN SPACE
  filter.add_char('\u{200A}'); // HAIR SPACE
  filter.add_char('\u{202F}'); // NARROW NO-BREAK SPACE
  filter.add_char('\u{205F}'); // MEDIUM MATHEMATICAL SPACE
  filter.add_char('\u{3000}'); // IDEOGRAPHIC SPACE
  filter.add_char('\u{FEFF}'); // ZERO WIDTH NO-BREAK SPACE (BOM)
  filter
});
