use ahash::HashSet;
use ahash::HashSetExt;
use core::ops::RangeInclusive;
use once_cell::sync::Lazy;

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

pub const ECMASCRIPT_LINE_TERMINATORS: [char; 4] = ['\n', '\r', '\u{2028}', '\u{2029}'];

pub const ECMASCRIPT_WHITESPACE: [char; 21] = [
  '\x09', // Horizontal tab
  '\x0b', // Vertical tab
  '\x0c', // Form feed
  '\x20', // Space
  '\u{00A0}', // NO-BREAK SPACE
  '\u{1680}', // OGHAM SPACE MARK
  '\u{2000}', // EN QUAD
  '\u{2001}', // EM QUAD
  '\u{2002}', // EN SPACE
  '\u{2003}', // EM SPACE
  '\u{2004}', // THREE-PER-EM SPACE
  '\u{2005}', // FOUR-PER-EM SPACE
  '\u{2006}', // SIX-PER-EM SPACE
  '\u{2007}', // FIGURE SPACE
  '\u{2008}', // PUNCTUATION SPACE
  '\u{2009}', // THIN SPACE
  '\u{200A}', // HAIR SPACE
  '\u{202F}', // NARROW NO-BREAK SPACE
  '\u{205F}', // MEDIUM MATHEMATICAL SPACE
  '\u{3000}', // IDEOGRAPHIC SPACE
  '\u{FEFF}', // ZERO WIDTH NO-BREAK SPACE (BOM)
];

#[inline]
pub fn is_line_terminator(c: char) -> bool {
  ECMASCRIPT_LINE_TERMINATORS.contains(&c)
}
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
  filter.add_chars('0'..='7');
  filter
});

pub static WHITESPACE: Lazy<CharFilter> = Lazy::new(|| {
  let mut filter = CharFilter::new();
  for c in ECMASCRIPT_WHITESPACE {
    filter.add_char(c);
  }
  filter
});
