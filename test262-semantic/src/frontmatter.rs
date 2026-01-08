use anyhow::{anyhow, bail, Context, Result};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct Frontmatter {
  #[serde(default, deserialize_with = "string_or_seq")]
  pub includes: Vec<String>,
  #[serde(default, deserialize_with = "string_or_seq")]
  pub flags: Vec<String>,
  #[serde(default, deserialize_with = "string_or_seq")]
  pub features: Vec<String>,
  #[serde(default)]
  pub negative: Option<Negative>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Negative {
  pub phase: String,
  #[serde(rename = "type")]
  pub typ: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ParsedTestSource {
  pub frontmatter: Option<Frontmatter>,
  pub body: String,
}

pub fn parse_test_source(source: &str) -> Result<ParsedTestSource> {
  let source = source.strip_prefix('\u{feff}').unwrap_or(source);
  let Some(start) = source.find("/*---") else {
    return Ok(ParsedTestSource {
      frontmatter: None,
      body: source.to_string(),
    });
  };

  if !source[..start].trim().is_empty() {
    return Ok(ParsedTestSource {
      frontmatter: None,
      body: source.to_string(),
    });
  }

  let yaml_start = start + "/*---".len();
  let Some(end_rel) = source[yaml_start..].find("---*/") else {
    bail!("frontmatter begins with `/*---` but is missing terminating `---*/`");
  };
  let yaml_end = yaml_start + end_rel;
  let yaml = &source[yaml_start..yaml_end];
  let after = yaml_end + "---*/".len();

  let frontmatter: Frontmatter =
    serde_yaml::from_str(yaml).context("deserialize test262 YAML frontmatter")?;

  Ok(ParsedTestSource {
    frontmatter: Some(frontmatter),
    body: source
      .get(after..)
      .ok_or_else(|| anyhow!("frontmatter terminator offset out of bounds"))?
      .to_string(),
  })
}

fn string_or_seq<'de, D>(deserializer: D) -> std::result::Result<Vec<String>, D::Error>
where
  D: serde::de::Deserializer<'de>,
{
  struct Visitor;

  impl<'de> serde::de::Visitor<'de> for Visitor {
    type Value = Vec<String>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
      formatter.write_str("string or sequence of strings")
    }

    fn visit_str<E>(self, v: &str) -> std::result::Result<Self::Value, E>
    where
      E: serde::de::Error,
    {
      Ok(vec![v.to_string()])
    }

    fn visit_string<E>(self, v: String) -> std::result::Result<Self::Value, E>
    where
      E: serde::de::Error,
    {
      Ok(vec![v])
    }

    fn visit_seq<A>(self, mut seq: A) -> std::result::Result<Self::Value, A::Error>
    where
      A: serde::de::SeqAccess<'de>,
    {
      let mut out = Vec::new();
      while let Some(value) = seq.next_element::<String>()? {
        out.push(value);
      }
      Ok(out)
    }
  }

  deserializer.deserialize_any(Visitor)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parses_yaml_frontmatter_and_strips_body() {
    let src = r#"/*---
includes: [assert.js, helper.js]
flags: [onlyStrict]
features: [BigInt]
negative:
  phase: runtime
  type: TypeError
---*/
throw new TypeError();
"#;

    let parsed = parse_test_source(src).unwrap();
    let fm = parsed.frontmatter.unwrap();
    assert_eq!(fm.includes, vec!["assert.js", "helper.js"]);
    assert_eq!(fm.flags, vec!["onlyStrict"]);
    assert_eq!(fm.features, vec!["BigInt"]);
    let negative = fm.negative.unwrap();
    assert_eq!(negative.phase, "runtime");
    assert_eq!(negative.typ, "TypeError");
    assert!(parsed.body.contains("throw new TypeError()"));
    assert!(!parsed.body.contains("includes:"));
  }

  #[test]
  fn missing_frontmatter_is_ok() {
    let src = "let x = 1;";
    let parsed = parse_test_source(src).unwrap();
    assert!(parsed.frontmatter.is_none());
    assert_eq!(parsed.body, src);
  }
}

