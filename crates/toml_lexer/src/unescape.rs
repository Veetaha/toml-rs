//! Utilities for validating string literals and turning them into
//! values they represent.

use crate::{cursor::Cursor, Span, StringKind};
use std::{borrow::Cow, char, iter, str::CharIndices};

/// Represents the low-level subtokens of the string literal token contents.
/// The tokens represent both welformed strings and malformed string literals.
/// See the the docs on the variants for more details.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum StringSubtoken {
    /// Leading newline character in multiline strings (it should be skipped).
    LeadingNewline,
    /// Unicode escape sequence, represents a unicode scalar value of a character
    /// or the error of decoding one.
    UnicodeEscape {
        /// Type of the unicode escape (it is determined by `\u` or `\U` prefix)
        kind: HexLen,
        /// The result of decoding the unicode escape sequnce.
        unescaped: UnicodeEscape,
    },
    /// Shorthand escape sequence for ad-hoc characters.
    /// These are one of: `\, \b, \f, \n, \r, \t, \", \'`,
    /// It will be `Ok(unescaped_char)` if the character after the slash does belong
    /// to the aformentioned set of shorthand escapes, otherwise the character
    /// that doesn't belong to that set will be stored as `Err(unexpected_char)`
    ShorthandEscape(Result<char, char>),
    /// Exactly the character itself that doesn't need any escaping and can be used as is.
    Char(char),
    /// Unescaped character that was expected to be escaped (e.g. raw control chars like \0 \b)
    /// or the character that cannot appear in this kind of string at all (e.g. ' or \n in literal line strings)
    BannedChar(char),
    /// Represents "line ending backslash" and the following trimmed whitespaces characters.
    /// If there was no newline after the slash-whitespace chars `includes_newline` will be `false`.
    TrimmedWhitespace { includes_newline: bool },
    /// Slash character exactly at the end of the input (appears only in unterminated strings).
    TrailingSlash,
    /// Leading quotes, this the required first subtoken of the string literal
    LeadingQuotes(Quotes),
    /// Optional trailing quotes (when not present the string literal is unterminated),
    TrailingQuotes,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Quotes {
    pub len: QuotesLen,
    pub kind: StringKind,
}

/// Represents the length of the quotes
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[repr(u8)]
pub enum QuotesLen {
    /// `'` or `"`
    X1 = 1,
    /// `'''` or `"""`
    X3 = 3,
}

impl From<QuotesLen> for usize {
    fn from(len: QuotesLen) -> usize {
        len as usize
    }
}

/// Result of tokenizing the unicode escape sequence of forms `\uXXXX` and `\UXXXXXXXX`
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum UnicodeEscape {
    /// Successfully parsed unicode character itself.
    Valid(char),
    /// Contains the actual amount of digits parsed.
    NotEnoughDigits(u32),
    /// Contains the scalar value itself (it cannot be turned into a valid
    /// unicode `char`, i.e. into Rust `char` itself since Rust `char` **must** be
    /// a valid unicode character)
    InvalidScalarValue(u32),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum HexLen {
    /// Unicode escape of form `\uXXXX`
    X4 = 4,
    /// Unicode escape of form `\UXXXXXXXX`
    X8 = 8,
}

impl From<HexLen> for u32 {
    fn from(len: HexLen) -> u32 {
        len as u32
    }
}

impl From<HexLen> for usize {
    fn from(len: HexLen) -> usize {
        len as usize
    }
}

pub struct EscapeError {
    pub kind: EscapeErrorKind,
    pub at: usize,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum EscapeErrorKind {
    /// Contains invlid char itself.
    InvalidCharInString(char),
    /// Invalid shorthand escape (i.e. not one of `\, \b, \f, \n, \r, \t, \", \'`).
    InvalidShorthandEscape(char),
    /// Too less digits specified in the unicode escape sequnence
    NotEnoughDigitsInHex { expected: HexLen, actual: u32 },
    /// Contains invalid unicode scalar value itself.
    InvalidEscapeValue(u32),
    /// Character that may not appear in the unescaped string literal.
    BannedChar(char),
    /// String literal has no closing quotes.
    UnterminatedString,
    /// No newline character after the backslash-whitespace sequence, e.g.
    /// ```toml
    /// key = "abc \   <- no newline, before the next non-whitespace character"
    /// ```
    NoNewlineInTrimmedWhitespace,
}

/// Unescapes the string string literal error-reluctantly (i.e. returns early
/// on the first detected error in the string literal)
///
/// Does best effort to unescape the first string literal in the input.
/// It expects the full string literal with leading and optionally trailing
/// (unterminated strings) quotes.
/// If no leading quotes are present, returns the empty string.
///
/// It expects the full string literal with leading and optionally trailing
/// (unterminated strings) quotes. If no leading quotes are present,
/// *only in this case* returns `None`.
pub fn try_unescape_str_lit(string_literal: &str) -> Option<Result<Cow<'_, str>, EscapeError>> {
    let tokens = tokenize_str_lit(string_literal)?;

    let mut acc = MaybeEscaped::new(string_literal);

    let mut has_trailing_quotes = false;

    for (span, token) in tokens {
        acc.append(match token {
            StringSubtoken::UnicodeEscape { unescaped, kind } => match unescaped {
                UnicodeEscape::Valid(ch) => ch,
                UnicodeEscape::NotEnoughDigits(actual) => {
                    return Some(Err(EscapeError {
                        kind: EscapeErrorKind::NotEnoughDigitsInHex {
                            actual,
                            expected: kind,
                        },
                        at: span.start,
                    }))
                }
                UnicodeEscape::InvalidScalarValue(val) => {
                    return Some(Err(EscapeError {
                        kind: EscapeErrorKind::InvalidEscapeValue(val),
                        at: span.start,
                    }))
                }
            },
            StringSubtoken::ShorthandEscape(ch) => match ch {
                Ok(ch) => ch,
                Err(ch) => {
                    return Some(Err(EscapeError {
                        kind: EscapeErrorKind::InvalidShorthandEscape(ch),
                        at: span.start,
                    }))
                }
            },
            StringSubtoken::Char(ch) => ch,
            StringSubtoken::BannedChar(it) => {
                return Some(Err(EscapeError {
                    kind: EscapeErrorKind::BannedChar(it),
                    at: span.start,
                }))
            }
            StringSubtoken::TrailingSlash => {
                return Some(Err(EscapeError {
                    kind: EscapeErrorKind::UnterminatedString,
                    at: 0,
                }))
            }
            StringSubtoken::TrimmedWhitespace {
                includes_newline: false,
            } => {
                return Some(Err(EscapeError {
                    kind: EscapeErrorKind::NoNewlineInTrimmedWhitespace,
                    at: span.start,
                }))
            }
            StringSubtoken::TrimmedWhitespace {
                includes_newline: true,
            }
            | StringSubtoken::TrailingQuotes
            | StringSubtoken::LeadingQuotes { .. }
            | StringSubtoken::LeadingNewline => {
                if matches!(token, StringSubtoken::TrailingQuotes) {
                    debug_assert!(!has_trailing_quotes);
                    has_trailing_quotes = true;
                }
                acc.skip(span);
                continue;
            }
        });
    }
    if !has_trailing_quotes {
        return Some(Err(EscapeError {
            kind: EscapeErrorKind::UnterminatedString,
            at: 0,
        }));
    }

    Some(Ok(acc.into_cow()))
}

/// Does best effort to unescape the first string literal in the input.
/// It expects the full string literal with leading and optionally trailing
/// (unterminated strings) quotes.
/// If no leading quotes are present, *only then* returns None.
///
/// It will replace all bad characters with `std::char::REPLACEMENT_CHARACTER`.
pub fn unescape_str_lit(string_literal: &str) -> Option<Cow<'_, str>> {
    let tokens = tokenize_str_lit(string_literal)?;

    let mut acc = MaybeEscaped::new(string_literal);

    for (span, token) in tokens {
        acc.append(match token {
            StringSubtoken::UnicodeEscape { unescaped, .. } => match unescaped {
                UnicodeEscape::Valid(ch) => ch,
                UnicodeEscape::NotEnoughDigits(_) => char::REPLACEMENT_CHARACTER,
                UnicodeEscape::InvalidScalarValue(_) => char::REPLACEMENT_CHARACTER,
            },
            StringSubtoken::ShorthandEscape(ch) => ch.unwrap_or(char::REPLACEMENT_CHARACTER),
            StringSubtoken::Char(ch) => ch,
            StringSubtoken::BannedChar(_) => char::REPLACEMENT_CHARACTER,
            StringSubtoken::TrailingSlash => char::REPLACEMENT_CHARACTER,
            StringSubtoken::TrimmedWhitespace { includes_newline: _ } // heuristically trim, even if there was no newline
            | StringSubtoken::TrailingQuotes
            | StringSubtoken::LeadingQuotes { .. }
            | StringSubtoken::LeadingNewline => {
                acc.skip(span);
                continue;
            }
        });
    }

    Some(acc.into_cow())
}

/// The same as `tokenize_str()`, but consumes
/// the leading quotes and returns them as the first element of the tuple.
/// It is fully safe to call this function if you wan't to check the kind of the string
/// literal.
/// ```
/// # use toml_lexer::*;
///
/// // Good:
/// let (quotes_span, quotes, mut iter) = tokenize_str_lit_take_leading_quotes("'foo'")
///     .expect("The string clearly has leading quotes");
///
/// assert_eq!(iter.next(), Some((Span { start: 1, end: 2 }, StringSubtoken::Char('f'))));
///
/// // Bad:
/// let (_, token) = tokenize_str_lit("'foo'")
///     .expect("Yes, there are leading quotes")
///     .next()
///     .expect("There must be at least one leading quotes token!");
/// let quotes = match token {
///     StringSubtoken::LeadingQuotes(it) => it,
///     _ => unreachable!("Common, there first token is always the leading quotes!")
/// };
/// ```
pub fn tokenize_str_lit_take_leading_quotes(
    string_literal: &str,
) -> Option<(
    Span,
    Quotes,
    impl '_ + Iterator<Item = (Span, StringSubtoken)>,
)> {
    StringSubtokenizer::from_cursor(Cursor::new(string_literal))
}

// TODO: test quotes tokens
/// Tokenizes the leading string literal into its component subtokens.
/// It determines the kind of the literal by the leading quotes and if there are
/// no leading quotes, *only in this case* returns `None`.
///
/// ```
/// # use toml_lexer::*;
/// assert!(tokenize_str_lit("No leading quotes").is_none());
///
/// let tokens = tokenize_str_lit("\"<- leading quote!").unwrap();
/// let tokens: Vec<(Span, StringSubtoken)> = tokens.collect();
/// let quotes = Quotes {
///     kind: StringKind::Basic,
///     len: QuotesLen::X1
/// };
///
/// assert_eq!(tokens[0], (Span { start: 0, end: 1 }, StringSubtoken::LeadingQuotes(quotes)));
/// ```
///
pub fn tokenize_str_lit(
    string_literal: &str,
) -> Option<impl '_ + Iterator<Item = (Span, StringSubtoken)>> {
    let (quotes_span, quotes, tokenizer) = tokenize_str_lit_take_leading_quotes(string_literal)?;

    let first_token = StringSubtoken::LeadingQuotes(quotes);

    Some(iter::once((quotes_span, first_token)).chain(tokenizer))
}

/// String subtokenizer is a state machine since the tokens it expects
/// depend on the previous context.
#[derive(Debug)]
enum State {
    Begin,
    Content,
    End,
}

#[derive(Debug)]
pub(crate) struct StringSubtokenizer<'a> {
    cursor: Cursor<'a>,
    state: State,
    kind: StringKind,
    multiline: bool,
}

impl<'a> StringSubtokenizer<'a> {
    pub(crate) fn from_cursor(mut cursor: Cursor<'a>) -> Option<(Span, Quotes, Self)> {
        let start = cursor.current_index();
        let quote = cursor.one()?;
        let kind = StringKind::from_quote(quote)?;

        let len = if cursor.peek_two() == Some((quote, quote)) {
            cursor.one();
            cursor.one();
            QuotesLen::X3
        } else {
            QuotesLen::X1
        };

        let me = StringSubtokenizer {
            cursor,
            kind,
            state: State::Begin,
            multiline: len == QuotesLen::X3,
        };
        let leading_quotes = Quotes { kind, len };

        Some((me.cursor.step_span(start), leading_quotes, me))
    }

    pub(crate) fn into_cursor(self) -> Cursor<'a> {
        self.cursor
    }

    fn unicode_hex(&mut self, len: HexLen) -> UnicodeEscape {
        debug_assert!(
            self.cursor.consumed_slice().ends_with("\\u")
                || self.cursor.consumed_slice().ends_with("\\U")
        );

        let mut code_point = 0u32;
        for n_digits in 0..len.into() {
            match self.cursor.peek_one().and_then(|ch| ch.to_digit(16)) {
                Some(digit) => code_point = (code_point * 16) + digit,
                _ => return UnicodeEscape::NotEnoughDigits(n_digits),
            }
            self.cursor.one();
        }
        std::char::from_u32(code_point)
            .map(UnicodeEscape::Valid)
            .unwrap_or_else(|| UnicodeEscape::InvalidScalarValue(code_point))
    }

    fn eat_3_trailing_quotes(&mut self) -> bool {
        let quote = self.kind.to_quote();

        debug_assert!(self.cursor.consumed_slice().ends_with(quote));

        let mut cloned = self.cursor.clone();
        // Lookahed 3 more chars to findout if the cursor is currently in the middle 3 closing quotes
        if !cloned.eatc(quote) || !cloned.eatc(quote) {
            return false;
        }
        if cloned.eatc(quote) {
            // this is the case of 4 consecutive quotes """"
            return false;
        }
        self.cursor.one();
        self.cursor.one();
        true
    }

    fn trimmed_whitespace(&mut self, begin: char) -> StringSubtoken {
        let mut includes_newline = begin == '\n';
        while let Some(ch @ ' ') | Some(ch @ '\t') | Some(ch @ '\n') = self.cursor.peek_one() {
            includes_newline = includes_newline || ch == '\n';
            self.cursor.one();
        }
        StringSubtoken::TrimmedWhitespace { includes_newline }
    }
}

impl Iterator for StringSubtokenizer<'_> {
    type Item = (Span, StringSubtoken);

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.cursor.current_index();

        let token = match self.state {
            State::Begin => {
                self.state = State::Content;
                if self.multiline && self.cursor.eatc('\n') {
                    StringSubtoken::LeadingNewline
                } else {
                    return self.next();
                }
            }
            State::Content => {
                let ch = self.cursor.peek_one()?;

                if ch == '\n' && !self.multiline {
                    return None;
                }

                self.cursor.one();

                match (self.kind, ch) {
                    (StringKind::Basic, '\\') => match self.cursor.one() {
                        None => StringSubtoken::TrailingSlash,
                        Some(ch) => match ch {
                            '"' => StringSubtoken::ShorthandEscape(Ok('"')),
                            '\\' => StringSubtoken::ShorthandEscape(Ok('\\')),
                            'n' => StringSubtoken::ShorthandEscape(Ok('\n')),
                            'r' => StringSubtoken::ShorthandEscape(Ok('\r')),
                            't' => StringSubtoken::ShorthandEscape(Ok('\t')),
                            'b' => StringSubtoken::ShorthandEscape(Ok('\u{8}')),
                            'f' => StringSubtoken::ShorthandEscape(Ok('\u{c}')),
                            'u' | 'U' => {
                                let kind = if ch == 'u' { HexLen::X4 } else { HexLen::X8 };
                                let unescaped = self.unicode_hex(kind);
                                StringSubtoken::UnicodeEscape { unescaped, kind }
                            }
                            ' ' | '\t' | '\n' if self.multiline => self.trimmed_whitespace(ch),
                            _ => StringSubtoken::ShorthandEscape(Err(ch)),
                        },
                    },
                    _ if ch == self.kind.to_quote() => {
                        if self.multiline && !self.eat_3_trailing_quotes() {
                            StringSubtoken::Char(ch)
                        } else {
                            self.state = State::End;
                            StringSubtoken::TrailingQuotes
                        }
                    }
                    _ if (ch >= '\u{20}' && ch != '\u{7f}') || matches!(ch, '\u{09}' | '\n') => {
                        StringSubtoken::Char(ch)
                    }
                    _ => StringSubtoken::BannedChar(ch),
                }
            }
            State::End => return None,
        };

        Some((self.cursor.step_span(start), token))
    }
}

#[derive(Debug)]
enum MaybeEscaped<'a> {
    NotEscaped(&'a str, CharIndices<'a>, usize),
    Escaped(String),
}

// TODO: test
impl<'a> MaybeEscaped<'a> {
    fn new(source: &str) -> MaybeEscaped<'_> {
        MaybeEscaped::NotEscaped(source, source.char_indices(), 0)
    }

    fn skip(&mut self, span: Span) {
        match self {
            // Move the start of the slice further if we are skipping
            // right from the beginning of the string
            MaybeEscaped::NotEscaped(source, char_indices, begin) if span.start == *begin => {
                *begin = span.end;
                *char_indices = source[*begin..].char_indices();
            }
            MaybeEscaped::NotEscaped(..) => {
                // Don't do anything since we might be skipping right until the end of the string.
                // If not, the next `append()` will upgrade us to owned variant
            }
            MaybeEscaped::Escaped(_) => {}
        }
    }

    fn append(&mut self, ch: char) {
        match self {
            MaybeEscaped::NotEscaped(source, char_indices, begin) => {
                let (i, contents_char) = char_indices
                    .next()
                    .expect("the caller (i.e. tokenizer) has eaten at least one char `ch`");
                if ch == contents_char {
                    // .. we may reuse the source string
                } else {
                    *self = MaybeEscaped::Escaped(format!("{}{}", &source[*begin..*begin + i], ch));
                }
            }
            MaybeEscaped::Escaped(it) => it.push(ch),
        }
    }

    fn into_cow(self) -> Cow<'a, str> {
        match self {
            MaybeEscaped::NotEscaped(source, mut char_indices, begin) => {
                match char_indices.next() {
                    Some((end, _)) => Cow::Borrowed(&source[begin..begin + end]),
                    None => Cow::Borrowed(&source[begin..]),
                }
            }
            MaybeEscaped::Escaped(it) => Cow::Owned(it),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_matches {
        ($val:expr, $pat:pat) => {{
            let val = &$val;
            if !matches!(val, $pat) {
                let val_str = stringify!($val);
                let pat_str = stringify!($pat);
                panic!(
                    "{} doesn't match the pattern: {}\n actual value: {:?}",
                    val_str, pat_str, val
                );
            }
        }};
    }

    #[test]
    fn unescape_borrows_when_possible() {
        use unescape_str_lit as unescape;

        assert_matches!(unescape("'abcdef'"), Some(Cow::Borrowed("abcdef")));
        assert_matches!(unescape("'abcdef"), Some(Cow::Borrowed("abcdef")));
        assert_matches!(unescape("'''abcdef'"), Some(Cow::Borrowed("abcdef'")));
        assert_matches!(unescape("'''\nabcdef"), Some(Cow::Borrowed("abcdef")));
        assert_matches!(
            unescape("\"\"\"\\ \t \n \t abcdef"),
            Some(Cow::Borrowed("abcdef"))
        );
        assert_matches!(unescape(r#""\\""#), Some(Cow::Borrowed("\\")));
    }

    #[test]
    fn unescape_returns_owned_when_meets_escapes() {
        use unescape_str_lit as unescape;

        let t = |input, expected: &str| {
            let actual = unescape(input);
            assert_matches!(actual, Some(Cow::Owned(_)));
            assert_eq!(actual, Some(expected.into()));
        };

        t(r#""\t""#, "\t");
        t(r#""""abc\ a"#, "abca");
        t(r#""\u1234""#, "\u{1234}");
    }

    #[test]
    fn leading_and_trailing_quotes() {
        let t = |input, kind, quotes_len: usize, trailing| {
            let it = tokenize_str_lit_take_leading_quotes(input).unwrap();
            let (_, actual_leading, tokens) = it;

            let leading = Quotes {
                kind,
                len: match quotes_len {
                    1 => QuotesLen::X1,
                    3 => QuotesLen::X3,
                    _ => unreachable!(),
                },
            };

            assert_eq!(leading, actual_leading);
            let last_token = tokens.last();
            let matches = matches!(last_token, Some((_, StringSubtoken::TrailingQuotes)));
            assert!(matches == trailing, "{:?}", last_token);
        };

        let t_none = |input| assert!(matches!(tokenize_str_lit_take_leading_quotes(input), None));

        t_none("");
        t_none("a");
        t_none("\\");

        t("'a", StringKind::Literal, 1, false);
        t("\"a", StringKind::Basic, 1, false);
        t("'''a", StringKind::Literal, 3, false);
        t("\"\"\"a", StringKind::Basic, 3, false);

        t("'a'", StringKind::Literal, 1, true);
        t("\"a\"", StringKind::Basic, 1, true);
        t("'''a'''", StringKind::Literal, 3, true);
        t("\"\"\"a\"\"\"", StringKind::Basic, 3, true);

        t("''''", StringKind::Literal, 3, false);
        t("\"\"\"\"", StringKind::Basic, 3, false);

        t("'''''", StringKind::Literal, 3, false);
        t("\"\"\"\"\"", StringKind::Basic, 3, false);

        t("'", StringKind::Literal, 1, false);
        t("\"", StringKind::Basic, 1, false);
        t("''", StringKind::Literal, 1, true);
        t("\"\"", StringKind::Basic, 1, true);

        t("'''", StringKind::Literal, 3, false);
        t("\"\"\"", StringKind::Basic, 3, false);
        t("''''''", StringKind::Literal, 3, true);
        t("\"\"\"\"\"\"", StringKind::Basic, 3, true);
    }

    mod unicode_escapes {
        use super::*;

        fn assert_unicode_escape(len: HexLen, input: &str, expected: UnicodeEscape) {
            assert_single_string_content_subtoken(
                input,
                StringSubtoken::UnicodeEscape {
                    kind: len,
                    unescaped: expected,
                },
                &["\"", "\"\"\""],
            );
        }

        #[test]
        fn valid_unicode_escapes() {
            let t = |len, input, expected| {
                assert_unicode_escape(len, input, UnicodeEscape::Valid(expected))
            };

            t(HexLen::X4, "\\u0000", '\u{0}');
            t(HexLen::X4, "\\u1f1A", '\u{1F1A}');
            t(HexLen::X4, "\\u0019", '\u{19}');

            t(HexLen::X8, "\\U00000000", '\u{0}');
            t(HexLen::X8, "\\U000AbBcD", '\u{ABBCD}');
            t(HexLen::X8, "\\U0010FFFF", '\u{10FFFF}');

            let valid_unicode_escape = |kind, unescaped| StringSubtoken::UnicodeEscape {
                kind,
                unescaped: UnicodeEscape::Valid(unescaped),
            };
            assert_string_content_subtokens(
                "\\u12345\\U000456789F",
                &["\"", "\"\"\""],
                vec![
                    ((0, 6), valid_unicode_escape(HexLen::X4, '\u{1234}')),
                    ((6, 7), StringSubtoken::Char('5')),
                    ((7, 17), valid_unicode_escape(HexLen::X8, '\u{45678}')),
                    ((17, 18), StringSubtoken::Char('9')),
                    ((18, 19), StringSubtoken::Char('F')),
                ],
            );
        }

        #[test]
        fn not_enough_digits_in_unicode_escapes() {
            let t = |len, input, expected| {
                assert_unicode_escape(len, input, UnicodeEscape::NotEnoughDigits(expected))
            };

            t(HexLen::X4, "\\u", 0);
            t(HexLen::X4, "\\u0", 1);
            t(HexLen::X4, "\\u00", 2);
            t(HexLen::X4, "\\u000", 3);
            t(HexLen::X8, "\\U", 0);
            t(HexLen::X8, "\\U0", 1);
            t(HexLen::X8, "\\U00", 2);
            t(HexLen::X8, "\\U000", 3);
            t(HexLen::X8, "\\U0000", 4);
            t(HexLen::X8, "\\U00000", 5);
            t(HexLen::X8, "\\U000000", 6);
            t(HexLen::X8, "\\U0000000", 7);
        }

        #[test]
        fn invalid_scalar_value() {
            let t = |len, input, expected| {
                assert_unicode_escape(len, input, UnicodeEscape::InvalidScalarValue(expected))
            };
            t(HexLen::X4, "\\uD800", 0xd800);
            t(HexLen::X8, "\\U00110000", 0x0011_0000);
            t(HexLen::X8, "\\Uffffffff", 0xffff_ffff);
        }
    }

    mod shorthand_escapes {
        use super::*;

        fn t_all(input: &str, result: Result<char, char>) {
            assert_single_string_content_subtoken(
                input,
                StringSubtoken::ShorthandEscape(result),
                &["\"", "\"\"\""],
            );
        }

        fn t_single_line(input: &str, result: Result<char, char>) {
            assert_single_string_content_subtoken(
                input,
                StringSubtoken::ShorthandEscape(result),
                &["\""],
            );
        }

        #[test]
        fn valid_shorthand_escapes() {
            t_all(r#"\b"#, Ok('\u{0008}'));
            t_all(r#"\t"#, Ok('\u{0009}'));
            t_all(r#"\n"#, Ok('\u{000A}'));
            t_all(r#"\f"#, Ok('\u{000C}'));
            t_all(r#"\r"#, Ok('\u{000D}'));
            t_all(r#"\""#, Ok('\u{0022}'));
            t_all(r#"\\"#, Ok('\u{005C}'));
        }

        #[test]
        fn invalid_shorthand_escapes() {
            t_all(r#"\a"#, Err('a'));
            t_all("\\\u{0}", Err('\u{0}'));
            t_all("\\🦀", Err('🦀'));

            t_single_line("\\\r\n", Err('\n'));
            t_single_line("\\\n", Err('\n'));
        }
    }

    #[test]
    fn banned_chars() {
        let t = |input, expected| {
            assert_single_string_content_subtoken(
                input,
                StringSubtoken::BannedChar(expected),
                &["\"", "\"\"\"", "'", "'''"],
            )
        };

        t("\u{0}", '\u{0}');
        t("\u{1}", '\u{1}');
        t("\u{18}", '\u{18}');
        t("\u{19}", '\u{19}');
        t("\u{7f}", '\u{7f}');
    }

    #[test]
    fn leading_newline() {
        let t = |input| {
            assert_single_string_content_subtoken(
                input,
                StringSubtoken::LeadingNewline,
                &["\"\"\"", "'''"],
            )
        };
        t("\n");
        t("\r\n");
    }

    #[test]
    fn valid_char_itself() {
        let t = |input, expected| {
            assert_single_string_content_subtoken(
                input,
                StringSubtoken::Char(expected),
                &["\"", "\"\"\"", "'", "'''"],
            );
        };

        t("a", 'a');
        t("Ї", 'Ї');
        t("🦀", '🦀');
        t("©", '©');
    }

    #[test]
    fn escapes_are_ignored_in_literal_strings() {
        assert_string_content_subtokens(
            "\\u1234\\n\\ \t ",
            &["'", "'''"],
            vec![
                ((0, 1), StringSubtoken::Char('\\')),
                ((1, 2), StringSubtoken::Char('u')),
                ((2, 3), StringSubtoken::Char('1')),
                ((3, 4), StringSubtoken::Char('2')),
                ((4, 5), StringSubtoken::Char('3')),
                ((5, 6), StringSubtoken::Char('4')),
                ((6, 7), StringSubtoken::Char('\\')),
                ((7, 8), StringSubtoken::Char('n')),
                ((8, 9), StringSubtoken::Char('\\')),
                ((9, 10), StringSubtoken::Char(' ')),
                ((10, 11), StringSubtoken::Char('\t')),
                ((11, 12), StringSubtoken::Char(' ')),
            ],
        );
    }

    #[test]
    fn valid_trimmed_whitespace() {
        use assert_string_content_subtokens as t;

        t(
            "\\ \n  ",
            &["\"\"\""],
            vec![(
                (0, 5),
                StringSubtoken::TrimmedWhitespace {
                    includes_newline: true,
                },
            )],
        );
        t(
            " \\ \n \t:\t",
            &["\"\"\""],
            vec![
                ((0, 1), StringSubtoken::Char(' ')),
                (
                    (1, 6),
                    StringSubtoken::TrimmedWhitespace {
                        includes_newline: true,
                    },
                ),
                ((6, 7), StringSubtoken::Char(':')),
                ((7, 8), StringSubtoken::Char('\t')),
            ],
        );
    }

    #[test]
    fn trimmed_whitespace_with_no_newline() {
        use assert_string_content_subtokens as t;

        t(
            "\\   ",
            &["\"\"\""],
            vec![(
                (0, 4),
                StringSubtoken::TrimmedWhitespace {
                    includes_newline: false,
                },
            )],
        );
        t(
            " \\  \t:\t",
            &["\"\"\""],
            vec![
                ((0, 1), StringSubtoken::Char(' ')),
                (
                    (1, 5),
                    StringSubtoken::TrimmedWhitespace {
                        includes_newline: false,
                    },
                ),
                ((5, 6), StringSubtoken::Char(':')),
                ((6, 7), StringSubtoken::Char('\t')),
            ],
        );
    }

    #[test]
    fn trailing_slash() {
        // May appear only in unterminated basic strings
        let acutal: Vec<_> = tokenize_str_lit("\"\\").unwrap().collect();
        assert_eq!(
            acutal,
            vec![
                (
                    Span { start: 0, end: 1 },
                    StringSubtoken::LeadingQuotes(Quotes {
                        kind: StringKind::Basic,
                        len: QuotesLen::X1
                    })
                ),
                (Span { start: 1, end: 2 }, StringSubtoken::TrailingSlash)
            ]
        );

        let acutal: Vec<_> = tokenize_str_lit("\"\"\"\\").unwrap().collect();
        assert_eq!(
            acutal,
            vec![
                (
                    Span { start: 0, end: 3 },
                    StringSubtoken::LeadingQuotes(Quotes {
                        kind: StringKind::Basic,
                        len: QuotesLen::X3
                    })
                ),
                (Span { start: 3, end: 4 }, StringSubtoken::TrailingSlash)
            ]
        );
    }

    fn quotes_permutations(contents: &str, quotes_cases: &[&str]) -> Vec<String> {
        quotes_cases
            .iter()
            .flat_map(|quotes| {
                let terminated = format!("{}{}{}", quotes, contents, quotes);
                let unterminated = format!("{}{}", quotes, contents);
                iter::once(terminated).chain(iter::once(unterminated))
            })
            .collect()
    }

    fn assert_string_content_subtokens(
        input_contents: &str,
        quotes_cases: &[&str],
        expected: Vec<((usize, usize), StringSubtoken)>,
    ) {
        assert!(quotes_cases
            .iter()
            .all(|&case| matches!(case, "'" | "\"" | "'''" | "\"\"\"")));

        for string_literal in quotes_permutations(input_contents, quotes_cases) {
            let it = tokenize_str_lit_take_leading_quotes(&string_literal).unwrap();
            let (_, leading_quotes, actual) = it;

            let quotes_len: usize = leading_quotes.len.into();

            let actual: Vec<_> = actual
                .filter(|(_, token)| *token != StringSubtoken::TrailingQuotes)
                .map(|(span, token)| ((span.start - quotes_len, span.end - quotes_len), token))
                .collect();

            assert_eq!(actual, expected, "\nstring_literal: {{{}}}", string_literal);
        }
    }

    fn assert_single_string_content_subtoken(
        contents: &str,
        token: StringSubtoken,
        quotes_cases: &[&str],
    ) {
        assert_string_content_subtokens(contents, quotes_cases, vec![((0, contents.len()), token)]);
    }
}
