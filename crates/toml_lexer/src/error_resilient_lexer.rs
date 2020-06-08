use std::char;
use std::str;

use self::Token::*;
use crate::{cursor::Cursor, QuotesLen, Span, StringKind, StringSubtoken, StringSubtokenizer};

/// Represents a lexeme of TOML language.
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum Token {
    /// Unknown character, the token could not be created
    Unknown(char),

    Whitespace,
    Newline,
    Comment,

    Equals,
    Period,
    Comma,
    Colon,
    Plus,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,

    /// Keylike token, it may also include floats, ints and date-time literals.
    /// The actual interpretation of this token should be decided on higher level.
    /// TODO: find out where it is decided
    Keylike,
    // FIXME: I wish there was a way to elegantly pack these into u8 bit flags
    // and leave each bit as a separate type (@Veetaha)
    String {
        kind: StringKind,
        multiline: bool,
        terminated: bool,
    },
}

/// Tokenizer is called to break a string up into its component tokens.
/// It implements `Iterator<Item = Token>` for this purpose.
///
/// This tokenizer is error-resilient as in it always produces a token,
/// even a malformed one.
/// The errors that may occur during tokenization are mainly related to
/// string literals. The strings literals are not unescaped by this tokenizer
/// but they are checked for being terminated or not.
/// If you want to get unescaped string literals you should take a look at
/// `unescape_str_lit()/try_unescape_str_lit()` where the first one is error-resilient
/// and the second one is error-reluctant.
///
/// ```
/// # use toml_lexer::{error_resilient_lexer::{self, Token}, Span, StringKind};
/// # use toml_lexer::unescape_str_lit;
/// # use std::borrow::Cow;
/// let input = "\"valid: \\n, \\u1234 invalid: \\{";
/// let tokenizer = error_resilient_lexer::Tokenizer::new(input);
/// let spans_and_tokens: Vec<(Span, Token)> = tokenizer.collect();
///
/// let span = Span { start: 0, end: input.len() };
/// let token = Token::String {
///     kind: StringKind::Basic,
///     multiline: false,
///     terminated: false,
/// };
/// assert_eq!(spans_and_tokens, vec![(span, token)]);
///
/// let unescaped = Cow::Borrowed("valid: \n, \u{1234} invalid: �");
/// assert_eq!(unescape_str_lit(input), Some(unescaped));
///
/// ```
#[derive(Clone)]
pub struct Tokenizer<'a>(Cursor<'a>);

impl<'a> Tokenizer<'a> {
    /// Creates a new `Tokenizer`. It skips the first utf-8 BOM character right away,
    /// but beware that its length contributes to resulting tokens' spans.
    /// The tokenizer contains an internal iterator over the input string to keep track
    /// of the already analyzed part of the string.
    pub fn new(input: &'a str) -> Tokenizer<'a> {
        let mut t = Tokenizer(Cursor::new(input));
        // Eat utf-8 BOM
        t.0.eatc('\u{feff}');
        t
    }

    /// Returns the input string which `Tokenizer` was initially created with.
    pub fn input(&self) -> &'a str {
        self.0.string()
    }

    pub fn current_index(&self) -> usize {
        self.0.current_index()
    }

    fn whitespace_token(&mut self) -> Token {
        while self.0.eatc(' ') || self.0.eatc('\t') {
            // ...
        }
        Whitespace
    }

    fn comment_token(&mut self) -> Token {
        debug_assert!(self.0.consumed_slice().ends_with('#'));

        while let Some(ch) = self.0.peek_one() {
            if ch != '\t' && (ch < '\u{20}' || ch > '\u{10ffff}') {
                break;
            }
            self.0.one();
        }
        Comment
    }

    fn keylike(&mut self) -> Token {
        while let Some(ch) = self.0.peek_one() {
            if !is_keylike(ch) {
                break;
            }
            self.0.one();
        }
        Keylike
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = (Span, Token);

    /// Analyzes the next token in the input string.
    fn next(&mut self) -> Option<(Span, Token)> {
        let start = self.0.current_index();

        let token = if let Some(it) = StringSubtokenizer::from_cursor(self.0.clone()) {
            let (_, quotes, mut subtokenizer) = it;

            let end = subtokenizer.find_map(|(span, subtoken)| match subtoken {
                StringSubtoken::TrailingQuotes => Some(span.end),
                _ => None,
            });
            assert_eq!(subtokenizer.next(), None);

            self.0 = subtokenizer.into_cursor();

            Token::String {
                kind: quotes.kind,
                multiline: quotes.len == QuotesLen::X3,
                terminated: end.is_some(),
            }
        } else {
            match self.0.one()? {
                '\n' => Newline,
                ' ' | '\t' => self.whitespace_token(),
                '#' => self.comment_token(),
                '=' => Equals,
                '.' => Period,
                ',' => Comma,
                ':' => Colon,
                '+' => Plus,
                '{' => LeftBrace,
                '}' => RightBrace,
                '[' => LeftBracket,
                ']' => RightBracket,
                ch if is_keylike(ch) => self.keylike(),
                ch => Unknown(ch),
            }
        };
        Some((self.0.step_span(start), token))
    }
}

fn is_keylike(ch: char) -> bool {
    ('A' <= ch && ch <= 'Z')
        || ('a' <= ch && ch <= 'z')
        || ('0' <= ch && ch <= '9')
        || ch == '-'
        || ch == '_'
}

#[cfg(test)]
mod tests {
    use super::{StringKind, Token, Tokenizer};
    #[test]
    fn empty_input() {
        assert_tokens("", vec![]);
    }

    #[test]
    fn unknown_token() {
        let t = |input| assert_single_token(input, Token::Unknown(input.chars().next().unwrap()));

        t("\\");
        t("Ї");
        t("🦀");
        t("©");
        t("\r");
        t("\u{0}");
    }

    #[test]
    fn keylike() {
        let t = |input| assert_single_token(input, Token::Keylike);

        t("foo");
        t("0bar");
        t("bar0");
        t("1234");
        t("a-b");
        t("a_B");
        t("-_-");
        t("___");
    }

    #[test]
    fn all() {
        assert_tokens(
            " a ",
            vec![
                ((0, 1), Token::Whitespace),
                ((1, 2), Token::Keylike),
                ((2, 3), Token::Whitespace),
            ],
        );
        assert_tokens(
            " a\t [[]] \t [] {} , . =\n# foo \r\n#foo \n ",
            vec![
                ((0, 1), Token::Whitespace),
                ((1, 2), Token::Keylike),
                ((2, 4), Token::Whitespace),
                ((4, 5), Token::LeftBracket),
                ((5, 6), Token::LeftBracket),
                ((6, 7), Token::RightBracket),
                ((7, 8), Token::RightBracket),
                ((8, 11), Token::Whitespace),
                ((11, 12), Token::LeftBracket),
                ((12, 13), Token::RightBracket),
                ((13, 14), Token::Whitespace),
                ((14, 15), Token::LeftBrace),
                ((15, 16), Token::RightBrace),
                ((16, 17), Token::Whitespace),
                ((17, 18), Token::Comma),
                ((18, 19), Token::Whitespace),
                ((19, 20), Token::Period),
                ((20, 21), Token::Whitespace),
                ((21, 22), Token::Equals),
                ((22, 23), Token::Newline),
                ((23, 29), Token::Comment),
                ((29, 31), Token::Newline),
                ((31, 36), Token::Comment),
                ((36, 37), Token::Newline),
                ((37, 38), Token::Whitespace),
            ],
        );
    }

    #[test]
    fn bad_comment() {
        assert_tokens(
            "#\u{0}",
            vec![((0, 1), Token::Comment), ((1, 2), Token::Unknown('\u{0}'))],
        );
    }

    mod strings {
        use super::*;
        use Flags::*;

        /// B - basic
        /// L - literal
        /// S - single-line
        /// M - multi-line
        /// T - terminated
        /// U - unterminated
        #[derive(Copy, Clone)]
        enum Flags {
            BST,
            BSU,
            BMT,
            BMU,
            LST,
            LSU,
            LMT,
            LMU,
        }

        fn str(flags: Flags) -> Token {
            let (terminated, multiline, kind) = match flags {
                BMT => (true, true, StringKind::Basic),
                BMU => (false, true, StringKind::Basic),
                BST => (true, false, StringKind::Basic),
                BSU => (false, false, StringKind::Basic),
                LMT => (true, true, StringKind::Literal),
                LMU => (false, true, StringKind::Literal),
                LST => (true, false, StringKind::Literal),
                LSU => (false, false, StringKind::Literal),
            };
            Token::String {
                kind,
                multiline,
                terminated,
            }
        }

        fn assert_single_string(flags: Flags, input: &str, expected_unescaped: &str) {
            assert_single_token(input, str(flags));
            let unescaped = crate::unescape_str_lit(input).unwrap();
            assert_eq!(unescaped, expected_unescaped, "input: {{{}}}", input);
        }

        fn assert_empty_string(flags: Flags, input: &str) {
            assert_single_string(flags, input, "");
        }

        #[test]
        fn terminated_empty_strings() {
            use assert_empty_string as t;

            t(LST, "''");
            t(LMT, "''''''");
            t(LMT, "'''\n'''");

            t(BST, r#""""#);
            t(BMT, r#""""""""#);

            t(BMT, "\"\"\"\n\"\"\"");
            t(BMT, "\"\"\"\n\\\n  \t\t  \"\"\"");
        }

        #[test]
        fn single_char_strings() {
            use assert_single_string as t;

            t(LST, "'a'", "a");
            t(LST, "' '", " ");
            t(LST, "'\t'", "\t");
            t(LMT, "'''a'''", "a");
            t(LMT, "''' '''", " ");
            t(LMT, "'''\t'''", "\t");
            t(LMT, "'''''''", "'");
            t(BST, r#""a""#, "a");
            t(BST, r#""\t""#, "\t");
            t(BST, "\"\t\"", "\t");
            t(BMT, r#""""a""""#, "a");
            t(BMT, r#"""""""""#, "\"");
            t(BMT, r#""""\t""""#, "\t");
            t(BMT, "\"\"\"\t\"\"\"", "\t");
            t(BMT, r#""""\"""""#, "\"");
        }

        #[test]
        fn multi_char_strings() {
            use assert_single_string as t;

            t(LST, "'ab'", "ab");
            t(LST, "'\"a'", "\"a");
            t(LST, "'\\t'", "\\t");

            t(LMT, "''''''''", "''");
            t(BMT, r#""""""""""#, "\"\"");

            t(LMT, "'''\n'a\n'''", "'a\n");
            t(LMT, "'''a\n'a\r\n'''", "a\n'a\n");
            t(LST, "'\\U00'", "\\U00");

            t(BST, r#""\\t""#, "\\t");
            t(BMT, r#""""\\t""""#, "\\t");
        }

        #[test]
        fn unterminated_strings() {
            use assert_single_string as t;

            t(LMU, "'''''", "''");
            t(BMU, r#"""""""#, "\"\"");
            t(LMU, "''''", "'");
            t(BMU, r#""""""#, "\"");

            t(LSU, "'a", "a");
            t(LSU, "'\\", "\\");

            t(BSU, r#""a"#, "a");
            t(BSU, r#""\"#, "�");
            t(BSU, r#""\""#, "\"");

            t(LMU, "'''a", "a");
            t(LMU, "'''\\", "\\");

            t(BMU, r#""""a"#, "a");
            t(BMU, r#""""\"#, "�");
            t(BMU, r#""""\""#, "\"");

            assert_tokens("'\\''", vec![((0, 3), str(LST)), ((3, 4), str(LSU))]);
            assert_tokens(
                "'foo\n'",
                vec![
                    ((0, 4), str(LSU)),
                    ((4, 5), Token::Newline),
                    ((5, 6), str(LSU)),
                ],
            );
            assert_tokens(
                "\"foo\n\"",
                vec![
                    ((0, 4), str(BSU)),
                    ((4, 5), Token::Newline),
                    ((5, 6), str(BSU)),
                ],
            );
        }

        #[test]
        fn with_escapes() {
            use assert_single_string as t;

            t(BMT, "\"\"\"\n\t\"\"\"", "\t");
            t(BMT, "\"\"\"\\\n\"\"\"", "");
            t(
                BMT,
                "\"\"\"\\\n     \t   \t  \\\r\n  \t \n  \t \r\n\"\"\"",
                "",
            );
            t(BST, r#""\r""#, "\r");
            t(BST, r#""\n""#, "\n");
            t(BST, r#""\b""#, "\u{8}");
            t(BST, r#""a\fa""#, "a\u{c}a");
            t(BST, r#""\"a""#, "\"a");
            t(BMT, "\"\"\"\na\"\"\"", "a");
            t(BMT, r#""""a\"""b""""#, "a\"\"\"b");
        }
    }

    fn assert_tokens(input: &str, expected: Vec<((usize, usize), Token)>) {
        panic_on_duplicated_input(input);

        let t = Tokenizer::new(input);
        let actual: Vec<_> = t.map(|(span, token)| (span.into(), token)).collect();
        assert_eq!(actual, expected, "input: {}", input);
    }

    fn assert_single_token(input: &str, expected_token: Token) {
        assert_tokens(input, vec![((0, input.len()), expected_token)]);
    }

    /// overtesting is bad :D
    pub(super) fn panic_on_duplicated_input(input: &str) {
        use once_cell::sync::Lazy;
        use std::{collections::HashSet, sync::Mutex};

        static INPUTS: Lazy<Mutex<HashSet<std::string::String>>> = Lazy::new(Default::default);
        let mut set = INPUTS.lock().unwrap();
        assert!(!set.contains(input), "duplicated test: {{{}}}", input);
        set.insert(input.to_owned());
    }
}
