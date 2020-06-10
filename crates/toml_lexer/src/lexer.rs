use std::char;
use std::str;

use crate::{cursor::Cursor, str_lit, Span};
use TokenKind::*;

/// Represents a (possibly malformed) lexeme of TOML language.
pub struct Token {
    /// Span that the token occupies in the input string
    pub span: Span,
    /// Kind if the token
    pub kind: TokenKind,
}

/// Defines the type of the token as well as additional information
/// whether it is malfromed and in which way.
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum TokenKind {
    /// Unknown character, the token could not be created
    Unknown,
    /// Consecutive whitespace characters (spans ony a single line)
    Whitespace,
    /// `\n` or `\r\n`
    Newline,
    /// Comment with its prefix (e.g. `# foo bar`)
    Comment,
    /// `=`
    Equals,
    /// `.`
    Period,
    /// `,`
    Comma,
    /// `:`
    Colon,
    /// `+`
    Plus,
    /// `{`
    LeftBrace,
    /// `}`
    RightBrace,
    /// `[`
    LeftBracket,
    /// `]`
    RightBracket,
    /// Keylike token, it may also include floats, ints and date-time literals.
    /// The actual interpretation of this token should be decided on higher level.
    // TODO: find out where it is decided and add number and date parsing into this crate
    Keylike,
    /// String literal subtoken
    StrLitSubtoken(str_lit::StrLitSubtoken),
}

/// Tokenizer is called to break a string up into its component tokens.
/// It implements `Iterator<Item = Token>` for this purpose.
/// ```
/// # use toml_lexer::*;
/// fn tokenize(input: &str) -> impl '_ + Iterator<Item = Token> {
///     Tokenizer::new(input)
/// }
/// ```
#[derive(Clone)]
pub struct Tokenizer<'s> {
    cursor: Cursor<'s>,
    state: State<'s>,
}

#[derive(Clone)]
enum State<'s> {
    ReadingContent,
    ReadingStrLit(str_lit::StrLitTokenizer<'s>),
}

impl<'s> Tokenizer<'s> {
    /// Creates a new `Tokenizer`. It skips the first utf-8 BOM character right away,
    /// but beware that its length contributes to resulting tokens' spans.
    /// The tokenizer contains an internal iterator over the input string to keep track
    /// of the already analyzed part of the string.
    pub fn new(input: &'s str) -> Tokenizer<'s> {
        let mut cursor = Cursor::new(input);

        // Eat utf-8 BOM
        cursor.eatc('\u{feff}');
        Tokenizer {
            cursor,
            state: State::ReadingContent,
        }
    }

    /// Returns the input string which `Tokenizer` was initially created with.
    pub fn input(&self) -> &'s str {
        self.cursor.string()
    }

    /// The offset in the input string of the next token to be lexed.
    pub fn current_index(&self) -> usize {
        self.cursor.current_index()
    }

    fn whitespace_token(&mut self) -> TokenKind {
        while self.cursor.eatc(' ') || self.cursor.eatc('\t') {
            // ...
        }
        Whitespace
    }

    fn comment_token(&mut self) -> TokenKind {
        debug_assert!(self.cursor.consumed_slice().ends_with('#'));

        while matches!(self.cursor.peek_one(), Some(ch) if ch == '\t' || ch >= '\u{20}') {
            self.cursor.one();
        }
        Comment
    }

    fn keylike(&mut self) -> TokenKind {
        while matches!(self.cursor.peek_one(), Some(ch) if is_keylike(ch)) {
            self.cursor.one();
        }
        Keylike
    }
}

impl<'s> Iterator for Tokenizer<'s> {
    type Item = Token;

    /// Analyzes the next token in the input string.
    fn next(&mut self) -> Option<Token> {
        match self.state {
            State::ReadingContent => {
                // Try to read a string literal
                if let Some(it) = str_lit::StrLitTokenizer::from_cursor(self.cursor.clone()) {
                    let (leading_quotes_span, leading_quotes, subtokenizer) = it;
                    let kind =
                        StrLitSubtoken(str_lit::StrLitSubtoken::LeadingQuotes(leading_quotes));

                    self.state = State::ReadingStrLit(subtokenizer);
                    return Some(Token {
                        span: leading_quotes_span,
                        kind,
                    });
                }

                let (start, ch) = self.cursor.one_with_index()?;
                let kind = match ch {
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
                    _ if is_keylike(ch) => self.keylike(),
                    _ => Unknown,
                };
                Some(Token {
                    span: self.cursor.span_from(start),
                    kind,
                })
            }
            State::ReadingStrLit(ref mut subtokenizer) => match subtokenizer.next() {
                Some((span, subtoken)) => Some(Token {
                    span,
                    kind: StrLitSubtoken(subtoken),
                }),
                None => {
                    self.cursor = subtokenizer.cursor().clone();
                    self.state = State::ReadingContent;
                    // single-stackframe recursive call with new state
                    self.next()
                }
            },
        }
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
    use super::*;
    #[test]
    fn empty_input() {
        assert_tokens("", vec![]);
    }

    #[test]
    fn unknown_token() {
        let t = |input| assert_single_token(input, Unknown);

        t("\\");
        t("Ї");
        t("🦀");
        t("©");
        t("\r");
        t("\u{0}");
    }

    #[test]
    fn keylike() {
        let t = |input| assert_single_token(input, Keylike);

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
                ((0, 1), Whitespace),
                ((1, 2), Keylike),
                ((2, 3), Whitespace),
            ],
        );
        assert_tokens(
            " a\t [[]] \t [] {} , . =\n# foo \r\n#foo \n ",
            vec![
                ((0, 1), Whitespace),
                ((1, 2), Keylike),
                ((2, 4), Whitespace),
                ((4, 5), LeftBracket),
                ((5, 6), LeftBracket),
                ((6, 7), RightBracket),
                ((7, 8), RightBracket),
                ((8, 11), Whitespace),
                ((11, 12), LeftBracket),
                ((12, 13), RightBracket),
                ((13, 14), Whitespace),
                ((14, 15), LeftBrace),
                ((15, 16), RightBrace),
                ((16, 17), Whitespace),
                ((17, 18), Comma),
                ((18, 19), Whitespace),
                ((19, 20), Period),
                ((20, 21), Whitespace),
                ((21, 22), Equals),
                ((22, 23), Newline),
                ((23, 29), Comment),
                ((29, 31), Newline),
                ((31, 36), Comment),
                ((36, 37), Newline),
                ((37, 38), Whitespace),
            ],
        );
    }

    #[test]
    fn bad_comment() {
        assert_tokens("#\u{0}", vec![((0, 1), Comment), ((1, 2), Unknown)]);
    }

    fn assert_tokens(input: &str, expected: Vec<((usize, usize), TokenKind)>) {
        let sut = Tokenizer::new(input);
        let actual: Vec<_> = sut.map(|token| (token.span.into(), token.kind)).collect();
        assert_eq!(actual, expected, "input: {}", input);
    }

    fn assert_single_token(input: &str, expected_kind: TokenKind) {
        assert_tokens(input, vec![((0, input.len()), expected_kind)]);
    }
}
