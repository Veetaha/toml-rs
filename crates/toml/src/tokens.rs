use std::{borrow::Cow, iter, str};
pub(crate) use toml_lexer::{HexLen, Span, QuotesLen};

// Entirely wellformed token of TOML language
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum Token<'s> {
    Whitespace(&'s str),
    Newline,
    Comment(&'s str),

    Equals,
    Period,
    Comma,
    Colon,
    Plus,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,

    Keylike(&'s str),
    String {
        src: &'s str,
        val: Cow<'s, str>,
        multiline: bool,
    },
}

impl Token<'_> {
    pub(crate) fn describe(&self) -> &'static str {
        match *self {
            Token::Keylike(_) => "an identifier",
            Token::Equals => "an equals",
            Token::Period => "a period",
            Token::Comment(_) => "a comment",
            Token::Newline => "a newline",
            Token::Whitespace(_) => "whitespace",
            Token::Comma => "a comma",
            Token::RightBrace => "a right brace",
            Token::LeftBrace => "a left brace",
            Token::RightBracket => "a right bracket",
            Token::LeftBracket => "a left bracket",
            Token::String { multiline, .. } => {
                if multiline {
                    "a multiline string"
                } else {
                    "a string"
                }
            }
            Token::Colon => "a colon",
            Token::Plus => "a plus",
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) enum Error {
    InvalidCharInString(usize, char),
    InvalidShorthandEscape(usize, Option<char>),
    NotEnoughDigitsInHex {
        at: usize,
        expected: HexLen,
        actual: u32,
    },
    InvalidEscapeValue(usize, u32),
    UnterminatedString(usize),
    NoNewlineInTrimmedWhitespace(usize),
    Unexpected(usize, char),
    NewlineInTableKey(usize),
    MultilineStringKey(usize),
    EmptyTableKey(usize),
    Wanted {
        at: usize,
        expected: &'static str,
        found: &'static str,
    },
}

/// Error-reluctant tokenizer. It bails upon the first error detected
/// in the input TOML source string. We build it on top of error-resilient
/// one which is very generic on purpose and resides in `toml_lexer` crate.
#[derive(Clone)]
pub(crate) struct Tokenizer<'s> {
    inner: toml_lexer::Tokenizer<'s>,
    lookahead: Option<Result<Option<(Span, Token<'s>)>, Error>>,
}

impl<'s> Tokenizer<'s> {
    pub(crate) fn new(input: &'s str) -> Tokenizer<'s> {
        Tokenizer {
            inner: toml_lexer::Tokenizer::new(input),
            lookahead: None,
        }
    }

    pub(crate) fn input(&self) -> &'s str {
        self.inner.input()
    }

    pub(crate) fn peek(&mut self) -> Result<Option<(Span, Token<'s>)>, Error> {
        if matches!(self.lookahead, None) {
            let next = self.next();
            // next() may fill `.lookahead` with the token in unescape_next_str_lit()
            return self.lookahead.get_or_insert(next).clone();
        }

        match self.lookahead {
            Some(ref mut it) => it.clone(),
            None => unreachable!("Ownership workaround :D copied from Option::get_or_insert_with()"),
        }
    }

    pub fn current_index(&self) -> usize {
        self.inner.current_index()
    }

    fn input_slice(&self, span: Span) -> &'s str {
        &self.inner.input()[span.start..span.end]
    }

    pub(crate) fn next(&mut self) -> Result<Option<(Span, Token<'s>)>, Error> {
        match self.lookahead.take() {
            Some(it) => return it,
            None => {}
        }

        let token = match self.inner.next() {
            Some(it) => it,
            None => return Ok(None),
        };

        let (leading_quotes_span, leading_quotes) = match self.into_non_str_lit(token) {
            Ok(non_str_lit) => return non_str_lit,
            Err(it) => it
        };

        let quotes = match leading_quotes {
            toml_lexer::StrLitSubtoken::LeadingQuotes(it) => it,
            _ => unreachable!("String always begins with leading quotes!")
        };

        self.unescape_next_str_lit(leading_quotes_span, quotes)
    }

    fn into_non_str_lit(&self, token: toml_lexer::Token) -> Result<Result<Option<(Span, Token<'s>)>, Error>, (Span, toml_lexer::StrLitSubtoken)> {
        let wellformed_token = match token.kind {
            toml_lexer::TokenKind::Whitespace => Token::Whitespace(self.input_slice(token.span)),
            toml_lexer::TokenKind::Newline => Token::Newline,
            toml_lexer::TokenKind::Comment => Token::Comment(self.input_slice(token.span)),
            toml_lexer::TokenKind::Equals => Token::Equals,
            toml_lexer::TokenKind::Period => Token::Period,
            toml_lexer::TokenKind::Comma => Token::Comma,
            toml_lexer::TokenKind::Colon => Token::Colon,
            toml_lexer::TokenKind::Plus => Token::Plus,
            toml_lexer::TokenKind::LeftBrace => Token::LeftBrace,
            toml_lexer::TokenKind::RightBrace => Token::RightBrace,
            toml_lexer::TokenKind::LeftBracket => Token::LeftBracket,
            toml_lexer::TokenKind::RightBracket => Token::RightBracket,
            toml_lexer::TokenKind::Keylike => Token::Keylike(self.input_slice(token.span)),
            toml_lexer::TokenKind::Unknown => {
                return Ok(Err(Error::Unexpected(token.span.start, self.input().chars().next().unwrap())));
            }
            toml_lexer::TokenKind::StrLitSubtoken(it) => {
                return Err((token.span, it))
            }
        };

        Ok(Ok(Some((token.span, wellformed_token))))
    }

    fn unescape_next_str_lit(&mut self, leading_quotes_span: Span, quotes: toml_lexer::Quotes) -> Result<Option<(Span, Token<'s>)>, Error> {
        let mut unescaped = MaybeEscaped::new(&self.input()[leading_quotes_span.start..]);

        let end = loop {
            let token = match self.inner.next() {
                Some(it) => it,
                None => break self.input().len(),
            };

            match token.kind {
                toml_lexer::TokenKind::StrLitSubtoken(it) => {
                    unescaped.append(match it {
                        toml_lexer::StrLitSubtoken::UnicodeEscape { unescaped, kind } => match unescaped {
                            toml_lexer::UnicodeEscape::Valid(ch) => ch,
                            toml_lexer::UnicodeEscape::NotEnoughDigits(actual) => {
                                return Err(Error::NotEnoughDigitsInHex {
                                    at: token.span.start,
                                    actual,
                                    expected: kind,
                                })
                            }
                            toml_lexer::UnicodeEscape::InvalidScalarValue(val) => {
                                return Err(Error::InvalidEscapeValue(token.span.start, val))
                            }
                        },
                        toml_lexer::StrLitSubtoken::ShorthandEscape(ch) => match ch {
                            Ok(ch) => ch,
                            Err(ch) => return Err(Error::InvalidShorthandEscape(token.span.start, ch))
                        },
                        toml_lexer::StrLitSubtoken::Char(ch) => ch,
                        toml_lexer::StrLitSubtoken::BannedChar(it) => {
                            return Err(Error::InvalidCharInString(token.span.start, it))
                        }
                        toml_lexer::StrLitSubtoken::TrimmedWhitespace {
                            includes_newline: false,
                        } => {
                            return Err(Error::NoNewlineInTrimmedWhitespace(token.span.start))
                        }
                        toml_lexer::StrLitSubtoken::TrimmedWhitespace {
                            includes_newline: true,
                        }
                        | toml_lexer::StrLitSubtoken::TrailingQuotes
                        | toml_lexer::StrLitSubtoken::LeadingQuotes { .. }
                        | toml_lexer::StrLitSubtoken::LeadingNewline => {
                            unescaped.skip(token.span);
                            continue;
                        }
                    })
                }
                _ => {
                    let end = token.span.end;
                    // Remember the token, to be returned next
                    self.lookahead = Some(self.into_non_str_lit(token).expect("non string literal subtoken"));
                    break end;
                }
            }
        };

        let span = Span {
            start: leading_quotes_span.start,
            end
        };

        Ok(Some((span, Token::String {
            src: self.input_slice(span),
            val: unescaped.into_cow(),
            multiline: quotes.len == QuotesLen::X3,
        })))
    }

    pub(crate) fn eat(&mut self, expected: Token<'s>) -> Result<bool, Error> {
        self.eat_spanned(expected).map(|s| s.is_some())
    }

    /// Eat a value, returning it's span if it was consumed.
    pub(crate) fn eat_spanned(&mut self, expected: Token<'s>) -> Result<Option<Span>, Error> {
        let span = match self.peek()? {
            Some((span, ref found)) if expected == *found => span,
            Some(_) => return Ok(None),
            None => return Ok(None),
        };

        drop(self.next());
        Ok(Some(span))
    }

    pub(crate) fn expect(&mut self, expected: Token<'s>) -> Result<(), Error> {
        // ignore span
        let _ = self.expect_spanned(expected)?;
        Ok(())
    }

    /// Expect the given token returning its span.
    pub(crate) fn expect_spanned(&mut self, expected: Token<'s>) -> Result<Span, Error> {
        let current = self.current_index();
        match self.next()? {
            Some((span, found)) => {
                if expected == found {
                    Ok(span)
                } else {
                    Err(Error::Wanted {
                        at: current,
                        expected: expected.describe(),
                        found: found.describe(),
                    })
                }
            }
            None => Err(Error::Wanted {
                at: self.input().len(),
                expected: expected.describe(),
                found: "eof",
            }),
        }
    }

    pub(crate) fn table_key(&mut self) -> Result<(Span, Cow<'s, str>), Error> {
        let current = self.current_index();
        match self.next()? {
            Some((span, Token::Keylike(k))) => Ok((span, k.into())),
            Some((
                span,
                Token::String {
                    src,
                    val,
                    multiline,
                },
            )) => {
                let offset = self.substr_offset(src);
                if multiline {
                    return Err(Error::MultilineStringKey(offset));
                }
                if val == "" {
                    return Err(Error::EmptyTableKey(offset));
                }
                match src.find('\n') {
                    None => Ok((span, val)),
                    Some(i) => Err(Error::NewlineInTableKey(offset + i)),
                }
            }
            Some((_, other)) => Err(Error::Wanted {
                at: current,
                expected: "a table key",
                found: other.describe(),
            }),
            None => Err(Error::Wanted {
                at: self.input().len(),
                expected: "a table key",
                found: "eof",
            }),
        }
    }

    pub(crate) fn eat_whitespace(&mut self) -> Result<(), Error> {
        while let Ok(Some((_, Token::Whitespace(_)))) = self.peek() {
            drop(self.next());
        }
        // TODO: rethink whether this method should return Result<>
        Ok(())
    }

    pub(crate) fn eat_comment(&mut self) -> Result<bool, Error> {
        if !matches!(self.peek()?, Some((_, Token::Comment(_)))) {
            return Ok(false);
        }
        drop(self.next());
        self.eat_newline_or_eof().map(|()| true)
    }

    pub(crate) fn eat_newline_or_eof(&mut self) -> Result<(), Error> {
        let current = self.current_index();
        match self.next()? {
            None | Some((_, Token::Newline)) => Ok(()),
            Some((_, other)) => Err(Error::Wanted {
                at: current,
                expected: "newline",
                found: other.describe(),
            }),
        }
    }

    pub(crate) fn skip_to_newline(&mut self) {
        while !matches!(self.peek(), Err(_) | Ok(None) | Ok(Some((_, Token::Newline)))) {
            drop(self.next());
        }
    }

    pub(crate) fn substr_offset(&self, s: &'s str) -> usize {
        assert!(s.len() <= self.input().len());
        let a = self.input().as_ptr() as usize;
        let b = s.as_ptr() as usize;
        assert!(a <= b);
        b - a
    }
}

#[derive(Debug)]
enum MaybeEscaped<'s> {
    NotEscaped(&'s str, str::CharIndices<'s>, usize),
    Escaped(String),
}

// TODO: test
impl<'s> MaybeEscaped<'s> {
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

    fn into_cow(self) -> Cow<'s, str> {
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

// #[cfg(test)]
// mod tests {

//     macro_rules! assert_matches {
//         ($val:expr, $pat:pat) => {{
//             let val = &$val;
//             if !matches!(val, $pat) {
//                 let val_str = stringify!($val);
//                 let pat_str = stringify!($pat);
//                 panic!(
//                     "{} doesn't match the pattern: {}\n actual value: {:?}",
//                     val_str, pat_str, val
//                 );
//             }
//         }};
//     }

//     #[test]
//     fn unescape_borrows_when_possible() {
//         use unescape_str_lit as unescape;

//         assert_matches!(unescape("'abcdef'"), Some(Cow::Borrowed("abcdef")));
//         assert_matches!(unescape("'abcdef"), Some(Cow::Borrowed("abcdef")));
//         assert_matches!(unescape("'''abcdef'"), Some(Cow::Borrowed("abcdef'")));
//         assert_matches!(unescape("'''\nabcdef"), Some(Cow::Borrowed("abcdef")));
//         assert_matches!(
//             unescape("\"\"\"\\ \t \n \t abcdef"),
//             Some(Cow::Borrowed("abcdef"))
//         );
//         assert_matches!(unescape(r#""\\""#), Some(Cow::Borrowed("\\")));
//     }

//     #[test]
//     fn unescape_returns_owned_when_meets_escapes() {
//         use unescape_str_lit as unescape;

//         let t = |input, expected: &str| {
//             let actual = unescape(input);
//             assert_matches!(actual, Some(Cow::Owned(_)));
//             assert_eq!(actual, Some(expected.into()));
//         };

//         t(r#""\t""#, "\t");
//         t(r#""""abc\ a"#, "abca");
//         t(r#""\u1234""#, "\u{1234}");
//     }

//     mod strings {
//         use super::*;
//         use Flags::*;

//         /// B - basic
//         /// L - literal
//         /// S - single-line
//         /// M - multi-line
//         /// T - terminated
//         /// U - unterminated
//         #[derive(Copy, Clone)]
//         enum Flags {
//             BST,
//             BSU,
//             BMT,
//             BMU,
//             LST,
//             LSU,
//             LMT,
//             LMU,
//         }

//         fn str(flags: Flags) -> Token {
//             let (terminated, multiline, kind) = match flags {
//                 BMT => (true, true, StringKind::Basic),
//                 BMU => (false, true, StringKind::Basic),
//                 BST => (true, false, StringKind::Basic),
//                 BSU => (false, false, StringKind::Basic),
//                 LMT => (true, true, StringKind::Literal),
//                 LMU => (false, true, StringKind::Literal),
//                 LST => (true, false, StringKind::Literal),
//                 LSU => (false, false, StringKind::Literal),
//             };
//             String {
//                 kind,
//                 multiline,
//                 terminated,
//             }
//         }

//         fn assert_single_string(flags: Flags, input: &str, expected_unescaped: &str) {
//             assert_single_token(input, str(flags));
//             let unescaped = crate::unescape_str_lit(input).unwrap();
//             assert_eq!(unescaped, expected_unescaped, "input: {{{}}}", input);
//         }

//         fn assert_empty_string(flags: Flags, input: &str) {
//             assert_single_string(flags, input, "");
//         }

//         #[test]
//         fn terminated_empty_strings() {
//             use assert_empty_string as t;

//             t(LST, "''");
//             t(LMT, "''''''");
//             t(LMT, "'''\n'''");

//             t(BST, r#""""#);
//             t(BMT, r#""""""""#);

//             t(BMT, "\"\"\"\n\"\"\"");
//             t(BMT, "\"\"\"\n\\\n  \t\t  \"\"\"");
//         }

//         #[test]
//         fn single_char_strings() {
//             use assert_single_string as t;

//             t(LST, "'a'", "a");
//             t(LST, "' '", " ");
//             t(LST, "'\t'", "\t");
//             t(LMT, "'''a'''", "a");
//             t(LMT, "''' '''", " ");
//             t(LMT, "'''\t'''", "\t");
//             t(LMT, "'''''''", "'");
//             t(BST, r#""a""#, "a");
//             t(BST, r#""\t""#, "\t");
//             t(BST, "\"\t\"", "\t");
//             t(BMT, r#""""a""""#, "a");
//             t(BMT, r#"""""""""#, "\"");
//             t(BMT, r#""""\t""""#, "\t");
//             t(BMT, "\"\"\"\t\"\"\"", "\t");
//             t(BMT, r#""""\"""""#, "\"");
//         }

//         #[test]
//         fn multi_char_strings() {
//             use assert_single_string as t;

//             t(LST, "'ab'", "ab");
//             t(LST, "'\"a'", "\"a");
//             t(LST, "'\\t'", "\\t");

//             t(LMT, "''''''''", "''");
//             t(BMT, r#""""""""""#, "\"\"");

//             t(LMT, "'''\n'a\n'''", "'a\n");
//             t(LMT, "'''a\n'a\r\n'''", "a\n'a\n");
//             t(LST, "'\\U00'", "\\U00");

//             t(BST, r#""\\t""#, "\\t");
//             t(BMT, r#""""\\t""""#, "\\t");
//         }

//         #[test]
//         fn unterminated_strings() {
//             use assert_single_string as t;

//             t(LMU, "'''''", "''");
//             t(BMU, r#"""""""#, "\"\"");
//             t(LMU, "''''", "'");
//             t(BMU, r#""""""#, "\"");

//             t(LSU, "'a", "a");
//             t(LSU, "'\\", "\\");

//             t(BSU, r#""a"#, "a");
//             t(BSU, r#""\"#, "�");
//             t(BSU, r#""\""#, "\"");

//             t(LMU, "'''a", "a");
//             t(LMU, "'''\\", "\\");

//             t(BMU, r#""""a"#, "a");
//             t(BMU, r#""""\"#, "�");
//             t(BMU, r#""""\""#, "\"");

//             assert_tokens("'\\''", vec![((0, 3), str(LST)), ((3, 4), str(LSU))]);
//             assert_tokens(
//                 "'foo\n'",
//                 vec![
//                     ((0, 4), str(LSU)),
//                     ((4, 5), Token::Newline),
//                     ((5, 6), str(LSU)),
//                 ],
//             );
//             assert_tokens(
//                 "\"foo\n\"",
//                 vec![
//                     ((0, 4), str(BSU)),
//                     ((4, 5), Token::Newline),
//                     ((5, 6), str(BSU)),
//                 ],
//             );
//         }

//         #[test]
//         fn with_escapes() {
//             use assert_single_string as t;

//             t(BMT, "\"\"\"\n\t\"\"\"", "\t");
//             t(BMT, "\"\"\"\\\n\"\"\"", "");
//             t(
//                 BMT,
//                 "\"\"\"\\\n     \t   \t  \\\r\n  \t \n  \t \r\n\"\"\"",
//                 "",
//             );
//             t(BST, r#""\r""#, "\r");
//             t(BST, r#""\n""#, "\n");
//             t(BST, r#""\b""#, "\u{8}");
//             t(BST, r#""a\fa""#, "a\u{c}a");
//             t(BST, r#""\"a""#, "\"a");
//             t(BMT, "\"\"\"\na\"\"\"", "a");
//             t(BMT, r#""""a\"""b""""#, "a\"\"\"b");
//         }
//     }
// }
