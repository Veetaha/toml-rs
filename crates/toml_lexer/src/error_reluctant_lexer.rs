use crate::{error_resilient_lexer as error_res, EscapeErrorKind, Span};
use std::borrow::Cow;

// Entirely wellformed token of TOML language
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Token<'a> {
    Whitespace(&'a str),
    Newline,
    Comment(&'a str),

    Equals,
    Period,
    Comma,
    Colon,
    Plus,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,

    Keylike(&'a str),
    String {
        src: &'a str,
        val: Cow<'a, str>,
        multiline: bool,
    },
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Error {
    pub kind: ErrorKind,
    pub at: usize,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ErrorKind {
    Escape(EscapeErrorKind),
    Unexpected(char),
}

/// Error-reluctant tokenizer. It bails upon the first error detected
/// int the input TOML source string.
#[derive(Clone)]
pub struct Tokenizer<'a>(error_res::Tokenizer<'a>);

impl<'a> Tokenizer<'a> {
    pub fn new(input: &'a str) -> Tokenizer<'a> {
        Tokenizer(error_res::Tokenizer::new(input))
    }

    pub fn input(&self) -> &'a str {
        self.0.input()
    }

    /// Returns the next token in the input, if the token is malformed
    /// returns an error describing it. When reached the end of input
    /// returns `Ok(None)`
    ///
    /// ```
    /// use toml_lexer::error_reluctant_lexer::Tokenizer as Tokenizer;
    /// use toml_lexer::{EscapeErrorKind, error_reluctant_lexer::{Error, ErrorKind}};
    ///
    /// let mut tokenizer = Tokenizer::new("abc = 'ff ");
    /// loop {
    ///     match tokenizer.next() {
    ///         Err(err) => {
    ///             let kind = ErrorKind::Escape(EscapeErrorKind::UnterminatedString);
    ///             assert_eq!(err, Error { at: 6, kind });
    ///             break;
    ///         }
    ///         Ok(Some(token)) => eprintln!("token: {:?}", token),
    ///         Ok(None) => {
    ///             eprintln!("end of input");
    ///             break;
    ///         }
    ///     }
    /// }
    /// ```
    ///
    pub fn next(&mut self) -> Result<Option<(Span, Token<'a>)>, Error> {
        let (span, maybe_malformed_token) = match self.0.next() {
            Some(it) => it,
            None => return Ok(None),
        };

        Ok(Some((
            span,
            self.try_into_wellformed_token(span, maybe_malformed_token)?,
        )))
    }

    pub fn current_index(&self) -> usize {
        self.0.current_index()
    }

    fn input_slice(&self, span: Span) -> &'a str {
        &self.0.input()[span.start..span.end]
    }

    fn try_into_wellformed_token(
        &self,
        span: Span,
        token: error_res::Token,
    ) -> Result<Token<'a>, Error> {
        Ok(match token {
            error_res::Token::Whitespace => Token::Whitespace(self.input_slice(span)),
            error_res::Token::Newline => Token::Newline,
            error_res::Token::Comment => Token::Comment(self.input_slice(span)),
            error_res::Token::Equals => Token::Equals,
            error_res::Token::Period => Token::Period,
            error_res::Token::Comma => Token::Comma,
            error_res::Token::Colon => Token::Colon,
            error_res::Token::Plus => Token::Plus,
            error_res::Token::LeftBrace => Token::LeftBrace,
            error_res::Token::RightBrace => Token::RightBrace,
            error_res::Token::LeftBracket => Token::LeftBracket,
            error_res::Token::RightBracket => Token::RightBracket,
            error_res::Token::Keylike => Token::Keylike(self.input_slice(span)),
            error_res::Token::Unknown(ch) => {
                return Err(Error {
                    kind: ErrorKind::Unexpected(ch),
                    at: span.start,
                })
            }
            error_res::Token::String {
                kind: _,
                multiline,
                terminated,
            } => {
                if !terminated {
                    return Err(Error {
                        kind: ErrorKind::Escape(EscapeErrorKind::UnterminatedString),
                        at: span.start,
                    });
                }

                let src = self.input_slice(span);
                let unescaped = crate::try_unescape_str_lit(src)
                    .expect("The string literal must have leading quotes")
                    .map_err(|err| Error {
                        kind: ErrorKind::Escape(err.kind),
                        at: err.at + span.start,
                    })?;

                Token::String {
                    src,
                    val: unescaped,
                    multiline,
                }
            }
        })
    }
}
