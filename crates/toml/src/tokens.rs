use std::borrow::Cow;
use toml_lexer::error_reluctant_lexer;
pub(crate) use toml_lexer::{
    error_reluctant_lexer::{Error as LexerError, ErrorKind as LexerErrorKind, Token},
    EscapeErrorKind, HexLen, Span,
};

pub(crate) trait Describe {
    fn describe(&self) -> &'static str;
}

impl Describe for Token<'_> {
    fn describe(&self) -> &'static str {
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

pub(crate) enum Error {
    Lexer(error_reluctant_lexer::Error),
    NewlineInTableKey(usize),
    MultilineStringKey(usize),
    EmptyTableKey(usize),
    Wanted {
        at: usize,
        expected: &'static str,
        found: &'static str,
    },
}

impl From<error_reluctant_lexer::Error> for Error {
    fn from(err: error_reluctant_lexer::Error) -> Error {
        Error::Lexer(err)
    }
}

// TODO: use std::iter::Peekable ?
#[derive(Clone)]
pub(crate) struct Tokenizer<'a>(error_reluctant_lexer::Tokenizer<'a>);

impl<'a> Tokenizer<'a> {
    pub(crate) fn new(input: &'a str) -> Tokenizer<'a> {
        Tokenizer(error_reluctant_lexer::Tokenizer::new(input))
    }

    pub(crate) fn next(&mut self) -> Result<Option<(Span, Token<'a>)>, Error> {
        self.0.next().map_err(Into::into)
    }

    pub(crate) fn peek(&self) -> Result<Option<(Span, Token<'a>)>, Error> {
        self.0.clone().next().map_err(Into::into)
    }

    pub(crate) fn current_index(&self) -> usize {
        self.0.current_index()
    }

    pub(crate) fn input(&self) -> &'a str {
        self.0.input()
    }

    pub(crate) fn eat(&mut self, expected: Token<'a>) -> Result<bool, Error> {
        self.eat_spanned(expected).map(|s| s.is_some())
    }

    /// Eat a value, returning it's span if it was consumed.
    pub(crate) fn eat_spanned(&mut self, expected: Token<'a>) -> Result<Option<Span>, Error> {
        let span = match self.peek()? {
            Some((span, ref found)) if expected == *found => span,
            Some(_) => return Ok(None),
            None => return Ok(None),
        };

        drop(self.next());
        Ok(Some(span))
    }

    pub(crate) fn expect(&mut self, expected: Token<'a>) -> Result<(), Error> {
        // ignore span
        let _ = self.expect_spanned(expected)?;
        Ok(())
    }

    /// Expect the given token returning its span.
    pub(crate) fn expect_spanned(&mut self, expected: Token<'a>) -> Result<Span, Error> {
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

    pub(crate) fn table_key(&mut self) -> Result<(Span, Cow<'a, str>), Error> {
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
        // TODO: rethink wether this method should return Result<>
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

    pub(crate) fn substr_offset(&self, s: &'a str) -> usize {
        assert!(s.len() <= self.input().len());
        let a = self.input().as_ptr() as usize;
        let b = s.as_ptr() as usize;
        assert!(a <= b);
        b - a
    }
}
