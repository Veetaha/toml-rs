use crate::Span;

/// Forward-only cursor into a string that normalizes `\r\n` to `\n`
#[derive(Debug, Clone)]
pub(crate) struct Cursor<'a> {
    string: &'a str,
    chars: CrlfFold<'a>,
}

impl<'a> Cursor<'a> {
    pub(crate) fn new(string: &str) -> Cursor<'_> {
        Cursor {
            string,
            chars: CrlfFold {
                chars: string.char_indices(),
            },
        }
    }

    pub(crate) fn string(&self) -> &'a str {
        self.string
    }

    /// Returns the already consumed slice of the string (i.e. from index 0 to last consumed char).
    pub(crate) fn consumed_slice(&self) -> &'a str {
        let span = self.step_span(0);
        &self.string[0..span.end]
    }

    pub(crate) fn eatc(&mut self, ch: char) -> bool {
        match self.peek_one() {
            Some(ch2) if ch == ch2 => {
                self.one();
                true
            }
            _ => false,
        }
    }

    /// Calculate the span of the currently analyzed token.
    pub(crate) fn step_span(&self, start: usize) -> Span {
        Span {
            start,
            end: self.current_index(),
        }
    }

    /// Peek one char without consuming it.
    pub(crate) fn peek_one(&self) -> Option<char> {
        Some(self.peek_one_with_index()?.1)
    }

    pub(crate) fn peek_two(&self) -> Option<(char, char)> {
        let mut chars = self.chars.clone();
        Some((chars.next()?.1, chars.next()?.1))
    }

    /// Peek one char without consuming it.
    pub(crate) fn peek_one_with_index(&self) -> Option<(usize, char)> {
        self.chars.clone().next()
    }

    /// Take one char.
    pub(crate) fn one(&mut self) -> Option<char> {
        Some(self.one_with_index()?.1)
    }

    /// Take one char and also return its index.
    pub(crate) fn one_with_index(&mut self) -> Option<(usize, char)> {
        self.chars.next()
    }

    pub(crate) fn current_index(&self) -> usize {
        self.peek_one_with_index()
            .map_or_else(|| self.string.len(), |(i, _)| i)
    }
}

#[derive(Debug, Clone)]
struct CrlfFold<'a> {
    chars: std::str::CharIndices<'a>,
}

impl<'a> Iterator for CrlfFold<'a> {
    type Item = (usize, char);

    fn next(&mut self) -> Option<(usize, char)> {
        self.chars.next().map(|(i, c)| {
            if c == '\r' {
                let mut attempt = self.chars.clone();
                if let Some((_, '\n')) = attempt.next() {
                    self.chars = attempt;
                    return (i, '\n');
                }
            }
            (i, c)
        })
    }
}
