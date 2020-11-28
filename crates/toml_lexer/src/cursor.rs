use crate::Span;

/// Forward-only cursor into a string that normalizes `\r\n` to `\n`
#[derive(Debug, Clone)]
pub(crate) struct Cursor<'s> {
    string: &'s str,
    chars: CrlfFold<'s>,
}

impl<'s> Cursor<'s> {
    pub(crate) fn new(string: &str) -> Cursor<'_> {
        Cursor {
            string,
            chars: CrlfFold {
                chars: string.char_indices(),
            },
        }
    }

    pub(crate) fn string(&self) -> &'s str {
        self.string
    }

    /// Returns the already consumed slice of the string (i.e. from index 0 to last consumed char).
    pub(crate) fn consumed_slice(&self) -> &'s str {
        let span = self.span_from(0);
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

    pub(crate) fn eat_keyword(&mut self, keyword: &str) -> bool {
        debug_assert!(keyword.chars().all(|ch| ch.is_ascii_alphabetic()));

        if self.chars.chars.as_str().starts_with(keyword) {
            for _ in 0..keyword.len() {
                self.one();
            }
            return true;
        }
        false
    }


    /// Calculate the span of the currently analyzed token.
    pub(crate) fn span_from(&self, start: usize) -> Span {
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
        let ch1 = chars.next()?.1;
        let ch2 = chars.next()?.1;
        Some((ch1, ch2))
    }

    /// Peek one char without consuming it.
    pub(crate) fn peek_one_with_index(&self) -> Option<(usize, char)> {
        self.chars.clone().next()
    }

    /// Take two chars.
    pub(crate) fn two(&mut self) -> Option<(char, char)> {
        let pair = self.peek_two();
        if let Some(_) = pair {
            self.one();
            self.one();
        }
        pair
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
struct CrlfFold<'s> {
    chars: std::str::CharIndices<'s>,
}

impl<'s> Iterator for CrlfFold<'s> {
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
