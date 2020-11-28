use crate::cursor::Cursor;

pub enum NumLitError {
    DisallowedSign,
    DisallowedLeadingZero,
    NoDigitNearUnderscore,
    ExpectedDigit,
    Unrepresentable,
}

pub enum NumLit {
    Int(i64),
    Float(f64),
}

pub(crate) struct NumLitParser<'c, 's> {
    cursor: &'c mut Cursor<'s>,
    buf: String,
}

impl<'c, 's> NumLitParser<'c, 's> {
    pub(crate) fn new(cursor: &'c mut Cursor<'s>) -> Self {
        Self { cursor, buf: String::new() }
    }

    pub(crate) fn eat_number(&mut self) -> Option<Result<NumLit, NumLitError>> {
        let sign = self.eat_sign();

        if self.cursor.eat_keyword("inf") {
            return Some(Ok(NumLit::Float(sign.map(f64::from).unwrap_or(1.0) * f64::INFINITY)))
        }
        if self.cursor.eat_keyword("nan") {
            let nan = if sign.map(i8::is_positive).unwrap_or(true) {
                f64::NAN
            } else {
                -f64::NAN // 1.0 * f64::NAN doesnt yield negative nan :D
            };
            return Some(Ok(NumLit::Float(nan)))
        }

        match self.cursor.peek_two() {
            Some(('0', 'x')) => return Some(self.expect_exotic_radix_int(16)),
            Some(('0', 'o')) => return Some(self.expect_exotic_radix_int(8)),
            Some(('0', 'b')) => return Some(self.expect_exotic_radix_int(2)),
            Some(('0', '0'..='9')) | Some(('0', '_')) => {
                self.cursor.one();
                return Some(Err(NumLitError::DisallowedLeadingZero))
            }
            _ => {}
        }

        match (self.eat_digits(10), sign) {
            (Ok(true), _) => {}
            (Ok(false), Some(_sign)) => return Some(Err(NumLitError::ExpectedDigit)),
            (Ok(false), None) => return None,
            (Err(err), _) => return Some(Err(err)),
        }

        Some(match self.eat_dot_and_or_exponent() {
            Ok(true) => match self.buf.parse::<f64>() {
                Ok(float) if float.is_finite() => Ok(NumLit::Float(float)),
                _ => Err(NumLitError::Unrepresentable),
            }
            Ok(false) => self.buf.parse::<i64>().map(NumLit::Int).map_err(|_| NumLitError::Unrepresentable),
            Err(err) => Err(err),
        })
    }

    fn expect_exotic_radix_int(&mut self, radix: u32) -> Result<NumLit, NumLitError> {
        if !self.buf.is_empty() {
            debug_assert!(matches!(self.buf.as_str(), "+" | "-"));
            return Err(NumLitError::DisallowedSign);
        }
        self.cursor.two();
        self.expect_digits(radix)?;
        i64::from_str_radix(&self.buf, radix).map(NumLit::Int).map_err(|_| NumLitError::Unrepresentable)
    }

    fn eat_dot_and_or_exponent(&mut self) -> Result<bool, NumLitError> {
        let has_dot = self.cursor.eatc('.');
        if has_dot {
            self.buf.push('.');
            self.expect_digits(10)?;
        }

        let has_exponent = self.cursor.eatc('E') || self.cursor.eatc('e');
        if has_exponent {
            self.buf.push('E');
            self.eat_sign();
            self.expect_digits(10)?;
        }
        Ok(has_dot || has_exponent)
    }

    fn eat_sign(&mut self) -> Option<i8> {
        let (pos_or_neg_one, sign_char) = match self.cursor.peek_one()? {
            '+' => (1, '+'),
            '-' => (-1, '-'),
            _ => return None,
        };
        self.cursor.one();
        self.buf.push(sign_char);
        Some(pos_or_neg_one)
    }

    fn expect_digits(&mut self, radix: u32) -> Result<(), NumLitError> {
        if !self.eat_digits(radix)? {
            return Err(NumLitError::ExpectedDigit)
        }
        Ok(())
    }

    fn eat_digits(&mut self, radix: u32) -> Result<bool, NumLitError> {
        enum State {
            Begin,
            AteDigit,
            AteUnderscore,
        }

        let mut loop_state = State::Begin;
        while let Some(ch) = self.cursor.peek_one() {
            loop_state = match ch {
                '_' => match loop_state {
                    State::Begin | State::AteUnderscore => {
                        self.cursor.one();
                        return Err(NumLitError::NoDigitNearUnderscore)
                    }
                    State::AteDigit => State::AteUnderscore,
                },
                _ if ch.is_digit(radix) => {
                    self.buf.push(ch);
                    State::AteDigit
                }
                _ => break,
            };
            self.cursor.one();
        }
        match loop_state {
            State::Begin => Ok(false),
            State::AteUnderscore => Err(NumLitError::NoDigitNearUnderscore),
            State::AteDigit => Ok(true),
        }
    }
}
