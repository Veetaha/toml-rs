use crate::cursor::Cursor;

pub enum NumOrDateError {
    Empty,
    DisallowedSign,
    DisallowedLeadingZero,
    NoDigitNearUnderscore,
}

pub enum NumOrDate {
    Datetime,
    Int(i64),
    Float(f64),
}


fn eat_num_or_date(str: &str) -> Result<(usize, NumOrDate), NumOrDateError> {
    NumOrDateParser(Cursor::new(str)).parse()
}

struct NumOrDateParser<'s>(Cursor<'s>);

impl<'s> NumOrDateParser<'s> {

    fn parse(&mut self) -> Result<(usize, NumOrDate), NumOrDateError> {
        let input = self.0.string();

        if input.contains('T')
            || input.contains('t')
            || (
                input.get(1..).map(|it| it.contains('-')) == Some(true) &&
                !input.contains("e-") &&
                !input.contains("E-")
            )
        {
            self.datetime(false)
        } else if self.0.eatc(':') { // TODO:
            self.datetime(true)
        } else {
            self.number()
        }
    }

    fn number(&mut self) -> Result<(usize, NumOrDate), NumOrDateError> {
        {
            let exotic_radix_int = |radix| {
                self.0.two();
                self.integer(radix).map(NumOrDate::Int)
            };
            match self.0.peek_two() {
                Some(('0', 'x')) => return exotic_radix_int(16),
                Some(('0', 'o')) => return exotic_radix_int(8),
                Some(('0', 'b')) => return exotic_radix_int(2),
                Some(_) => {}
                None => return Err(NumOrDateError::Empty),
            }
        }

        let s = self.0.string();

        if s.contains('e') || s.contains('E') {
            self.float(s, None)
        } else if self.0.eatc('.') {
            // match self.next()? {
                // Some((Span { start, end }, Token::Keylike(after))) => {
                    return self.float(s, Some(after)).map(NumOrDate::Float);
                // }
                // _ => Err(self.error(at, ErrorKind::NumberInvalid)),
            // }
        }

        if s.starts_with("inf") {
            return Ok(("inf".len(), f64::INFINITY))
        }
        if s.starts_with("-inf") {
            return Ok(("-inf".len(), f64::NEG_INFINITY))
        }
        if s.starts_with("nan") {
            return Ok(("nan".len(), f64::NAN))
        }
        if s.starts_with("-nan") {
            return Ok(("-nan".len(), -f64::NAN))
        }

        self.integer(s, 10)
    }

    fn integer(&self, radix: u32) -> Result<NumOrDate, NumOrDateError> {
        let allow_sign = radix == 10;
        let allow_leading_zeros = radix != 10;
        let (prefix, suffix) = self
            .parse_integer(allow_sign, allow_leading_zeros, radix)?;

        let start = self.tokens.substr_offset(s);
        if suffix != "" {
            return Err(self.error(start, ErrorKind::NumberInvalid));
        }
        i64::from_str_radix(&prefix.replace("_", "").trim_start_matches('+'), radix)
            .map_err(|_e| self.error(start, ErrorKind::NumberInvalid))
    }

    fn parse_integer(
        &self,
        allow_sign: bool,
        allow_leading_zeros: bool,
        radix: u32,
    ) -> Result<&'s str, NumOrDateError> {
        let start = self.0.current_index();

        if self.0.eatc('+') || self.0.eatc('-') && !allow_sign {
            return Err(NumOrDateError::DisallowedSign);
        }

        while self.0.eatc('0') {
            // ...
        }

        if self.0.current_index() - start > 1 && !allow_leading_zeros {
            return Err(NumOrDateError::DisallowedLeadingZero);
        }

        let mut prev_is_digit = false;
        while let Some(ch) = self.0.peek_one() {
            prev_is_digit = match (ch, prev_is_digit) {
                ('_', false) => return Err(NumOrDateError::NoDigitNearUnderscore),
                ('_', true) => false,
                _ if ch.is_digit(radix) => true,
                _ => break,
            };
            self.0.one();
        }
        if !prev_is_digit {
            return Err(NumOrDateError::NoDigitNearUnderscore);
        }
        self.0.consumed_slice()[start..]
    }

    fn float(&mut self, after_decimal: Option<&'_ str>) -> Result<f64, NumOrDateError> {
        let (integral, mut suffix) = self.parse_integer(true, false, 10)?;
        let start = self.tokens.substr_offset(integral);

        let mut fraction = None;
        if let Some(after) = after_decimal {
            if suffix != "" {
                return Err(self.error(start, ErrorKind::NumberInvalid));
            }
            let (a, b) = self.parse_integer(after, false, true, 10)?;
            fraction = Some(a);
            suffix = b;
        }

        let mut exponent = None;
        if suffix.starts_with('e') || suffix.starts_with('E') {
            let (a, b) = if suffix.len() == 1 {
                self.eat(Token::Plus)?;
                match self.next()? {
                    Some((_, Token::Keylike(s))) => self.parse_integer(s, false, true, 10)?,
                    _ => return Err(self.error(start, ErrorKind::NumberInvalid)),
                }
            } else {
                self.parse_integer(&suffix[1..], true, true, 10)?
            };
            if b != "" {
                return Err(self.error(start, ErrorKind::NumberInvalid));
            }
            exponent = Some(a);
        } else if !suffix.is_empty() {
            return Err(self.error(start, ErrorKind::NumberInvalid));
        }

        let mut number = integral
            .trim_start_matches('+')
            .chars()
            .filter(|c| *c != '_')
            .collect::<String>(); // TODO: make this thread local?
        if let Some(fraction) = fraction {
            number.push_str(".");
            number.extend(fraction.chars().filter(|c| *c != '_'));
        }
        if let Some(exponent) = exponent {
            number.push_str("E");
            number.extend(exponent.chars().filter(|c| *c != '_'));
        }
        number
            .parse()
            .map_err(|_e| self.error(start, ErrorKind::NumberInvalid))
            .and_then(|n: f64| {
                if n.is_finite() {
                    Ok(n)
                } else {
                    Err(self.error(start, ErrorKind::NumberInvalid))
                }
            })
    }

    fn datetime(
        &mut self,
        colon_eaten: bool,
    ) -> Result<(usize, NumOrDate), NumOrDateError> {
        let start = self.tokens.substr_offset(date);

        // Check for space separated date and time.
        let mut lookahead = self.tokens.clone();
        if let Ok(Some((_, Token::Whitespace(" ")))) = lookahead.next() {
            // Check if hour follows.
            if let Ok(Some((_, Token::Keylike(_)))) = lookahead.next() {
                self.next()?; // skip space
                self.next()?; // skip keylike hour
            }
        }

        if colon_eaten || self.eat(Token::Colon)? {
            // minutes
            match self.next()? {
                Some((_, Token::Keylike(_))) => {}
                _ => return Err(self.error(start, ErrorKind::DateInvalid)),
            }
            // Seconds
            self.expect(Token::Colon)?;
            match self.next()? {
                Some((Span { end, .. }, Token::Keylike(_))) => {
                    span.end = end;
                }
                _ => return Err(self.error(start, ErrorKind::DateInvalid)),
            }
            // Fractional seconds
            if self.eat(Token::Period)? {
                match self.next()? {
                    Some((Span { end, .. }, Token::Keylike(_))) => {
                        span.end = end;
                    }
                    _ => return Err(self.error(start, ErrorKind::DateInvalid)),
                }
            }

            // offset
            if self.eat(Token::Plus)? {
                match self.next()? {
                    Some((Span { end, .. }, Token::Keylike(_))) => {
                        span.end = end;
                    }
                    _ => return Err(self.error(start, ErrorKind::DateInvalid)),
                }
            }
            if self.eat(Token::Colon)? {
                match self.next()? {
                    Some((Span { end, .. }, Token::Keylike(_))) => {
                        span.end = end;
                    }
                    _ => return Err(self.error(start, ErrorKind::DateInvalid)),
                }
            }
        }

        let end = self.tokens.current_index();
        Ok((span, &self.tokens.input()[start..end]))
    }
