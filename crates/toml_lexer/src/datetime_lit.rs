use crate::{cursor::Cursor};

pub enum DatetimeLitError {
    ExpectedDigit,
    ExpectedDash,
    ExpectedColon,
    OutOfRangeHour(u8),
    OutOfRangeMinute(u8),
    OutOfRangeSecond(u8),
    OutOfRangeMonth(u8),
    OutOfRangeDay(u8),
}

#[derive(PartialEq, Clone)]
pub enum DatetimeLit {
    OffsetDatetime(Date, Time, Offset),
    LocalDatetime(Date, Time),
    LocalDate(Date),
    LocalTime(Time)
}

#[derive(PartialEq, Clone)]
pub struct Date {
    year: u16,
    month: u8,
    day: u8,
}

#[derive(PartialEq, Clone)]
pub struct Time {
    hour: u8,
    minute: u8,
    second: u8,
    nanosecond: u32,
}

#[derive(PartialEq, Clone)]
pub enum Offset {
    Z,
    Custom { hours: i8, minutes: u8 },
}

pub(crate) struct DatetimeParser<'c, 's>(&'c mut Cursor<'s>);

impl<'c, 's> DatetimeParser<'c, 's> {
    pub(crate) fn new(cursor: &'c mut Cursor<'s>) -> Self {
        Self(cursor)
    }

    pub(crate) fn eat_datetime(&mut self) -> Option<Result<DatetimeLit, DatetimeLitError>> {
        let first_digit = self.eat_digit()?;
        Some(self.eat_datetime_inner(first_digit))
    }

    fn eat_datetime_inner(&mut self, digit1: u8) -> Result<DatetimeLit, DatetimeLitError> {
        // Accepted formats:
        //
        // 0000-00-00T00:00:00.00+00:00   // offset date-time
        // 0000-00-00T00:00:00.00Z
        // 0000-00-00T00:00:00.00         // local date-time
        // 0000-00-00                     // local date
        // 00:00:00.00                    // local time
        //
        // Number after the dot in time is expressed in nanoseconds.const
        // It is truncated after the 8-th digit.

        let digit2 = self.expect_digit()?;

        if self.0.peek_one() == Some(':') {
            return self.expect_time((digit1, digit2)).map(DatetimeLit::LocalTime);
        }

        let date = {
            let y1 = u16::from(digit1);
            let y2 = u16::from(digit2);
            let y3 = u16::from(self.expect_digit()?);
            let y4 = u16::from(self.expect_digit()?);
            self.expect_dash()?;
            let m1 = self.expect_digit()?;
            let m2 = self.expect_digit()?;
            self.expect_dash()?;
            let d1 = self.expect_digit()?;
            let d2 = self.expect_digit()?;

            Date {
                year: y1 * 1000 + y2 * 100 + y3 * 10 + y4,
                month: m1 * 10 + m2,
                day: d1 * 10 + d2,
            }
        };

        if !matches!(date.month, 1..=12) {
            return Err(DatetimeLitError::OutOfRangeMonth(date.month));
        }
        if !matches!(date.day, 1..=31) {
            return Err(DatetimeLitError::OutOfRangeDay(date.day));
        }

        if !self.0.eatc('T') && !self.0.eatc('t') {
            if matches!(self.0.peek_two(), Some((' ', d)) if d.is_ascii_digit()) {
                self.0.one();
            } else {
                return Ok(DatetimeLit::LocalDate(date));
            }
        }

        let time = {
            let h1 = self.expect_digit()?;
            let h2 = self.expect_digit()?;
            self.expect_time((h1, h2))?
        };

        let offset = match self.0.peek_one() {
            Some('Z') | Some('z') => {
                self.0.one();
                Offset::Z
            }
            Some(sign @ '+') | Some(sign @ '-') => {
                self.0.one();
                let sign = if sign == '+' { 1 } else { -1 };
                let h1 = self.expect_digit()? as i8;
                let h2 = self.expect_digit()? as i8;
                self.expect_colon()?;
                let m1 = self.expect_digit()?;
                let m2 = self.expect_digit()?;
                Offset::Custom {
                    hours: sign * (h1 * 10 + h2),
                    minutes: m1 * 10 + m2,
                }
            }
            _ => return Ok(DatetimeLit::LocalDatetime(date, time)),
        };
        Ok(DatetimeLit::OffsetDatetime(date, time, offset))
    }

    fn expect_time(&mut self, (h1, h2): (u8, u8)) -> Result<Time, DatetimeLitError> {
        self.expect_colon()?;
        let m1 = self.expect_digit()?;
        let m2 = self.expect_digit()?;
        self.expect_colon()?;
        let s1 = self.expect_digit()?;
        let s2 = self.expect_digit()?;

        let nanosecond = if !self.0.eatc('.') {
            0
        } else {
            let mut nanosecond = u32::from(self.expect_digit()?) * 10_u32.pow(8);
            let mut i = 8;
            while let Some(digit) = self.eat_digit().map(u32::from) {
                if i != 0 {
                    nanosecond += 10_u32.pow(i - 1) * digit;
                    i -= 1;
                } else {
                    // consume remaining digits of excess precision
                }
            }
            nanosecond
        };
        let time = Time {
            hour: h1 * 10 + h2,
            minute: m1 * 10 + m2,
            second: s1 * 10 + s2,
            nanosecond,
        };
        if time.hour > 24 {
            return Err(DatetimeLitError::OutOfRangeHour(time.hour));
        }
        if time.minute > 59 {
            return Err(DatetimeLitError::OutOfRangeMinute(time.minute));
        }
        if time.second > 59 {
            return Err(DatetimeLitError::OutOfRangeSecond(time.second));
        }
        assert!(time.nanosecond < 999_999_999, "only first 9 digits of a nanosecond are read");
        Ok(time)
    }

    fn eat_digit(&mut self) -> Option<u8> {
        self.0.peek_one().filter(char::is_ascii_digit).map(|ch| {
            self.0.one();
            ch as u8 - b'0'
        })
    }

    fn expect_digit(&mut self) -> Result<u8, DatetimeLitError> {
        self.eat_digit().ok_or_else(|| DatetimeLitError::ExpectedDigit)
    }

    fn expect_colon(&mut self) -> Result<(), DatetimeLitError> {
        if self.0.eatc(':') {
            return Ok(())
        }
        Err(DatetimeLitError::ExpectedColon)
    }

    fn expect_dash(&mut self) -> Result<(), DatetimeLitError> {
        if self.0.eatc('-') {
            return Ok(())
        }
        Err(DatetimeLitError::ExpectedDash)
    }
}
