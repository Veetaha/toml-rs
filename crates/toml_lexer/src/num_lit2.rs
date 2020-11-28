use crate::{cursor::Cursor, Span};

use std::convert::TryFrom;
// use decimal_num::Subtoken as DecimalNumSubtoken;
// use explicit_base_int::Subtoken as ExplicitBaseIntSubtoken;

// pub enum NumLitSubtoken {
//     DecimalNum(DecimalNumSubtoken),
//     ExplicitBaseInt(ExplicitBaseIntSubtoken),
//     ExponentSymbol,
//     Inf,
//     Nan,
//     Sign(NumSign),
//     IntBase(IntBase)
// }

pub trait NumLitTokenizer: Iterator<Item = NumLitSubtoken> {
    fn into_number() -> Option<Number>;
}

enum Number {
    Int(i64),
    Float(f64),
}

enum NumLitSubtoken {
    Digit(char, u32),
    NonDigit(char),
    Dot,
    ExponentPrefix(Option<NumSign>),
    Underscores,
}

#[repr(u8)]
pub enum NumSign {
    Plus = b'+',
    Minus = b'-',
}

#[derive(Copy, Clone)]
#[repr(u32)]
pub enum IntRadix {
    Binary = 2,
    Octal = 8,
    Decimal = 10,
    Hex = 16,
}

impl From<IntRadix> for u32 {
    fn from(radix: IntRadix) -> Self {
        radix as u32
    }
}

struct NumLitTokenizerImpl<'s>(Cursor<'s>);




fn tokenize_num_lit(&mut self) -> Option<(Span, NumLitSubtoken)> {
        let start = self.cursor.current_index();
        let sign = self.eat_sign();

        let kind = match self.eat_explicit_radix() {
            Some(radix) => NumLitTokenKind::Int {
                kind: IntKind::ExplicitRadix(radix),
                val: self.int(u32::from(radix)).map(|(_, _, val)| val)
            },
            None => match self.decimal_num() {
                Some(it) => it,
                None => {
                    return Some((
                        self.cursor.span_from(start),
                        NumLitSubtoken::Signful(sign?, None),
                    ))
                }
            },
        };
        let token = match sign {
            Some(sign) => NumLitSubtoken::Signful(sign, Some(kind)),
            None => NumLitSubtoken::Signless(kind),
        };
        Some((self.cursor.span_from(start), token))
    }

    fn eat_digit(&mut self, radix: u32) -> Option<i64> {
        self.cursor
            .peek_one()
            .and_then(|it| it.to_digit(radix))
            .map(|it| {
                self.cursor.one();
                it.into()
            })
    }

    fn int(&mut self, radix: u32) -> impl Iterator<Item = (char, i64)> {
        // Leading underscores are always invalid
        self.eat_underscores().map(self.report_bad_underscores);

        std::iter::from_fn(|| {
            let digit = self.eat_digit(radix);
            let underscores = self.eat_underscores();

            if let Some(span) = underscores {
                // Trailing or consecutive underscores are invalid
                if digit.is_none() || span.start + 1 != span.end {
                    (self.report_bad_underscores)(span)
                }
            }
            match digit {
                Some(digit) => {
                    n_signifiant_digits += 1;
                    let shifted = val.checked_mul(i64::from(radix));
                    val = match shifted.and_then(|it| it.checked_add(digit)) {
                        Some(it) => it,
                        None => {
                            // Consume all what is left jus


                            break IntVal::Overflow
                        },
                    }
                }
                None => break IntVal::Val(val),
            }
        });
        // Some((leading_zeros, n_signifiant_digits, val))
    }

    fn eat_underscores(&mut self) -> Option<Span> {
        let start = self.cursor.current_index();
        while self.cursor.eatc('_') {
            // ...
        }
        let span = self.cursor.span_from(start);
        if span.start == span.end {
            None
        } else {
            Some(span)
        }
    }

    fn eat_zeros(&mut self) -> u32 {
        let mut n_zeros = 0;
        while self.cursor.eatc('0') {
            n_zeros += 1;
        }
        n_zeros
    }

    fn decimal_num(&mut self) -> Option<NumLitTokenKind> {
        let (n_leading_zeros, _, val) = self.int(10)?;
        let val = match val {
            IntVal::Val(it) => it,
            IntVal::Overflow => return Some(NumLitTokenKind::Int {
                val: Some(val),
                kind: IntKind::Decimal{ n_leading_zeros }
            }),
        };

        let val = if self.cursor.eatc('.') {
            let (n_leading_zeros, n_significant_digits, val) = match self.int(10) {
                Some(it) => it,
                None => return Some(NumLitTokenKind::Float(FloatVal::EmptyMantissa)),
            };
            match val {
                IntVal::Val(_) => {}
                IntVal::Overflow => return Some(NumLitTokenKind::Float(FloatVal::Overflow)),
            }
        } else {
            match f64::try_from(val) {
                Ok(it) => it,
                Err(_) => return Some(NumLitTokenKind::Float(FloatVal::Overflow)),
            }
        };

        if self.cursor.eatc('e') || self.cursor.eatc('E') {

            _ =>
        }

    }

    fn eat_exponent(&mut self, frac_part: f64) -> NumLitTokenKind {
        let sign = self.eat_sign();
        match self.int(10).map(|(_, val)| val) {
            Some(it) => it,
            None => return NumLitTokenKind::Float(FloatVal::EmptyExponent),
        };

    }

    fn eat_sign(&mut self) -> Option<NumSign> {
        let sign = match self.cursor.peek_one()? {
            '+' => NumSign::Plus,
            '-' => NumSign::Minus,
            _ => return None,
        };
        self.cursor.one();
        Some(sign)
    }

    fn eat_explicit_radix(&mut self) -> Option<IntRadix> {
        let radix = match self.cursor.peek_two()? {
            ('0', 'x') => IntRadix::Hex,
            ('0', 'o') => IntRadix::Octal,
            ('0', 'b') => IntRadix::Binary,
            _ => return None,
        };
        self.cursor.two();
        Some(radix)
    }
}

// fn integer(&self, s: &'a str, radix: u32) -> Result<i64, Error> {
//     let allow_sign = radix == 10;
//     let allow_leading_zeros = radix != 10;
//     let (prefix, suffix) = self.parse_integer(s, allow_sign, allow_leading_zeros, radix)?;
//     let start = self.tokens.substr_offset(s);
//     if suffix != "" {
//         return Err(self.error(start, ErrorKind::NumberInvalid));
//     }
//     i64::from_str_radix(&prefix.replace("_", "").trim_start_matches('+'), radix)
//         .map_err(|_e| self.error(start, ErrorKind::NumberInvalid))
// }

// fn parse_integer(
//     &self,
//     s: &'a str,
//     allow_sign: bool,
//     allow_leading_zeros: bool,
//     radix: u32,
// ) -> Result<(&'a str, &'a str), Error> {
//     let start = self.tokens.substr_offset(s);

//     let mut first = true;
//     let mut first_zero = false;
//     let mut underscore = false;
//     let mut end = s.len();
//     for (i, c) in s.char_indices() {
//         let at = i + start;
//         if i == 0 && (c == '+' || c == '-') && allow_sign {
//             continue;
//         }

//         if c == '0' && first {
//             first_zero = true;
//         } else if c.is_digit(radix) {
//             if !first && first_zero && !allow_leading_zeros {
//                 return Err(self.error(at, ErrorKind::NumberInvalid));
//             }
//             underscore = false;
//         } else if c == '_' && first {
//             return Err(self.error(at, ErrorKind::NumberInvalid));
//         } else if c == '_' && !underscore {
//             underscore = true;
//         } else {
//             end = i;
//             break;
//         }
//         first = false;
//     }
//     if first || underscore {
//         return Err(self.error(start, ErrorKind::NumberInvalid));
//     }
//     Ok((&s[..end], &s[end..]))
// }

// fn float(&mut self, s: &'a str, after_decimal: Option<&'a str>) -> Result<f64, Error> {
//     let (integral, mut suffix) = self.parse_integer(s, true, false, 10)?;
//     let start = self.tokens.substr_offset(integral);

//     let mut fraction = None;
//     if let Some(after) = after_decimal {
//         if suffix != "" {
//             return Err(self.error(start, ErrorKind::NumberInvalid));
//         }
//         let (a, b) = self.parse_integer(after, false, true, 10)?;
//         fraction = Some(a);
//         suffix = b;
//     }

//     let mut exponent = None;
//     if suffix.starts_with('e') || suffix.starts_with('E') {
//         let (a, b) = if suffix.len() == 1 {
//             self.eat(Token::Plus)?;
//             match self.next()? {
//                 Some((_, Token::Keylike(s))) => self.parse_integer(s, false, true, 10)?,
//                 _ => return Err(self.error(start, ErrorKind::NumberInvalid)),
//             }
//         } else {
//             self.parse_integer(&suffix[1..], true, true, 10)?
//         };
//         if b != "" {
//             return Err(self.error(start, ErrorKind::NumberInvalid));
//         }
//         exponent = Some(a);
//     } else if !suffix.is_empty() {
//         return Err(self.error(start, ErrorKind::NumberInvalid));
//     }

//     let mut number = integral
//         .trim_start_matches('+')
//         .chars()
//         .filter(|c| *c != '_')
//         .collect::<String>();
//     if let Some(fraction) = fraction {
//         number.push_str(".");
//         number.extend(fraction.chars().filter(|c| *c != '_'));
//     }
//     if let Some(exponent) = exponent {
//         number.push_str("E");
//         number.extend(exponent.chars().filter(|c| *c != '_'));
//     }
//     number
//         .parse()
//         .map_err(|_e| self.error(start, ErrorKind::NumberInvalid))
//         .and_then(|n: f64| {
//             if n.is_finite() {
//                 Ok(n)
//             } else {
//                 Err(self.error(start, ErrorKind::NumberInvalid))
//             }
//         })
// }
