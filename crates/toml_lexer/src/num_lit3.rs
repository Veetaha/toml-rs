use crate::{cursor::Cursor, Span};

use std::{str::FromStr, convert::{TryFrom, TryInto}};

enum NumLitError {
    DisallowedLeadingZeros,
    DisallowedSign,
    UnenclosedUnderscore,
    UnrepresentableInt,
    UnrepresentableFloat,
}

enum Number {
    Int(i64),
    Float(f64),
}
enum NumberKind {
    Int,
    Float,
}

// pub struct NumLitToken {
//     span: Span,
//     kind: NumLitTokenKind,
// }

// enum NumLitTokenKind {
//     LeadingSign(NumSign),
//     ExoticRadixPrefix(ExoticRadix),
//     LeadingZeros(DigitContext),
//     DigitLike(DigitLike, DigitContext),
//     Dot,
//     ExponentPrefix(Option<NumSign>),
// }

enum DigitContext {
    ExoticRadix(ExoticRadix),
    Int,
    Mantissa,
    Exponent,
}

impl DigitContext {
    fn to_radix(&self) -> u32 {
        match *self {
            DigitContext::ExoticRadix(exotic_radix) => u32::from(exotic_radix),
            _ => 10
        }
    }
}


#[repr(u8)]
pub enum NumSign {
    Plus = b'+',
    Minus = b'-',
}

#[derive(Copy, Clone)]
#[repr(u32)]
pub enum ExoticRadix {
    Binary = 2,
    Octal = 8,
    Hex = 16,
}

impl From<ExoticRadix> for u32 {
    fn from(radix: ExoticRadix) -> Self {
        radix as u32
    }
}

fn tokenize_num_lit(input: &str) -> NumLitTokenizer<'_> {
    NumLitTokenizer {
        cursor: Cursor::new(input),
        state: State::Begin,
        buf: String::new(),
    }
}

enum State {
    Begin,
    ConsumedSign,
    FirstDigit(DigitContext),
    Digit(DigitContext),
}

enum DigitLike {
    Digit(u32),
    Underscores
}

struct NumLitTokenizer<'s> {
    cursor: Cursor<'s>,
    state: State,
    buf: String,
}


impl<'s> NumLitTokenizer<'s> {
    fn next_state(&mut self) -> bool {
        let start = self.cursor.current_index();

        let token_kind = match self.state {
            State::Begin(int) => {
                self.state = State::ConsumedSign;
                match self.eat_sign() {
                    Some(sign) => NumLitTokenKind::LeadingSign(sign),
                    None => return self.next_state(),
                }
            }
            State::ConsumedSign => match self.eat_exotic_radix_prefix() {
                Some(radix) => {
                    self.state = State::FirstDigit(DigitContext::ExoticRadix(radix));
                    NumLitTokenKind::ExoticRadixPrefix(radix)
                }
                None => {
                    self.state = State::FirstDigit(DigitContext::Int);
                    return self.next();
                }
            },
            State::FirstDigit(ctx) => {
                self.state = State::Digit(ctx);
                while self.cursor.eatc('0') {
                    // ...
                }
                if start == self.cursor.current_index() {
                    return self.next();
                } else {
                    NumLitTokenKind::LeadingZeros(ctx)
                }
            }
            State::Digit(ctx) => match self.digit_like(ctx.to_radix()) {
                Some(digit) => NumLitTokenKind::DigitLike(digit, ctx),
                None => match (ctx, self.cursor.peek_one()?) {
                    (DigitContext::Int, '.') => {
                        self.cursor.one();
                        self.state = State::FirstDigit(DigitContext::Mantissa);
                        NumLitTokenKind::Dot
                    }
                    (DigitContext::Int, ch) | (DigitContext::Mantissa, ch) if matches!(ch, 'e' | 'E') => {
                        self.cursor.one();
                        self.state = State::FirstDigit(DigitContext::Exponent);
                        NumLitTokenKind::ExponentPrefix(self.eat_sign())
                    }
                    _ => return None
                }
            },
            // let kind = match self.eat_explicit_radix() {
            //     Some(radix) => NumLitTokenKind::Int {
            //         kind: IntKind::ExplicitRadix(radix),
            //         val: self.int(u32::from(radix)).map(|(_, _, val)| val)
            //     },
            //     None => match self.decimal_num() {
            //         Some(it) => it,
            //         None => {
            //             return Some((
            //                 self.cursor.span_from(start),
            //                 NumLitToken::Signful(sign?, None),
            //             ))
            //         }
            //     },
            // };
            // let token = match sign {
            //     Some(sign) => NumLitToken::Signful(sign, Some(kind)),
            //     None => NumLitToken::Signless(kind),
            // };
            // Some((self.cursor.span_from(start), token))
        };

        Some(NumLitToken { span: self.cursor.span_from(start), kind: token_kind })
    }

    fn digit_like(&mut self, radix: u32) -> Option<DigitLike> {
        Some(if self.eat_underscores() {
            DigitLike::Underscores
        } else {
            let digit = self.cursor.peek_one()?.to_digit(radix)?;
            self.cursor.one();
            DigitLike::Digit(digit)
        })


        // if let Some(span) = underscores {
        //     // Trailing or consecutive underscores are invalid
        //     if digit.is_none() || span.start + 1 != span.end {
        //         (self.report_bad_underscores)(span)
        //     }
        // }
        //     // match digit {
        //     //     Some(digit) => {
        //     //         n_signifiant_digits += 1;
        //     //         let shifted = val.checked_mul(i64::from(radix));
        //     //         val = match shifted.and_then(|it| it.checked_add(digit)) {
        //     //             Some(it) => it,
        //     //             None => {
        //     //                 // Consume all what is left jus


        //     //                 break IntVal::Overflow
        //     //             },
        //     //         }
        //     //     }
        //     //     None => break IntVal::Val(val),
        //     // }
        // // Some((leading_zeros, n_signifiant_digits, val))
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

    fn eat_underscores(&mut self) -> bool {
        while self.cursor.eatc('_') {
            // ...
        }
    }

    // fn eat_zeros(&mut self) -> u32 {
    //     let mut n_zeros = 0;
    //     while self.cursor.eatc('0') {
    //         n_zeros += 1;
    //     }
    //     n_zeros
    // }

    fn decimal_num(&mut self) -> Option<NumLitTokenKind> {
        let (n_leading_zeros, _, val) = self.digit_like(10)?;
        let val = match val {
            IntVal::Val(it) => it,
            IntVal::Overflow => return Some(NumLitTokenKind::IntPart {
                val: Some(val),
                kind: IntKind::Decimal{ n_leading_zeros }
            }),
        };

        let val = if self.cursor.eatc('.') {
            let (n_leading_zeros, n_significant_digits, val) = match self.digit_like(10) {
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

    // fn eat_exponent(&mut self, frac_part: f64) -> NumLitTokenKind {
    //     let sign = self.eat_sign();
    //     match self.digit(10).map(|(_, val)| val) {
    //         Some(it) => it,
    //         None => return NumLitTokenKind::Float(FloatVal::EmptyExponent),
    //     };
    // }

    fn eat_exotic_radix_prefix(&mut self) -> Option<ExoticRadix> {
        let radix = match self.cursor.peek_two()? {
            ('0', 'x') => ExoticRadix::Hex,
            ('0', 'o') => ExoticRadix::Octal,
            ('0', 'b') => ExoticRadix::Binary,
            _ => return None,
        };
        self.cursor.two();
        Some(radix)
    }
}

// f
// n integer(&self, s: &'a str, radix: u32) -> Result<i64, Error> {
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
