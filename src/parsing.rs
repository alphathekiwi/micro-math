use crate::{MAX_EXPRESSION_LEN, MAX_PARENS};
use crate::graphing::Axis;

const NARROW_TOKENS: [Token; 8] = [Token::Add, Token::Sub, Token::Mul, Token::Div, Token::Mod, Token::Exp, Token::Sqrt, Token::Equals];


#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Token { // size of 3 bytes // 
    Pi,  // π
    Number,
    VarX,  // 'X'
    VarY,  // 'Y'
    Variable,  // not 'X' or 'Y' etc.
    Add, // +
    Sub, // -
    Mul, // *
    Div, // /
    Mod,  // Modulo (%)
    Exp,  // Exponentiation (^)
    Sqrt,  // Square root (√)
    OpenParen,  // Parentheses
    Sin,      // sin(X)
    ArcSin,   // asin(X)
    Cos,      // cos(X)
    ArcCos,   // acos(X)
    Tan,      // tan(X)
    ArcTan,   // atan(X)
    CloseParen,
    Equals, // = // for balancing equations
    NoTok,
}
impl From<&u8> for Token {
    fn from(value: &u8) -> Self {
        use Token::*;
        match value {
            b'0'..=b'9' | b'.' => Number,
            b'+' => Add,
            b'-' => Sub,
            b'*' => Mul,
            b'/' => Div,
            b'^' => Exp,
            b'%' => Mod,
            b'\\' => Sqrt,
            b'(' => OpenParen,
            b')' => CloseParen,
            b'A' | b'a' => ArcSin, // match any arc
            b'S' | b's' => Sin,
            b'C' | b'c' => Cos,
            b'T' | b't' => Tan,
            b'P' | b'p' => Pi,
            b'x' | b'X' => VarX,
            b'y' | b'Y' => VarY,
            b'A'..=b'Z' => Variable,
            b'=' => Equals,
            _ => NoTok,
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Calc {
    Num(f32),
    Expr(Token)
}
impl Calc {
    pub fn invert(&self) -> Option<Self> {
        match self {
            // Same or not balancable
            Calc::Num(n) => Some(Calc::Num(*n)),
            Calc::Expr(Token::Pi) => Some(Calc::Expr(Token::Pi)),
            Calc::Expr(Token::VarX) => Some(Calc::Expr(Token::VarX)),
            Calc::Expr(Token::VarY) => Some(Calc::Expr(Token::VarY)),
            Calc::Expr(Token::Number) => Some(Calc::Expr(Token::Number)),
            Calc::Expr(Token::Variable) => Some(Calc::Expr(Token::Variable)),
            Calc::Expr(Token::OpenParen) => Some(Calc::Expr(Token::OpenParen)),
            Calc::Expr(Token::CloseParen) => Some(Calc::Expr(Token::CloseParen)),
            // Simple invertable
            Calc::Expr(Token::Add) => Some(Calc::Expr(Token::Sub)),
            Calc::Expr(Token::Sub) => Some(Calc::Expr(Token::Add)),
            Calc::Expr(Token::Mul) => Some(Calc::Expr(Token::Div)),
            Calc::Expr(Token::Div) => Some(Calc::Expr(Token::Mul)),
            Calc::Expr(Token::Sin) => Some(Calc::Expr(Token::ArcSin)),
            Calc::Expr(Token::ArcSin) => Some(Calc::Expr(Token::Sin)),
            Calc::Expr(Token::Cos) => Some(Calc::Expr(Token::ArcCos)),
            Calc::Expr(Token::ArcCos) => Some(Calc::Expr(Token::Cos)),
            Calc::Expr(Token::Tan) => Some(Calc::Expr(Token::ArcTan)),
            Calc::Expr(Token::ArcTan) => Some(Calc::Expr(Token::Tan)),
            // Complex or not possible
            Calc::Expr(Token::Sqrt) => None, // ^2
            Calc::Expr(Token::Exp) => None, // ^(1/n)
            Calc::Expr(Token::Mod|Token::Equals|Token::NoTok) => None, // Modulo, Equals and NoTok can't be rebalanced
        }
    }
}

pub struct MathParser {
    pub(crate) focus_of_eq: Axis,
    pub(crate) equals_pos: usize,
    pub(crate) current: usize,
    pub(crate) cached_ans: Option<f32>,
    pub(crate) parens: heapless::Vec<(usize, usize), MAX_PARENS>,
    pub(crate) expressions: heapless::Vec<Calc, MAX_EXPRESSION_LEN>,
}
impl MathParser {
    pub fn new(input: &str) -> Self {
        let mut parser = MathParser {
            focus_of_eq: Axis::NoFocus,
            equals_pos: 0, //  NOTE:  zero is an invalid position for the = sign to reside so it has no effect if placed here
            current: 0,
            cached_ans: None,
            parens:  heapless::Vec::new(),
            expressions: heapless::Vec::new(),
        };
        {
            parser.parse_expression(input);
        }
        parser
    }

    /// Parses an expression into the tokens from which it is composed
    pub fn parse_expression(&mut self, input: &str) -> &Self {
        let bytes = input.as_bytes();
        if let Some(b) = bytes.first() {
            if matches!(Token::from(b), Token::Add | Token::Sub | Token::Mul | Token::Div | Token::Exp | Token::Mod) {
            // If equation begins with an operation push a variable in front of it
            let _ = self.expressions.push(Calc::Expr(Token::Variable));
        }}
        for (i, b) in bytes.iter().enumerate() {
            if self.current > i { continue; }
            let token = Token::from(b);
            if NARROW_TOKENS.contains(&token) {
                match token {
                    Token::Sqrt => self.previous_is_multiplier(),
                    Token::Equals => self.equals_pos = i,
                    _ => {},
                }
                let _ = self.expressions.push(Calc::Expr(token));
            }
            match &token {
                Token::Number => {
                    self.current = i + self.find_end(&bytes[i..], &token);
                    if let Ok(n) = input[i..self.current].parse::<f32>() {
                        self.push_maybe_negative(n);
                    }
                },
                Token::OpenParen => {
                    self.previous_is_multiplier();
                    let _ = self.parens.push((self.expressions.len(), 0));
                },
                Token::CloseParen => {
                    if let Some((i,(s,_))) = self.parens.iter().enumerate().rev().find(|(_,(_,e))| *e == 0) {
                        self.parens[i] = (*s, self.expressions.len())
                    }
                },
                Token::Sin | Token::Cos | Token::Tan => {
                    self.previous_is_multiplier();
                    if matches!(bytes.get(i+1), Some(b'(')) {
                        let _ = self.expressions.push(Calc::Expr(token));
                    } else if matches!((token, &bytes[i..].get(..4)),
                        (Token::Sin, Some([b's', b'i', b'n', b'('])) |
                        (Token::Cos, Some([b'c', b'o', b's', b'('])) |
                        (Token::Tan, Some([b't', b'a', b'n', b'(']))) {
                        let _ = self.expressions.push(Calc::Expr(token));
                        self.current = i + 3;
                    } else {
                        let _ = self.expressions.push(Calc::Expr(Token::Variable));
                    }
                },
                Token::ArcCos => {
                    let maybe = match &bytes[i..].get(..5) {
                        Some([b'a', b's', b'i', b'n', b'(']) => Some(Token::ArcSin),
                        Some([b'a', b'c', b'o', b's', b'(']) => Some(Token::ArcCos),
                        Some([b'a', b't', b'a', b'n', b'(']) => Some(Token::ArcTan),
                        Some(_) | None => None,
                    };
                    if let Some(t) = maybe {
                        self.previous_is_multiplier();
                        let _ = self.expressions.push(Calc::Expr(t));
                        self.current = i + 4;
                    }
                },
                Token::Pi => {
                    self.previous_is_multiplier();
                    self.push_maybe_negative(core::f32::consts::PI);
                    if matches!(&bytes.get(i+1), Some(b'0'..=b'9' | b'.')) {
                        let _ = self.expressions.push(Calc::Expr(Token::Mul));
                    }
                },
                Token::VarX => {
                    self.previous_is_multiplier();
                    let _ = self.expressions.push(Calc::Expr(token));
                    if self.equals_pos == 0 {
                        self.focus_of_eq = Axis::GraphX;
                    }
                },
                Token::VarY => {
                    self.previous_is_multiplier();
                    let _ = self.expressions.push(Calc::Expr(token));
                    if self.equals_pos == 0 {
                        self.focus_of_eq = Axis::GraphY;
                    }
                },
                Token::Variable => {
                    self.previous_is_multiplier();
                    let _ = self.expressions.push(Calc::Expr(token));
                },
                _ => {}
            }
        }
        self
    }

    fn find_end(&mut self, input: &[u8], wide: &Token) -> usize {
        let mut last = 0;
        let mut not_my_closing_bracket = 0;
        while let Some(&c) = input.get(last) {
            match (c, wide) {
                (b'(', Token::OpenParen) => { last += 1; not_my_closing_bracket += 1; },
                (b')', Token::OpenParen) => {
                    if not_my_closing_bracket > 0 { last += 1; not_my_closing_bracket -= 1; }
                    else { break; }
                },
                (_, Token::OpenParen) => last += 1,
                (b'0'..=b'9' | b'.', Token::Number) => last += 1,
                _ => break,
            }
        }
        last
    }

    fn previous_is_multiplier(&mut self) {
        let recent = self.expressions.last();
        if matches!(recent, Some(Calc::Num(_) | Calc::Expr(Token::Pi | Token::Variable))) {
            let _ = self.expressions.push(Calc::Expr(Token::Mul));
        }
    }

    fn push_maybe_negative(&mut self, n: f32) {
        if self.expressions.last() == Some(&Calc::Expr(Token::Sub)) {
            let _ = self.expressions.pop();
            if let Some(&Calc::Num(_)) = self.expressions.last() {
                let _ = self.expressions.push(Calc::Expr(Token::Add));
            }
            let _ = self.expressions.push(Calc::Num(-n));
        } else {
            let _ = self.expressions.push(Calc::Num(n));
        }
    }

}
