#[allow(unused)]
pub mod parsing;
pub mod unsafe_parse;
// pub mod calculation;
// pub mod graphing;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Op {
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Mod,    // Modulo (%)
    Exp,    // Exponentiation (^)
    Sqrt,   // Square root (√)
    Fac,    // Factorial (!)
    Sin,    // sin(X)
    ArcSin, // asin(X)
    Cos,    // cos(X)
    ArcCos, // acos(X)
    Tan,    // tan(X)
    ArcTan, // atan(X)
    NotOp,
}
impl From<&u8> for Op {
    fn from(value: &u8) -> Self {
        use Op::*;
        match value {
            b'+' => Add,
            b'-' => Sub,
            b'*' => Mul,
            b'/' => Div,
            b'^' => Exp,
            b'%' => Mod,
            b'\\' => Sqrt,
            b'!' => Fac,
            b'A' | b'a' => ArcSin, // match any arc
            b'S' | b's' => Sin,
            b'C' | b'c' => Cos,
            b'T' | b't' => Tan,
            _ => NotOp,
        }
    }
}
impl From<&char> for Op {
    fn from(value: &char) -> Self {
        use Op::*;
        match value {
            '+' => Add,
            '-' => Sub,
            '*' => Mul,
            '/' => Div,
            '^' => Exp,
            '%' => Mod,
            '!' => Fac,
            '√' | '\\' => Sqrt,
            'A' | 'a' => ArcSin, // match any arc
            'S' | 's' => Sin,
            'C' | 'c' => Cos,
            'T' | 't' => Tan,
            _ => NotOp,
        }
    }
}


#[derive(Debug, PartialEq, Copy, Clone)]
#[derive(Default)]
pub enum Token {
    Equals, // = // for balancing equations
    Pi,     // π
    Number(f32),
    Variable(u32),
    OpenParen(u32), // Parentheses
    CloseParen(u32),
    Operation(Op),
    AstPointer(usize),
    #[default]
    NotTok,
}
impl From<&u8> for Token {
    fn from(value: &u8) -> Self {
        use Token::*;
        match value {
            b'0'..=b'9' | b'.' => Number(0.0),
            b'(' => OpenParen(0),
            b')' => CloseParen(0),
            b'P' | b'p' => Pi,
            b'x' | b'X' => Variable(1),
            b'y' | b'Y' => Variable(2),
            b'=' => Equals,
            _ => {
                let o = Op::from(value);
                if !matches!(o, Op::NotOp) {
                    Operation(o)
                } else if value.is_ascii_uppercase() {
                    Variable(*value as u32)
                } else {
                    NotTok
                }
            }
        }
    }
}
impl From<&char> for Token {
    fn from(value: &char) -> Self {
        use Token::*;
        match value {
            '0'..='9' | '.' => Number(0.0),
            '(' => OpenParen(0),
            ')' => CloseParen(0),
            'π' | 'P' | 'p' => Pi,
            'x' | 'X' => Variable(1),
            'y' | 'Y' => Variable(2),
            'A'..='Z' => Variable(*value as u32),
            '=' => Equals,
            _ => {
                let o = Op::from(value);
                if !matches!(o, Op::NotOp) {
                    Operation(o)
                } else if value.is_ascii_uppercase() {
                    Variable(*value as u32)
                } else {
                    NotTok
                }
            }
        }
    }
}

pub(crate) const NARROW_TOKENS: [Token; 9] = [
    Token::Operation(Op::Add),
    Token::Operation(Op::Sub),
    Token::Operation(Op::Mul),
    Token::Operation(Op::Div),
    Token::Operation(Op::Mod),
    Token::Operation(Op::Exp),
    Token::Operation(Op::Sqrt),
    Token::Operation(Op::Fac),
    Token::Equals,
];

#[cfg(test)]
pub(crate) mod tests;
