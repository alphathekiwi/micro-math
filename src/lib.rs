pub mod equation;
pub mod str_parse;
// pub mod safer_parse;
pub mod unsafe_parse;

#[cfg(test)]
pub(crate) mod tests;

pub mod calculation;
// pub mod graphing;

pub trait Equation {
    fn solve(&self, vars: &[f32]) -> f32;
    fn render_tree(&self) -> Vec<String>;
}
pub trait AbstractSnytaxTree
where
    Self: Sized,
{
    type A;
    // fn with_op(op: Op) -> Self;
    fn solve(&self, vars: &[f32]) -> f32;

    // SETTERS
    fn set_operation(&mut self, op: Op);
    fn set_left(&mut self, left: &Token<Self::A>);
    fn set_right(&mut self, right: &Token<Self::A>);

    // GETTERS
    fn get_values(&self) -> (MicroVal<Self>, MicroVal<Self>, Op);
    fn get_flags(&self) -> (u8, u8, Op);
    fn left_flags(&self) -> u8;
    fn right_flags(&self) -> u8;

    // IMPLEMENTED GENERIC
    fn invert(&mut self) {
        let (_, right, op) = self.get_values();
        let inv = match op {
            Op::Sin => Some(Op::ArcSin), // attach to right
            Op::ArcSin => Some(Op::Sin),
            Op::Cos => Some(Op::ArcCos),
            Op::ArcCos => Some(Op::Cos),
            Op::Tan => Some(Op::ArcTan),
            Op::ArcTan => Some(Op::Tan),
            Op::Add => Some(Op::Sub),
            Op::Sub => Some(Op::Add),
            Op::Mul => Some(Op::Div),
            Op::Div => Some(Op::Mul),
            Op::Sqrt => {
                // ^2
                // self.left = self.right;
                self.set_right(&Token::Number(2.0));
                Some(Op::Exp)
            }
            Op::Exp => {
                // ^(1/n)
                if let MicroVal::Float(val) = right {
                    self.set_right(&Token::Number(1.0 / val));
                }
                None // Operation doesn't change
            }
            Op::Fac | Op::Mod | Op::NotOp => None, // Modulo and NotOp can't be rebalanced
        };
        if let Some(new_op) = inv {
            self.set_operation(new_op);
        }
    }
    fn is_all_movable(&self) -> bool {
        let (left, right, op) = self.get_flags();
        match op {
            Op::Mod => (left & right & 0xC0) == 0xC0,
            _ => (left & right & MOVABLE) == MOVABLE,
        }
    }
    fn right_moves(&self) -> bool {
        (self.right_flags() & 64) == 64
    }
    fn left_moves(&self) -> bool {
        (self.left_flags() & 64) == 64
    }
}

#[repr(u32)]
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum MicroVal<'a, T> {
    Float(f32) = 3,
    Var(u32) = 2,
    Nested(&'a T) = 1,
    Unitialized = 0,
}

/// Tokens are easily cast into/from characters try `string.chars()`
///```
/// use micro_math::Token;
///
/// let ch = 'π';
/// let token = Token::from(ch);
/// assert_eq!(token, Token::Pi);
///```
#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub enum Token<T> {
    Equals, // = // for balancing equations
    Pi,     // π
    Number(f32),
    Variable(u32),
    OpenParen(u32), // Parentheses
    CloseParen(u32),
    Operation(Op),
    AstPointer(T),
    #[default]
    NotTok,
}
impl<T> Token<T> {
    const fn is_narrow(&self) -> bool {
        matches!( // fn is_narrow
            self,
            Token::Operation(
                Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Mod | Op::Exp | Op::Sqrt | Op::Fac,
            ) | Token::Equals
        )
    }
    const fn is_doublesided_op(&self) -> bool {
        matches!( // fn is_doublesided_op
            self,
            Token::Operation(Op::Add | Op::Mul | Op::Div | Op::Exp | Op::Mod | Op::Sub)
        )
    }
    const fn is_paren_start(&self) -> bool {
        matches!( // fn is_paren_start
            self,
            Token::Operation(Op::Sin | Op::ArcSin | Op::Cos | Op::ArcCos | Op::Tan | Op::ArcTan)
                | Token::OpenParen(_)
        )
    }
}

#[derive(Debug, PartialEq, Copy, Clone, Default)]
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
    #[default]
    NotOp,
}
impl Op {
    fn recurs_on_ans<T>(val: T) -> Option<Self>
    where
        T: Into<Op>,
    {
        let val = val.into();
        match &val {
            Op::Add | Op::Mul | Op::Div | Op::Exp | Op::Mod | Op::Sub => Some(val),
            _ => None,
        }
    }
}

const FLOAT_FLAG: u8 = 0b11100000; // Float is always move
const NESTED_FLAG: u8 = 0b10000000;
const VAR_FLAG: u8 = 0b01000000;
const MOVABLE: u8 = 0b00100000;

impl<T> From<u8> for Token<T> {
    fn from(value: u8) -> Self {
        Token::from(value as char)
    }
}
impl<T> From<char> for Token<T> {
    fn from(value: char) -> Self {
        use Token::*;
        match value {
            '0'..='9' | '.' => Number(0.0),
            '(' => OpenParen(0),
            ')' => CloseParen(0),
            'π' | 'P' | 'p' => Pi,
            'x' | 'X' => Variable(1),
            'y' | 'Y' => Variable(2),
            'A'..='Z' => Variable(value as u32),
            '=' => Equals,
            _ => {
                let o = Op::from(value);
                if !matches!(o, Op::NotOp) {
                    Operation(o)
                } else if value.is_ascii_uppercase() {
                    Variable(value as u32)
                } else {
                    NotTok
                }
            }
        }
    }
}
impl<T: std::fmt::Display> std::fmt::Display for Token<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Equals => write!(f, "="),
            Token::Pi => write!(f, "π"),
            Token::Number(n) => write!(f, "{n}"),
            Token::Variable(v) => write!(f, "{v}"),
            Token::OpenParen(_) => write!(f, "("),
            Token::CloseParen(_) => write!(f, ")"),
            Token::Operation(op) => write!(f, "{op}"),
            Token::AstPointer(p) => write!(f, "[{p}]"),
            Token::NotTok => write!(f, "="),
        }
    }
}

impl From<u8> for Op {
    fn from(value: u8) -> Self {
        Op::from(value as char)
    }
}
impl From<char> for Op {
    fn from(value: char) -> Self {
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
impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            crate::Op::Add => write!(f, "+"),
            crate::Op::Sub => write!(f, "-"),
            crate::Op::Mul => write!(f, "*"),
            crate::Op::Div => write!(f, "/"),
            crate::Op::Mod => write!(f, "%"),
            crate::Op::Exp => write!(f, "^"),
            crate::Op::Sqrt => write!(f, "√"),
            crate::Op::Fac => write!(f, "!"),
            crate::Op::Sin => write!(f, "sin"),
            crate::Op::ArcSin => write!(f, "asin"),
            crate::Op::Cos => write!(f, "cos"),
            crate::Op::ArcCos => write!(f, "acos"),
            crate::Op::Tan => write!(f, "tan"),
            crate::Op::ArcTan => write!(f, "atan"),
            crate::Op::NotOp => write!(f, "?"),
        }
    }
}

const VARS: &str = "AXY";
impl<T: Equation> Equation for MicroVal<'_, T> {
    fn solve(&self, vars: &[f32]) -> f32 {
        self.base_solve(vars)
    }
    fn render_tree(&self) -> Vec<String> {
        self.base_tree_render()
    }
}
impl<'a, T: Equation> MicroVal<'a, T> {
    pub(crate) fn base_solve(&self, vars: &[f32]) -> f32 {
        match self {
            MicroVal::Float(f) => *f,
            MicroVal::Var(v) => vars.get(*v as usize).copied().unwrap_or(0.0),
            MicroVal::Nested(micro_tree) => micro_tree.solve(vars),
            MicroVal::Unitialized => 0.0,
        }
    }
    pub(crate) fn base_tree_render(&self) -> Vec<String> {
        let mut display: Vec<String> = Vec::new();
        match self {
            MicroVal::Float(n) => display.push(format!("{n}")),
            MicroVal::Var(v) => display.push(
                VARS.chars()
                    .nth(*v as usize)
                    .map(|c| c.to_string())
                    .unwrap_or_else(|| format!("{}", v))
                    .to_string(),
            ),
            MicroVal::Nested(micro_equation) => {
                let lines = micro_equation.render_tree();
                for (i, line) in lines.iter().enumerate() {
                    let prefix: String = if i > 1 {
                        (0..(i / 2)).map(|_| "  ").collect()
                    } else {
                        "".into()
                    };
                    display.push(format!("{prefix}{}", line));
                }
            }
            MicroVal::Unitialized => {}
        }
        display
    }
}
