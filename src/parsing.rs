use std::ops::{Add as _, Div as _, Mul as _, Sub as _};
use crate::{Op, Token};
const NARROW_OPS: [Op; 7] = [Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Mod, Op::Exp, Op::Sqrt];

const FLOAT_FLAG: u8 = 0xE0; // Float is always move
const VAR_FLAG: u8 = 0x80;
const MOVABLE: u8 = 0x20;




// #[repr(C, packed)]
#[repr(u32)]
#[derive(Debug, PartialEq, Copy, Clone)]
enum MicroEqValue<'a> {
    Float(f32)                = 3,
    Var(u32)                  = 2,
    Nested(&'a MicroTree<'a>) = 1,
    Unitialized               = 0,
}
impl MicroEqValue<'_> {
    fn solution(&self, vars: &[f32]) -> f32 {
        match self {
            MicroEqValue::Float(f) => *f,
            MicroEqValue::Var(v) => vars.get(*v as usize).copied().unwrap_or(0.0),
            MicroEqValue::Nested(micro_tree) => micro_tree.solution(vars),
            MicroEqValue::Unitialized => 0.0,
        }
    }
}
#[allow(unused)]
/// ```
/// use micro_math::parsing::MicroTree;
/// 
/// 
/// ```
#[derive(Debug, PartialEq, Copy, Clone)]
pub struct MicroTree<'a> {
    // left: u32,
    // right: u32,
    left: MicroEqValue<'a>,
    right: MicroEqValue<'a>,
    left_flags: u8,
    right_flags: u8,
    operation: Op,
}
impl Default for MicroTree<'_> {
    fn default() -> Self {
        MicroTree {
            left: MicroEqValue::Unitialized, right: MicroEqValue::Unitialized,
            operation: Op::NotOp, left_flags: 0, right_flags: 0 
        }
    }
}

#[allow(unused)]
impl MicroTree<'_> {
    fn new(operation: Op) -> Self {
        MicroTree { 
            // left: 0, right: 0, 
            left: MicroEqValue::Unitialized, right: MicroEqValue::Unitialized,
            operation , left_flags: 0, right_flags: 0 
        }
    }
    fn solution(&self, vars: &[f32]) -> f32 {
        // let left = leaf_to_contained(self.left, self.left_flags).solution(vars);
        // let right = leaf_to_contained(self.right, self.right_flags).solution(vars);
        let left = self.left.solution(vars);
        let right = self.right.solution(vars);
        calculate(left, right, self.operation)
    }
    fn set_left_as_nested(&mut self, left: &'static MicroTree) {
        if left.is_all_movable() { 
            self.left_flags = MOVABLE; 
        } else { self.left_flags = 0; }
        self.left = MicroEqValue::Nested(left);
    }
    fn set_left_as_float(&mut self, left: f32) {
        self.left_flags = FLOAT_FLAG;
        self.left = MicroEqValue::Float(left);
    }
    fn set_left_as_var(&mut self, left: u32) {
        self.left_flags = VAR_FLAG;
        self.left = MicroEqValue::Var(left);
    }
    fn set_right_as_nested(&mut self, right: &'static MicroTree) {
        if right.is_all_movable() { 
            self.right_flags = MOVABLE; 
        } else { self.right_flags = 0; }
        self.right = MicroEqValue::Nested(right);
    }
    fn set_right_as_float(&mut self, right: f32) {
        self.right_flags = FLOAT_FLAG;
        self.right = MicroEqValue::Float(right);
    }
    fn set_right_as_var(&mut self, right: u32) {
        self.right_flags = VAR_FLAG;
        self.right = MicroEqValue::Var(right);
    }
    fn invert(&mut self) {
        let inv = match self.operation {
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
            Op::Sqrt => { // ^2
                self.left = self.right;
                self.set_right_as_float(2.0);
                Some(Op::Exp)
            },
            Op::Exp => { // ^(1/n)
                if let MicroEqValue::Float(val) = self.right {
                    self.set_right_as_float(1.0/val);
                }
                None // Operation doesn't change
            },
            Op::Fac|Op::Mod|Op::NotOp => None, // Modulo and NotOp can't be rebalanced
        };
        if let Some(i) = inv {
            self.operation = i;
        }
    }
    /// Determines if this part of the equation can be moved
    /// For modulo it can only move if both L&R are numbers
    fn is_all_movable(&self) -> bool {
        if matches!(self.operation, Op::Mod) {
            (self.left_flags & self.right_flags & 0xC0) == 0xC0
        } else {
            (self.left_flags & self.right_flags & MOVABLE) == MOVABLE
        }
    }
    fn right_moves(&self) -> bool {
        (self.right_flags & 64) == 64
    }
    fn left_moves(&self) -> bool {
        (self.left_flags & 64) == 64
    }
}

fn calculate(left: f32, right: f32, operation: Op) -> f32 {
    match operation {
        Op::Sin    => right.sin(),
        Op::ArcSin => right.asin(),
        Op::Cos    => right.cos(),
        Op::ArcCos => right.acos(),
        Op::Tan    => right.tan(),
        Op::ArcTan => right.atan(),
        Op::Sqrt   => right.sqrt(),
        Op::Exp    => left.powf(right),
        Op::Mul    => left.mul(right),
        Op::Div    => left.div(right),
        Op::Mod    => left % right,
        Op::Fac    => left/2.0*(left+1.0),
        Op::Add    => left.add(right),
        Op::Sub    => left.sub(right),
        Op::NotOp  => 0.0,
    }
}


pub struct MathParser {
    // pub(crate) focus_of_eq: crate::graphing::Axis,
    pub(crate) equals_pos: usize,
    pub(crate) current: usize,

    pub(crate) cached_ans: Option<f32>,
}
impl MathParser {
    pub fn new(input: &str) -> Self {
        let eq_index = input.find('=').filter(|i| { *i < input.len() }).unwrap_or_default();
        if eq_index > 0 {
            let (left, right) = input.split_at(eq_index);
            let left_ex = parse_expression(left);
            let right_ex = parse_expression(right);

            let mut root = MicroTree::default();
            // root.set_left_as_nested(&left_ex);
            // root.set_right_as_nested(&right_ex);
        } else {
            let root = parse_expression(input);
        }
        // let (eq_index, mut root) = if let Some(i) =  {
        //     if  { 
        //         (i, MicroTree::default())
        //     } else { (0, MicroTree::default()) }
        // } else { (0, MicroTree::default()) };
    // let root = if equals_pos == 0 {
    // } else {
    //     MicroTree::new(Op::NotOp);
    // };

        MathParser {
            // focus_of_eq: crate::graphing::Axis::NoFocus,
            equals_pos: eq_index,
            current: 0,
            cached_ans: None,
        }
    }
}
    /// Parses an expression into the tokens from which it is composed
pub fn parse_expression(input: &str) -> MicroTree { // <'a>(root: &'a mut MicroTree
    MicroTree::default()



    // let bytes = input.as_bytes();
    // if let Some(b) = bytes.first() {
    //     if matches!(Op::from(b), Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Exp | Op::Mod) {
    //     // If equation begins with an operation push a variable in front of it
    //     let _ = expressions.push(Calc::Expr(Op::Variable));
    // }}
    // for (i, b) in bytes.iter().enumerate() {
    //     if current > i { continue; }
    //     let token = Op::from(b);
    //     if NARROW_OPS.contains(&token) {
    //         match token {
    //             Op::Sqrt => previous_is_multiplier(),
    //             Op::Equals => equals_pos = i,
    //             _ => {},
    //         }
    //         let _ = expressions.push(Calc::Expr(token));
    //     }
    //     match &token {
    //         Op::Number => {
    //             current = i + find_end(&bytes[i..], &token);
    //             if let Ok(n) = input[i..current].parse::<f32>() {
    //                 push_maybe_negative(n);
    //             }
    //         },
    //         Op::OpenParen => {
    //             previous_is_multiplier();
    //             let _ = parens.push((expressions.len(), 0));
    //         },
    //         Op::CloseParen => {
    //             if let Some((i,(s,_))) = parens.iter().enumerate().rev().find(|(_,(_,e))| *e == 0) {
    //                 parens[i] = (*s, expressions.len())
    //             }
    //         },
    //         Op::Sin | Op::Cos | Op::Tan => {
    //             previous_is_multiplier();
    //             if matches!(bytes.get(i+1), Some(b'(')) {
    //                 let _ = expressions.push(Calc::Expr(token));
    //             } else if matches!((token, &bytes[i..].get(..4)),
    //                 (Op::Sin, Some([b's', b'i', b'n', b'('])) |
    //                 (Op::Cos, Some([b'c', b'o', b's', b'('])) |
    //                 (Op::Tan, Some([b't', b'a', b'n', b'(']))) {
    //                 let _ = expressions.push(Calc::Expr(token));
    //                 current = i + 3;
    //             } else {
    //                 let _ = expressions.push(Calc::Expr(Op::Variable));
    //             }
    //         },
    //         Op::ArcCos => {
    //             let maybe = match &bytes[i..].get(..5) {
    //                 Some([b'a', b's', b'i', b'n', b'(']) => Some(Op::ArcSin),
    //                 Some([b'a', b'c', b'o', b's', b'(']) => Some(Op::ArcCos),
    //                 Some([b'a', b't', b'a', b'n', b'(']) => Some(Op::ArcTan),
    //                 Some(_) | None => None,
    //             };
    //             if let Some(t) = maybe {
    //                 previous_is_multiplier();
    //                 let _ = expressions.push(Calc::Expr(t));
    //                 current = i + 4;
    //             }
    //         },
    //         Op::Pi => {
    //             previous_is_multiplier();
    //             push_maybe_negative(core::f32::consts::PI);
    //             if matches!(&bytes.get(i+1), Some(b'0'..=b'9' | b'.')) {
    //                 let _ = expressions.push(Calc::Expr(Op::Mul));
    //             }
    //         },
    //         Op::VarX => {
    //             previous_is_multiplier();
    //             let _ = expressions.push(Calc::Expr(token));
    //             if equals_pos == 0 {
    //                 focus_of_eq = Axis::GraphX;
    //             }
    //         },
    //         Op::VarY => {
    //             previous_is_multiplier();
    //             let _ = expressions.push(Calc::Expr(token));
    //             if equals_pos == 0 {
    //                 focus_of_eq = Axis::GraphY;
    //             }
    //         },
    //         Op::Variable => {
    //             previous_is_multiplier();
    //             let _ = expressions.push(Calc::Expr(token));
    //         },
    //         _ => {}
    //     }
    // }
}

fn find_end(input: &[u8], wide: &Token) -> usize {
    let mut last = 0;
    let mut not_my_closing_bracket = 0;
    while let Some(&c) = input.get(last) {
        match (c, wide) {
            (b'(', Token::OpenParen(_)) => { last += 1; not_my_closing_bracket += 1; },
            (b')', Token::OpenParen(_)) => {
                if not_my_closing_bracket > 0 { last += 1; not_my_closing_bracket -= 1; }
                else { break; }
            },
            (_, Token::OpenParen(_)) => last += 1,
            (b'0'..=b'9' | b'.', Token::Number(_)) => last += 1,
            _ => break,
        }
    }
    last
}

// fn previous_is_multiplier(exps: &heapless::Vec<>) {
//     let recent = exps.last();
//     if matches!(recent, Some(Calc::Num(_) | Calc::Expr(Op::Pi | Op::Variable))) {
//         let _ = exps.push(Calc::Expr(Op::Mul));
//     }
// }

// fn push_maybe_negative(exps: &heapless::Vec<>, n: f32) {
//     if exps.last() == Some(&Calc::Expr(Op::Sub)) {
//         let _ = exps.pop();
//         if let Some(&Calc::Num(_)) = exps.last() {
//             let _ = exps.push(Calc::Expr(Op::Add));
//         }
//         let _ = exps.push(Calc::Num(-n));
//     } else {
//         let _ = exps.push(Calc::Num(n));
//     }
// }
