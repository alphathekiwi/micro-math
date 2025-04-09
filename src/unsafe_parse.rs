use core::slice;
use std::mem::MaybeUninit;
use std::ops::{self, Add as _, Div as _, Mul as _, Sub as _};
use std::ptr;

use crate::{NARROW_TOKENS, Op, Token};

const FLOAT_FLAG: u8  = 0b11100000; // Float is always move
const NESTED_FLAG: u8 = 0b10000000;
const VAR_FLAG: u8    = 0b01000000;
const MOVABLE: u8     = 0b00100000; 

macro_rules! tokens_to_ast {
    ($parser:tt, $tokens:tt, $index:tt, $end:tt, $op:ident) => {
        if matches!($tokens.get($index), Some(Token::Operation(Op::$op))) {
            println!("Matched a {:?} {:?} {:?}", &$tokens.get($index-1), Op::$op, &$tokens.get($index+1));
            let mut exp = MicroEquation::new(Op::$op);
            exp.set_right_as_token(&$tokens.remove($index+1));
            exp.set_left_as_token(&$tokens.remove($index-1));
            println!("{:?}", exp);
            for line in exp.render_tree() {
                println!("{}", line);
            }
            let ptr = $parser.ptr_push(exp);
            $tokens[$index-1] = Token::AstPointer(ptr);
            $end -= 2;
        }
    };
    ($parser:tt, $tokens:tt, $index:tt, $end:tt, $($op:ident),*) => {
        match $tokens.get($index) {
            $(
                Some(Token::Operation(Op::$op)) => {
                    println!("Matched a {:?} {:?} {:?}", &$tokens.get($index-1), Op::$op, &$tokens.get($index+1));
                    let mut exp = MicroEquation::new(Op::$op);
                    exp.set_right_as_token(&$tokens.remove($index+1));
                    exp.set_left_as_token(&$tokens.remove($index-1));
                    println!("{:?}", exp);
                    for line in exp.render_tree() {
                        println!("{}", line);
                    }
                    let ptr = $parser.ptr_push(exp);
                    $tokens[$index-1] = Token::AstPointer(ptr);
                    $end -= 2;
                }
            ),*
            _ => {},
        }
    }
}
macro_rules! sctb_to_ast {
    ($parser:tt, $tokens:tt, $index:tt, $($op:ident),*) => {
        match ($tokens.get($index), $tokens.get($index+1), $tokens.get($index+2)) {
            (Some(Token::OpenParen(_)), Some(_), Some(Token::CloseParen(_))) => {
                let _ = &$tokens.remove($index+2);
                let _ = &$tokens.remove($index);
            },
            $((Some(Token::Operation(Op::$op)), Some(_), Some(Token::CloseParen(_))) => {
                println!("Matched a {:?} {:?}", Op::$op, &$tokens.get($index+1));
                let mut exp = MicroEquation::new(Op::$op);
                let _ = &$tokens.remove($index+2);
                let mid = $tokens.remove($index+1);
                exp.set_right_as_token(&mid);
                println!("{:?} {:?}", exp, &mid);
                for line in exp.render_tree() {
                    println!("{}", line);
                }
                let ptr = $parser.ptr_push(exp);
                $tokens[$index] = Token::AstPointer(ptr);
            }),*
            _ => {},
        }
    }
}


use std::cmp::max;

const VARS: &str = "AXY";
impl std::fmt::Display for crate::Op {
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
impl MicroEqValue<'_> {
    pub fn render_tree(&self) -> Vec<String> {
        let mut display: Vec<String> = Vec::new();
        match self {
            MicroEqValue::Float(n) => display.push(format!("{n}")),
            MicroEqValue::Var(v) => display.push(VARS.chars().nth(*v as usize).map(|c| c.to_string()).unwrap_or_else(||{format!("{}", v)}).to_string()),
            MicroEqValue::Nested(micro_equation) => {
                let lines = micro_equation.render_tree();
                for (i, line) in lines.iter().enumerate() {
                    let prefix: String = if i > 1 { (0..(i / 2)).map(|_|{"  "}).collect() } else { "".into() };
                    display.push(format!("{prefix}{}", line));
                }
            },
            MicroEqValue::Unitialized => {},
        }
        display
    }
}
impl 
MicroEquation {
    #[allow(unused)]
    pub fn render_tree(&self) -> Vec<String> {
        let mut display: Vec<String> = Vec::new();
        let (left, right, op) = self.get_values();
        let left = left.render_tree();
        let right = right.render_tree();
        let height = max(left.len(), right.len());
        let (ol, or) = (height-left.len(), height-right.len());
        for i in 0..height {
            match (i>=ol, i>=or) {
                (true, false) => {
                    let val = format!("{}  ", left.get(i-ol).cloned().unwrap_or_default());
                    let (pf, sf) = suffix_postfix(val.len()-3);
                    display.push(val);
                    display.push(format!("{pf}\\{op} {sf}"));
                },
                (false, true) => {
                    let val = format!("  {}", right.get(i-or).cloned().unwrap_or_default());
                    let (pf, sf) = suffix_postfix(val.len()-3);
                    display.push(val);
                    display.push(format!("{pf} {op}/{sf}"));
                },
                _ => {
                    let val = format!("{} {}", 
                        left.get(i-ol).cloned().unwrap_or_default(), 
                        right.get(i-or).cloned().unwrap_or_default()
                    );
                    let (pf, sf) = suffix_postfix(val.len()-3);
                    display.push(val);
                    display.push(format!("{pf}\\{op}/{sf}"));
                },
            }
            // let (wl, wr) = (left.get(i), right.get(i));
            // display.push(format!("{:?} {:?}", left, right));
        }
        display
    }
}
impl<const N: usize> MathParser<N> {
    pub fn render_tree(&self) -> Vec<String> {
        self.last().map(|r|{
            println!("Attempting to render tree {}", self.len());
            println!("{:?}", self.as_slice());
            r.render_tree()
        }).unwrap_or_else(||{
            println!("No final item found {}", self.len());
            println!("{:?}", self.as_slice());
            Vec::new()
        })
    }
}
fn suffix_postfix(len: usize) -> (String, String) {
    if len == 0 { 
        ("".into(), "".into()) 
    } else {
        (0..(len / 2)).map(|_|{(" ", " ")}).collect()
    }
}


// #[repr(C, packed)]
#[repr(u32)]
#[derive(Debug, PartialEq, Copy, Clone)]
#[allow(unused)]
pub enum MicroEqValue<'a> {
    Float(f32) = 3,
    Var(u32) = 2,
    Nested(&'a MicroEquation) = 1,
    Unitialized = 0,
}
#[allow(unused)]
impl MicroEqValue<'_> {
    pub fn solution(&self, vars: &[f32]) -> f32 {
        match self {
            MicroEqValue::Float(f) => *f,
            MicroEqValue::Var(v) => vars.get(*v as usize).copied().unwrap_or(0.0),
            MicroEqValue::Nested(micro_tree) => micro_tree.solution(vars),
            MicroEqValue::Unitialized => 0.0,
        }
    }
}

#[allow(unused)]
fn calculate(left: f32, right: f32, operation: Op) -> f32 {
    match operation {
        Op::Sin => right.sin(),
        Op::ArcSin => right.asin(),
        Op::Cos => right.cos(),
        Op::ArcCos => right.acos(),
        Op::Tan => right.tan(),
        Op::ArcTan => right.atan(),
        Op::Sqrt => right.sqrt(),
        Op::Exp => left.powf(right),
        Op::Mul => left.mul(right),
        Op::Div => left.div(right),
        Op::Mod => left % right,
        Op::Fac => left / 2.0 * (left + 1.0),
        Op::Add => left.add(right),
        Op::Sub => left.sub(right),
        Op::NotOp => 0.0,
    }
}

fn leaf_to_contained<'a>(leaf: usize, flag: u8) -> MicroEqValue<'a> {
    if (flag & FLOAT_FLAG) == FLOAT_FLAG {
        MicroEqValue::Float(f32::from_bits(leaf as u32))
    } else if (flag & VAR_FLAG) == VAR_FLAG {
        MicroEqValue::Var(leaf as u32)
    } else if (flag & NESTED_FLAG) == NESTED_FLAG && leaf != 0 {
        println!("Leaf: {} Flag: {:x}", leaf, flag);
        let ptr: *const MicroEquation = leaf as *const MicroEquation;
        let reference: &MicroEquation = unsafe { &*ptr };
        MicroEqValue::Nested(reference)
    } else {
        MicroEqValue::Unitialized
    }
}

#[allow(unused)]
#[derive(Debug, PartialEq, Copy, Clone)]
pub struct MicroEquation {
    left: usize,
    right: usize,
    left_flags: u8,
    right_flags: u8,
    operation: Op,
}
impl Default for MicroEquation {
    fn default() -> Self {
        MicroEquation {
            left: 0,
            right: 0,
            operation: Op::NotOp,
            left_flags: 0,
            right_flags: 0,
        }
    }
}
#[allow(unused)]
impl MicroEquation {
    fn new(operation: Op) -> Self {
        MicroEquation {
            left: 0,
            right: 0,
            operation,
            left_flags: 0,
            right_flags: 0,
        }
    }

    fn set_left_as_token(&mut self, left: &Token) {
        match left {
            Token::Pi => self.set_left_as_float(core::f32::consts::PI),
            Token::Number(n) => self.set_left_as_float(*n),
            Token::Variable(v) => self.set_left_as_var(*v as u8),
            Token::AstPointer(p) => {
                let ptr: *const MicroEquation = *p as *const MicroEquation;
                let left: &MicroEquation = unsafe { &*ptr };
                if left.is_all_movable() {
                    self.left_flags = NESTED_FLAG | MOVABLE;
                } else {
                    self.left_flags = NESTED_FLAG;
                }
                self.left = *p;
            }
            _ => {}
        }
    }
    fn set_right_as_token(&mut self, right: &Token) {
        match right {
            Token::Pi => self.set_right_as_float(core::f32::consts::PI),
            Token::Number(n) => self.set_right_as_float(*n),
            Token::Variable(v) => self.set_right_as_var(*v as u8),
            Token::AstPointer(p) => {
                let ptr: *const MicroEquation = *p as *const MicroEquation;
                let right: &MicroEquation = unsafe { &*ptr };
                if right.is_all_movable() {
                    self.right_flags = NESTED_FLAG | MOVABLE;
                } else {
                    self.right_flags = NESTED_FLAG;
                }
                self.right = *p;
            }
            _ => {}
        }
    }

    fn set_left_as_nested(&mut self, left: &MicroEquation) {
        if left.is_all_movable() {
            self.left_flags = NESTED_FLAG | MOVABLE;
        } else {
            self.left_flags = NESTED_FLAG;
        }
        self.left = left as *const MicroEquation as usize;
    }
    fn set_left_as_float(&mut self, left: f32) {
        self.left_flags = FLOAT_FLAG;
        self.left = f32::to_bits(left) as usize;
    }
    fn set_left_as_var(&mut self, left: u8) {
        self.left_flags = VAR_FLAG;
        self.left = left as usize;
    }
    fn set_right_as_nested(&mut self, right: &MicroEquation) {
        if right.is_all_movable() {
            self.right_flags = NESTED_FLAG | MOVABLE;
        } else {
            self.right_flags = NESTED_FLAG;
        }
        self.right = right as *const MicroEquation as usize;
    }
    fn set_right_as_float(&mut self, right: f32) {
        self.right_flags = FLOAT_FLAG;
        // println!("float: {} usize: {}", right, right as usize);
        self.right = f32::to_bits(right) as usize;
    }
    fn set_right_as_var(&mut self, right: u8) {
        self.right_flags = VAR_FLAG;
        self.right = right as usize;
    }

    pub fn get_values(&self) -> (MicroEqValue, MicroEqValue, Op) {
        let left = leaf_to_contained(self.left, self.left_flags);
        let right = leaf_to_contained(self.right, self.right_flags);
        (left, right, self.operation)
    }

    // solve this part
    fn solution(&self, vars: &[f32]) -> f32 {
        let left = leaf_to_contained(self.left, self.left_flags).solution(vars);
        let right = leaf_to_contained(self.right, self.right_flags).solution(vars);
        match self.operation {
            Op::Add => left.add(right),
            Op::Sub => left.sub(right),
            Op::Mul => left.mul(right),
            Op::Div => left.div(right),
            Op::Mod => left % right,
            Op::Exp => left.powf(right),
            Op::Sqrt => right.sqrt(),
            Op::Fac => left*(left+1.0)/2.0,
            Op::Sin => right.sin(),
            Op::ArcSin => right.asin(),
            Op::Cos => right.cos(),
            Op::ArcCos => right.acos(),
            Op::Tan => right.tan(),
            Op::ArcTan => right.atan(),
            Op::NotOp => 0.0,
        }
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
            Op::Sqrt => {
                // ^2
                self.left = self.right;
                self.set_right_as_float(2.0);
                Some(Op::Exp)
            }
            Op::Exp => {
                // ^(1/n)
                if let MicroEqValue::Float(val) = leaf_to_contained(self.right, self.right_flags) {
                    self.set_right_as_float(1.0 / val);
                }
                None // Operation doesn't change
            }
            Op::Fac | Op::Mod | Op::NotOp => None, // Modulo and NotOp can't be rebalanced
        };
        if let Some(i) = inv {
            self.operation = i;
        }
    }
    fn is_all_movable(&self) -> bool {
        if matches!(self.operation, Op::Mod) {
            (self.left_flags & self.right_flags & 0xC0) == 0xC0 // 0b00000000
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

pub fn string_to_tokens<const N: usize>(expressions: &mut heapless::Vec<Token, N>, input: &str) {
    let chars = input.chars();
    if let Some(b) = input.chars().next() {
        if matches!(
            Token::from(&b),
            Token::Operation(Op::Add | Op::Mul | Op::Div | Op::Exp | Op::Mod)
        ) {
            // Op::Sub avoided
            // If equation begins with an operation push a previous answer variable in front of it
            expressions.push(Token::Variable(0)).ok();
        }
    }
    let mut current = 0;
    for (i, b) in chars.into_iter().enumerate() {
        if current > i {
            continue;
        }
        let token = Token::from(&b);
        if NARROW_TOKENS.contains(&token) {
            if matches!(token, Token::Operation(Op::Sqrt)) {
                previous_is_multiplier::<N>(expressions);
            }
            expressions.push(token).ok();
        }
        match &token {
            Token::Number(_) => {
                if let Some(remaining) = input.get(i..) {
                    current = i;
                    for c in remaining.chars() {
                        if matches!(c, '0'..='9' | '.') {
                            current += 1;
                        } else { break; }
                    }
                }
                if let Ok(n) = input[i..current].parse::<f32>() {
                    push_maybe_negative::<N>(expressions, n);
                }
            }
            Token::Operation(Op::Sin | Op::Cos | Op::Tan) => {
                previous_is_multiplier::<N>(expressions);
                if matches!(input.chars().nth(i + 1), Some('(')) {
                    expressions.push(token).ok();
                    current = i + 2;
                } else if matches!(
                    (token, input.get(1 + i..i + 4)),
                    (Token::Operation(Op::Sin), Some("in(")) |
                    (Token::Operation(Op::Cos), Some("os(")) |
                    (Token::Operation(Op::Tan), Some("an("))
                ) {
                    expressions.push(token).ok();
                    current = i + 4;
                } else {
                    expressions.push(Token::Variable(b as u32)).ok();
                }
            }
            Token::Operation(Op::ArcCos) => {
                let maybe = match input.get(1 + i..i + 5) {
                    Some("sin(" | "Sin(") => Some(Token::Operation(Op::ArcSin)),
                    Some("cos(" | "Cos(") => Some(Token::Operation(Op::ArcCos)),
                    Some("tan(" | "Tan(") => Some(Token::Operation(Op::ArcTan)),
                    Some(_) | None => None,
                };
                if let Some(t) = maybe {
                    previous_is_multiplier::<N>(expressions);
                    expressions.push(t).ok();
                    current = i + 5;
                }
            }
            Token::Pi => {
                previous_is_multiplier::<N>(expressions);
                push_maybe_negative::<N>(expressions, core::f32::consts::PI);
                if matches!(input.chars().nth(i + 1), Some('0'..='9' | '.')) {
                    expressions.push(Token::Operation(Op::Mul)).ok();
                }
            }
            Token::Variable(_) => {
                previous_is_multiplier::<N>(expressions);
                expressions.push(token).ok();
            }
            Token::OpenParen(_) => {
                previous_is_multiplier::<N>(expressions);
                expressions.push(token).ok();
            }
            Token::CloseParen(_) => {
                expressions.push(token).ok();
            }
            _ => {}
        }
    }
}

fn previous_is_multiplier<const N: usize>(expressions: &mut heapless::Vec<Token, N>) {
    let recent = expressions.last();
    if matches!(
        recent,
        Some(Token::Number(_) | Token::Pi | Token::Variable(_))
    ) {
        let _ = expressions.push(Token::Operation(Op::Mul));
    }
}

fn push_maybe_negative<const N: usize>(expressions: &mut heapless::Vec<Token, N>, n: f32) {
    if expressions.last() == Some(&Token::Operation(Op::Sub)) {
        let _ = expressions.pop();
        if let Some(&Token::Number(_)) = expressions.last() {
            let _ = expressions.push(Token::Operation(Op::Add));
        }
        let _ = expressions.push(Token::Number(-n));
    } else {
        let _ = expressions.push(Token::Number(n));
    }
}

#[allow(unused)]
fn find_end(input: &[u8], wide: &Token) -> usize {
    let mut last = 0;
    let mut not_my_closing_bracket = 0;
    while let Some(&c) = input.get(last) {
        match (c, wide) {
            (b'(', Token::OpenParen(_)) => {
                last += 1;
                not_my_closing_bracket += 1;
            }
            (b')', Token::OpenParen(_)) => {
                if not_my_closing_bracket > 0 {
                    last += 1;
                    not_my_closing_bracket -= 1;
                } else {
                    break;
                }
            }
            (_, Token::OpenParen(_)) => last += 1,
            (b'0'..=b'9' | b'.', Token::Number(_)) => last += 1,
            _ => break,
        }
    }
    last
}

#[allow(unused)]
pub struct MathParser<const N: usize> {
    len: usize,
    // pub(crate) focus_of_eq: crate::graphing::Axis,
    pub(crate) equals_pos: usize,
    pub(crate) cached_ans: Option<f32>,
    equation: [MaybeUninit<MicroEquation>; N],
}
impl<const N: usize> MathParser<N> {
    const ELEM: MaybeUninit<MicroEquation> = MaybeUninit::uninit();
    const INIT: [MaybeUninit<MicroEquation>; N] = [Self::ELEM; N];

    pub fn new(input: &str) -> Self {
        let equals_pos = input.find('=').unwrap_or_default();
        let mut parser = MathParser {
            len: 0,
            // focus_of_eq: crate::graphing::Axis::NoFocus,
            equals_pos,
            cached_ans: None,
            equation: Self::INIT,
        };
        {
            parser.parse_expression(input);
        }
        parser
    }

    #[allow(unused)]
    fn parse_expression(&mut self, input: &str) {
        if self.equals_pos > 0 && self.equals_pos < input.len() - 1 {
            let (left, right) = input.split_at(self.equals_pos);
            let left_ex = self.parse_expression_side(left);
            let right_ex = self.parse_expression_side(right);

            let mut root = MicroEquation::default();
            root.set_left_as_nested(&left_ex);
            root.set_right_as_nested(&right_ex);
        } else {
            if let Some(b) = input.chars().next() {
                if matches!(
                    Op::from(&b),
                    Op::Add | Op::Mul | Op::Div | Op::Exp | Op::Mod | Op::Sub
                ) {
                    // If equation begins with an operation push a variable in front of it
                    let mut exp = MicroEquation::new(Op::Add);
                    exp.set_left_as_var(0);
                    self.push(exp);
                }
            }
            let root = self.parse_expression_side(input);
        }
    }
    #[allow(unused)]
    fn parse_expression_side(&mut self, input: &str) -> MicroEquation {
        let mut tokens: heapless::Vec<Token, N> = heapless::Vec::new();
        string_to_tokens::<N>(&mut tokens, input);
        let end = tokens.len();
        for start in (0..end).rev() {
            if matches!(
                tokens.get(start),
                Some(
                    Token::OpenParen(_)
                        | Token::Operation(
                            Op::Sin | Op::ArcSin | Op::Cos | Op::ArcCos | Op::Tan | Op::ArcTan
                        )
                )
            ) {
                if let Some(sub_slice) = tokens.get(start..) {
                    let end = tokens.len();
                    for end in 0..end {
                        if matches!(tokens.get(end), Some(Token::CloseParen(_))) {
                            self.section_to_ast(&mut tokens, start, end);
                        }
                    }
                }
            }
        }
        let end = tokens.len();
        self.section_to_ast(&mut tokens, 0, end);
        MicroEquation::default()
    }
    fn section_to_ast(&mut self, tokens: &mut heapless::Vec<Token, N>, start: usize, end: usize) {
        // Exponents evaluate Right to Left
        let mut end2 = end;
        for index in (start..end).rev() {
            tokens_to_ast!(self, tokens, index, end2, Sqrt, Exp)
        }
        let mut end3 = end2;
        for index in start..end2 {
            tokens_to_ast!(self, tokens, index, end3, Mul, Div, Mod, Fac)
        }
        let mut end4 = end3;
        for index in start..end3 {
            tokens_to_ast!(self, tokens, index, end4, Add, Sub)
        }
        for index in (start..end4).rev() {
            sctb_to_ast!(self, tokens, index, Sin, ArcSin, Cos, ArcCos, Tan, ArcTan)
        }
    }
    #[allow(unused)]
    unsafe fn ptr_push_unchecked(&mut self, item: MicroEquation) -> usize {
        debug_assert!(!self.is_full());
        let mut mem_slot = *unsafe { self.equation.get_unchecked_mut(self.len) };
        mem_slot.write(item);
        self.len += 1;
        mem_slot.as_ptr() as usize
    }
    #[allow(unused)]
    fn ptr_push(&mut self, val: MicroEquation) -> usize {
        if self.len < self.capacity() {
            unsafe { self.ptr_push_unchecked(val) }
        } else {
            0
        }
    }
}





// FURTHER IMPLEMENTATIONS
#[allow(unused, clippy::result_unit_err, clippy::missing_safety_doc)]
impl<const N: usize> MathParser<N> {
    #[inline]
    pub fn from_slice(other: &[MicroEquation]) -> Result<Self, ()> {
        let mut v = MathParser::default();
        v.extend_from_slice(other).ok();
        Ok(v)
    }
    pub(crate) fn clone(&self) -> Self {
        let mut new = Self::default();
        // avoid `extend_from_slice` as that introduces a runtime check / panicking branch
        for elem in self {
            unsafe {
                new.push_unchecked(*elem);
            }
        }
        new
    }
    pub fn as_ptr(&self) -> *const MicroEquation {
        self.equation.as_ptr() as *const MicroEquation
    }
    pub fn as_mut_ptr(&mut self) -> *mut MicroEquation {
        self.equation.as_mut_ptr() as *mut MicroEquation
    }

    pub fn as_slice(&self) -> &[MicroEquation] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &equation[..self.len]
        unsafe { slice::from_raw_parts(self.equation.as_ptr() as *const MicroEquation, self.len) }
    }

    pub fn into_array<const M: usize>(self) -> Result<[MicroEquation; M], Self> {
        if self.len() == M {
            // This is how the unstable `MaybeUninit::array_assume_init` method does it
            let array = unsafe { (&self.equation as *const _ as *const [MicroEquation; M]).read() };

            // We don't want `self`'s destructor to be called because that would drop all the
            // items in the array
            core::mem::forget(self);

            Ok(array)
        } else {
            Err(self)
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [MicroEquation] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &mut equation[..self.len]
        unsafe {
            slice::from_raw_parts_mut(self.equation.as_mut_ptr() as *mut MicroEquation, self.len)
        }
    }
    pub const fn capacity(&self) -> usize {
        N
    }
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = MicroEquation>,
    {
        for elem in iter {
            self.push(elem).ok().unwrap()
        }
    }

    pub fn extend_from_slice(&mut self, other: &[MicroEquation]) -> Result<(), ()> {
        if self.len + other.len() > self.capacity() {
            // won't fit in the `Vec`; don't modify anything and return an error
            Err(())
        } else {
            for elem in other {
                unsafe {
                    self.push_unchecked(*elem);
                }
            }
            Ok(())
        }
    }
    pub fn pop(&mut self) -> Option<MicroEquation> {
        if self.len != 0 {
            Some(unsafe { self.pop_unchecked() })
        } else {
            None
        }
    }

    pub fn push(&mut self, item: MicroEquation) -> Result<(), MicroEquation> {
        if self.len < self.capacity() {
            unsafe { self.push_unchecked(item) }
            Ok(())
        } else {
            Err(item)
        }
    }

    pub unsafe fn pop_unchecked(&mut self) -> MicroEquation {
        debug_assert!(!self.is_empty());

        self.len -= 1;
        unsafe { self.equation.get_unchecked_mut(self.len).as_ptr().read() }
    }

    pub unsafe fn push_unchecked(&mut self, item: MicroEquation) {
        // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
        // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
        debug_assert!(!self.is_full());

        *unsafe { self.equation.get_unchecked_mut(self.len) } = MaybeUninit::new(item);

        self.len += 1;
    }
    pub fn truncate(&mut self, len: usize) {
        // This is safe because:
        //
        // * the slice passed to `drop_in_place` is valid; the `len > self.len`
        //   case avoids creating an invalid slice, and
        // * the `len` of the vector is shrunk before calling `drop_in_place`,
        //   such that no value will be dropped twice in case `drop_in_place`
        //   were to panic once (if it panics twice, the program aborts).
        unsafe {
            // Note: It's intentional that this is `>` and not `>=`.
            //       Changing it to `>=` has negative performance
            //       implications in some cases. See rust-lang/rust#78884 for more.
            if len > self.len {
                return;
            }
            let remaining_len = self.len - len;
            let s = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), remaining_len);
            self.len = len;
            ptr::drop_in_place(s);
        }
    }

    pub fn resize(&mut self, new_len: usize, value: MicroEquation) -> Result<(), ()>
    where
        MicroEquation: Clone,
    {
        if new_len > self.capacity() {
            return Err(());
        }

        if new_len > self.len {
            while self.len < new_len {
                self.push(value).ok();
            }
        } else {
            self.truncate(new_len);
        }

        Ok(())
    }

    pub fn resize_default(&mut self, new_len: usize) -> Result<(), ()>
    where
        MicroEquation: Clone + Default,
    {
        self.resize(new_len, MicroEquation::default())
    }

    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        self.len = new_len
    }

    pub fn swap_remove(&mut self, index: usize) -> MicroEquation {
        assert!(index < self.len);
        unsafe { self.swap_remove_unchecked(index) }
    }

    pub unsafe fn swap_remove_unchecked(&mut self, index: usize) -> MicroEquation {
        let length = self.len();
        debug_assert!(index < length);
        let value = unsafe { ptr::read(self.as_ptr().add(index)) };
        let base_ptr = self.as_mut_ptr();
        unsafe { ptr::copy(base_ptr.add(length - 1), base_ptr.add(index), 1) };
        self.len -= 1;
        value
    }
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len == self.capacity()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn starts_with(&self, needle: &[MicroEquation]) -> bool
    where
        MicroEquation: PartialEq,
    {
        let n = needle.len();
        self.len >= n && needle == &self[..n]
    }

    #[inline]
    pub fn ends_with(&self, needle: &[MicroEquation]) -> bool
    where
        MicroEquation: PartialEq,
    {
        let (v, n) = (self.len(), needle.len());
        v >= n && needle == &self[v - n..]
    }

    pub fn insert(&mut self, index: usize, element: MicroEquation) -> Result<(), MicroEquation> {
        let len = self.len();
        if index > len {
            panic!(
                "insertion index (is {}) should be <= len (is {})",
                index, len
            );
        }

        // check there's space for the new element
        if self.is_full() {
            return Err(element);
        }

        unsafe {
            // infallible
            // The spot to put the new value
            {
                let p = self.as_mut_ptr().add(index);
                // Shift everything over to make space. (Duplicating the
                // `index`th element into two consecutive places.)
                ptr::copy(p, p.offset(1), len - index);
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(p, element);
            }
            self.set_len(len + 1);
        }

        Ok(())
    }

    pub fn remove(&mut self, index: usize) -> MicroEquation {
        let len = self.len();
        if index >= len {
            panic!("removal index (is {}) should be < len (is {})", index, len);
        }
        unsafe {
            // infallible
            let ret;
            {
                // the place we are taking from.
                let ptr = self.as_mut_ptr().add(index);
                // copy it out, unsafely having a copy of the value on
                // the stack and in the vector at the same time.
                ret = ptr::read(ptr);

                // Shift everything down to fill in that spot.
                ptr::copy(ptr.offset(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            ret
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&MicroEquation) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut MicroEquation) -> bool,
    {
        let original_len = self.len();
        // Avoid double drop if the drop guard is not executed,
        // since we may make some holes during the process.
        unsafe { self.set_len(0) };

        // Vec: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
        //      |<-              processed len   ->| ^- next to check
        //                  |<-  deleted cnt     ->|
        //      |<-              original_len                          ->|
        // Kept: Elements which predicate returns true on.
        // Hole: Moved or dropped element slot.
        // Unchecked: Unchecked valid elements.
        //
        // This drop guard will be invoked when predicate or `drop` of element panicked.
        // It shifts unchecked elements to cover holes and `set_len` to the correct length.
        // In cases when predicate and `drop` never panick, it will be optimized out.
        struct BackshiftOnDrop<'a, const N: usize> {
            v: &'a mut MathParser<N>,
            processed_len: usize,
            deleted_cnt: usize,
            original_len: usize,
        }

        impl<const N: usize> Drop for BackshiftOnDrop<'_, N> {
            fn drop(&mut self) {
                if self.deleted_cnt > 0 {
                    // SAFETY: MicroEquationrailing unchecked items must be valid since we never touch them.
                    unsafe {
                        ptr::copy(
                            self.v.as_ptr().add(self.processed_len),
                            self.v
                                .as_mut_ptr()
                                .add(self.processed_len - self.deleted_cnt),
                            self.original_len - self.processed_len,
                        );
                    }
                }
                // SAFETY: After filling holes, all items are in contiguous memory.
                unsafe {
                    self.v.set_len(self.original_len - self.deleted_cnt);
                }
            }
        }

        let mut g = BackshiftOnDrop {
            v: self,
            processed_len: 0,
            deleted_cnt: 0,
            original_len,
        };

        fn process_loop<F, const N: usize, const DELETED: bool>(
            original_len: usize,
            f: &mut F,
            g: &mut BackshiftOnDrop<'_, N>,
        ) where
            F: FnMut(&mut MicroEquation) -> bool,
        {
            while g.processed_len != original_len {
                let p = g.v.as_mut_ptr();
                // SAFETY: Unchecked element must be valid.
                let cur = unsafe { &mut *p.add(g.processed_len) };
                if !f(cur) {
                    // Advance early to avoid double drop if `drop_in_place` panicked.
                    g.processed_len += 1;
                    g.deleted_cnt += 1;
                    // SAFETY: We never touch this element again after dropped.
                    unsafe { ptr::drop_in_place(cur) };
                    // We already advanced the counter.
                    if DELETED {
                        continue;
                    } else {
                        break;
                    }
                }
                if DELETED {
                    // SAFETY: `deleted_cnt` > 0, so the hole slot must not overlap with current element.
                    // We use copy for move, and never touch this element again.
                    unsafe {
                        let hole_slot = p.add(g.processed_len - g.deleted_cnt);
                        ptr::copy_nonoverlapping(cur, hole_slot, 1);
                    }
                }
                g.processed_len += 1;
            }
        }

        // Stage 1: Nothing was deleted.
        process_loop::<F, N, false>(original_len, &mut f, &mut g);

        // Stage 2: Some elements were deleted.
        process_loop::<F, N, true>(original_len, &mut f, &mut g);

        // All item are processed. This can be optimized to `set_len` by LLVM.
        drop(g);
    }
}

impl<const N: usize> Default for MathParser<N> {
    fn default() -> Self {
        Self {
            len: 0,
            equals_pos: 0,
            cached_ans: None,
            equation: Self::INIT,
        }
    }
}

impl<const N: usize> Drop for MathParser<N> {
    fn drop(&mut self) {
        // We drop each element used in the vector by turning into a &mut[MicroEquation]
        unsafe {
            ptr::drop_in_place(self.as_mut_slice());
        }
    }
}

impl<'a, const N: usize> TryFrom<&'a [MicroEquation]> for MathParser<N> {
    type Error = ();

    fn try_from(slice: &'a [MicroEquation]) -> Result<Self, Self::Error> {
        MathParser::from_slice(slice)
    }
}

impl<const N: usize> Extend<MicroEquation> for MathParser<N> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = MicroEquation>,
    {
        self.extend(iter)
    }
}

impl<'a, const N: usize> Extend<&'a MicroEquation> for MathParser<N> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a MicroEquation>,
    {
        self.extend(iter.into_iter().cloned())
    }
}

impl<'a, const N: usize> IntoIterator for &'a MathParser<N> {
    type Item = &'a MicroEquation;
    type IntoIter = slice::Iter<'a, MicroEquation>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, const N: usize> IntoIterator for &'a mut MathParser<N> {
    type Item = &'a mut MicroEquation;
    type IntoIter = slice::IterMut<'a, MicroEquation>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<const N: usize> FromIterator<MicroEquation> for MathParser<N> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = MicroEquation>,
    {
        let mut vec = MathParser::default();
        for i in iter {
            vec.push(i).expect("MathParser::from_iter overflow");
        }
        vec
    }
}
pub struct IntoIter<const N: usize> {
    vec: MathParser<N>,
    next: usize,
}

impl<const N: usize> Iterator for IntoIter<N> {
    type Item = MicroEquation;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next < self.vec.len() {
            let item = unsafe {
                self.vec.equation.get_unchecked_mut(self.next).as_ptr()
                    .read()
            };
            self.next += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl<const N: usize> Clone for IntoIter<N> {
    fn clone(&self) -> Self {
        let mut vec = MathParser::default();

        if self.next < self.vec.len() {
            let s = unsafe {
                slice::from_raw_parts(
                    (self.vec.equation.as_ptr() as *const MicroEquation).add(self.next),
                    self.vec.len() - self.next,
                )
            };
            vec.extend_from_slice(s).ok();
        }

        Self { vec, next: 0 }
    }
}

impl<const N: usize> Drop for IntoIter<N> {
    fn drop(&mut self) {
        unsafe {
            // Drop all the elements that have not been moved out of vec
            ptr::drop_in_place(&mut self.vec.as_mut_slice()[self.next..]);
            // Prevent dropping of other elements
            self.vec.len = 0;
        }
    }
}

impl<const N: usize> IntoIterator for MathParser<N> {
    type Item = MicroEquation;
    type IntoIter = IntoIter<N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { vec: self, next: 0 }
    }
}

impl<const N1: usize, const N2: usize> PartialEq<MathParser<N2>> for MathParser<N1>
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &MathParser<N2>) -> bool {
        <[MicroEquation]>::eq(self, &**other)
    }
}

// MathParser<N> == [MicroEquation]
impl<const N: usize> PartialEq<[MicroEquation]> for MathParser<N>
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &[MicroEquation]) -> bool {
        <[MicroEquation]>::eq(self, other)
    }
}

// [MicroEquation] == MathParser<N>
impl<const N: usize> PartialEq<MathParser<N>> for [MicroEquation]
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &MathParser<N>) -> bool {
        <[MicroEquation]>::eq(other, self)
    }
}

// MathParser<N> == &[MicroEquation]
impl<const N: usize> PartialEq<&[MicroEquation]> for MathParser<N>
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &&[MicroEquation]) -> bool {
        <[MicroEquation]>::eq(self, &other[..])
    }
}

// &[MicroEquation] == MathParser<N>
impl<const N: usize> PartialEq<MathParser<N>> for &[MicroEquation]
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &MathParser<N>) -> bool {
        <[MicroEquation]>::eq(other, &self[..])
    }
}

// MathParser<N> == &mut [MicroEquation]
impl<const N: usize> PartialEq<&mut [MicroEquation]> for MathParser<N>
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &&mut [MicroEquation]) -> bool {
        <[MicroEquation]>::eq(self, &other[..])
    }
}

// &mut [MicroEquation] == MathParser<N>
impl<const N: usize> PartialEq<MathParser<N>> for &mut [MicroEquation]
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &MathParser<N>) -> bool {
        <[MicroEquation]>::eq(other, &self[..])
    }
}

// MathParser<N> == [MicroEquation; M]
// Equality does not require equal capacity
impl<const N: usize, const M: usize> PartialEq<[MicroEquation; M]> for MathParser<N>
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &[MicroEquation; M]) -> bool {
        <[MicroEquation]>::eq(self, &other[..])
    }
}

// [MicroEquation; M] == MathParser<N>
// Equality does not require equal capacity
impl<const N: usize, const M: usize> PartialEq<MathParser<N>> for [MicroEquation; M]
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &MathParser<N>) -> bool {
        <[MicroEquation]>::eq(other, &self[..])
    }
}

// MathParser<N> == &[MicroEquation; M]
// Equality does not require equal capacity
impl<const N: usize, const M: usize> PartialEq<&[MicroEquation; M]> for MathParser<N>
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &&[MicroEquation; M]) -> bool {
        <[MicroEquation]>::eq(self, &other[..])
    }
}

// &[MicroEquation; M] == MathParser<N>
// Equality does not require equal capacity
impl<const N: usize, const M: usize> PartialEq<MathParser<N>> for &[MicroEquation; M]
where
    MicroEquation: PartialEq<MicroEquation>,
{
    fn eq(&self, other: &MathParser<N>) -> bool {
        <[MicroEquation]>::eq(other, &self[..])
    }
}

// Implements Eq if underlying data is Eq
// impl<const N: usize> Eq for MathParser<N> where MicroEquation: Eq {}

// impl<const N1: usize, const N2: usize> PartialOrd<MathParser<N2>> for MathParser<N1>
// where
//     MicroEquation: PartialOrd,
// {
//     fn partial_cmp(&self, other: &MathParser<N2>) -> Option<Ordering> {
//         PartialOrd::partial_cmp(&**self, &**other)
//     }
// }

// impl<const N: usize> Ord for MathParser<N>
// where
//     MicroEquation: Ord,
// {
//     #[inline]
//     fn cmp(&self, other: &Self) -> Ordering {
//         Ord::cmp(&**self, &**other)
//     }
// }

impl<const N: usize> ops::Deref for MathParser<N> {
    type Target = [MicroEquation];

    fn deref(&self) -> &[MicroEquation] {
        self.as_slice()
    }
}

impl<const N: usize> ops::DerefMut for MathParser<N> {
    fn deref_mut(&mut self) -> &mut [MicroEquation] {
        self.as_mut_slice()
    }
}

impl<const N: usize> AsRef<MathParser<N>> for MathParser<N> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<const N: usize> AsMut<MathParser<N>> for MathParser<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<const N: usize> AsRef<[MicroEquation]> for MathParser<N> {
    #[inline]
    fn as_ref(&self) -> &[MicroEquation] {
        self
    }
}

impl<const N: usize> AsMut<[MicroEquation]> for MathParser<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [MicroEquation] {
        self
    }
}

impl<const N: usize> Clone for MathParser<N>
where
    MicroEquation: Clone,
{
    fn clone(&self) -> Self {
        self.clone()
    }
}
