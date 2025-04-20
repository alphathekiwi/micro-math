use crate::equation::MathParser;
use crate::{AbstractSnytaxTree, Equation, MicroVal, Op, Token};
use crate::{FLOAT_FLAG, MOVABLE, NESTED_FLAG, VAR_FLAG};

#[derive(Debug, PartialEq, Copy, Clone)]
pub struct SaferAst<'a> {
    left: MicroVal<'a, SaferAst<'a>>,
    right: MicroVal<'a, SaferAst<'a>>,
    left_flags: u8,
    right_flags: u8,
    op: Op,
}
impl Default for SaferAst<'_> {
    fn default() -> Self {
        SaferAst {
            left: MicroVal::Unitialized,
            right: MicroVal::Unitialized,
            op: Op::NotOp,
            left_flags: 0,
            right_flags: 0,
        }
    }
}

impl<'a> AbstractSnytaxTree for SaferAst<'a> {
    type A = SaferAst<'a>;
    fn with_op(op: Op) -> Self {
        Self {
            op,
            ..Default::default()
        }
    }

    fn solve(&self, vars: &[f32]) -> f32 {
        let (left, right, op) = self.get_values();
        crate::calculation::calculate(left.solve(vars), right.solve(vars), op)
    }

    fn set_left(&mut self, val: &Token<SaferAst>) {
        match val {
            Token::Pi => {
                self.left_flags = FLOAT_FLAG;
                self.left = MicroVal::Float(core::f32::consts::PI);
            }
            Token::Number(n) => {
                self.left_flags = FLOAT_FLAG;
                self.left = MicroVal::Float(*n);
            }
            Token::Variable(v) => {
                self.left_flags = VAR_FLAG;
                self.left = MicroVal::Var(*v);
            }
            Token::AstPointer(left) => {
                let ptr: *const SaferAst = left as *const SaferAst;
                let left: SaferAst = unsafe { *ptr };
                let left: &'a SaferAst = &left as &'a SaferAst;
                if left.is_all_movable() {
                    self.left_flags = NESTED_FLAG | MOVABLE;
                } else {
                    self.left_flags = NESTED_FLAG;
                }
                self.left = MicroVal::Nested(left);
            }
            _ => {}
        }
    }

    fn set_right(&mut self, val: &Token<SaferAst>) {
        match val {
            Token::Pi => {
                self.right_flags = FLOAT_FLAG;
                self.right = MicroVal::Float(core::f32::consts::PI);
            }
            Token::Number(n) => {
                self.right_flags = FLOAT_FLAG;
                self.right = MicroVal::Float(*n);
            }
            Token::Variable(v) => {
                self.right_flags = VAR_FLAG;
                self.right = MicroVal::Var(*v);
            }
            Token::AstPointer(p) => {
                let ptr: *const SaferAst = *p as *const SaferAst;
                let right: &'static SaferAst = unsafe { &*ptr };
                if right.is_all_movable() {
                    self.right_flags = NESTED_FLAG | MOVABLE;
                } else {
                    self.right_flags = NESTED_FLAG;
                }
                self.right = MicroVal::Nested(right);
            }
            _ => {}
        }
    }

    fn get_values(&self) -> (MicroVal<Self>, MicroVal<Self>, Op) {
        (self.left, self.right, self.op)
    }

    fn set_operation(&mut self, op: Op) {
        self.op = op
    }

    fn get_flags(&self) -> (u8, u8, Op) {
        (self.left_flags, self.right_flags, self.op)
    }

    fn left_flags(&self) -> u8 {
        self.left_flags
    }
    fn right_flags(&self) -> u8 {
        self.right_flags
    }
}


macro_rules! tokens_to_ast {
    ($parser:tt, $tokens:tt, $index:tt, $end:tt, $fallthrough:tt, $op:ident) => {
        if matches!($tokens.get($index), Some(Token::Operation(Op::$op))) {
            // println!("Matched a {:?} {:?} {:?}", &$tokens.get($index-1), Op::$op, &$tokens.get($index+1));
            let mut exp = SaferAst::with_op(Op::$op);
            exp.set_right(&$tokens.remove($index+1));
            exp.set_left(&$tokens.remove($index-1));
            // println!("{:?}", exp);
            // for line in exp.render_tree() {
            //     println!("{}", line);
            // }
            let ptr = $parser.left_ptr_push(exp);
            $tokens[$index-1] = Token::AstPointer(ptr);
            $end -= 2;
        } else $fallthrough
    };
    ($parser:tt, $tokens:tt, $index:tt, $end:tt, $fallthrough:tt, $($op:ident),*) => {
        match $tokens.get($index) {
            $(
                Some(Token::Operation(Op::$op)) => {
                    // println!("Matched a {:?} {:?} {:?}", &$tokens.get($index-1), Op::$op, &$tokens.get($index+1));
                    let mut exp = SaferAst::with_op(Op::$op);
                    exp.set_right(&$tokens.remove($index+1));
                    exp.set_left(&$tokens.remove($index-1));
                    // println!("{:?}", exp);
                    // for line in exp.render_tree() {
                    //     println!("{}", line);
                    // }
                    let ptr = $parser.left_ptr_push(exp);
                    $tokens[$index-1] = Token::AstPointer(ptr);
                    $end -= 2;
                }
            ),*
            _ => $fallthrough,
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
                // println!("Matched a {:?} {:?}", Op::$op, &$tokens.get($index+1));
                let mut exp = SaferAst::with_op(Op::$op);
                let _ = &$tokens.remove($index+2);
                let mid = $tokens.remove($index+1);
                exp.set_right(&mid);
                // println!("{:?} {:?}", exp, &mid);
                // for line in exp.render_tree() {
                //     println!("{}", line);
                // }
                let ptr = $parser.left_ptr_push(exp);
                $tokens[$index] = Token::AstPointer(ptr);
            }),*
            _ => {},
        }
    }
}

///  NOTE:  The main implementation for the safer parser
impl<'a, const N: usize> MathParser<SaferAst<'a>, N> { 
    pub fn all_values_and_pointers(&self) {
        for i in 0..self.len() {
            let ptr: *const SaferAst = self.equation[i].as_ptr();
            println!("[{}]: {:?}", ptr as usize, self.get(i))
        }
    }

    /// Note: that `Self::equals_pos` will not be set and may need initializing first
    pub fn parse_expression(&mut self, input: &str) {
        let equals_pos = input.find('=').unwrap_or_default();

        if equals_pos > 0 && equals_pos < input.len() - 1 {
            let (left, right) = input.split_at(equals_pos);
            let left_ex = self.parse_expression_side(left);
            let left_tk = Token::AstPointer(&left_ex as *const SaferAst<'static> as usize);
            let right_ex = self.parse_expression_side(right);
            let right_tk = Token::AstPointer(&right_ex as *const SaferAst<'static> as usize);
            let mut root = SaferAst::default();
            root.set_left(&left_tk);
            root.set_right(&right_tk);
            self.left_ptr_push(root);
        } else {
            if let Some(Some(op)) = input.chars().next().map(Op::recurs_on_ans) {
                let mut exp = SaferAst::with_op(op);
                exp.set_left(&Token::Variable(0));
                self.left_ptr_push(exp);
            }
            self.parse_expression_side(input);
        }
    }

    /// If operating on a balanced equation like
    fn parse_expression_side(&mut self, input: &str) -> SaferAst {
        let mut tokens: heapless::Vec<Token<SaferAst>, N> = heapless::Vec::new();
        crate::str_parse::string_to_tokens::<SaferAst, N>(&mut tokens, input);
        let end = tokens.len();
        println!("{:?} {}", tokens, end);
        for start in (0..end).rev() {
            if matches!(
                tokens.get(start),
                Some(
                    Token::OpenParen(_)
                        | Token::Operation(Op::Sin | Op::ArcSin)
                        | Token::Operation(Op::Cos | Op::ArcCos)
                        | Token::Operation(Op::Tan | Op::ArcTan)
                )
            ) {
                let tokens_len = tokens.len();
                for end in start..tokens_len {
                    if matches!(tokens.get(end), Some(Token::CloseParen(_))) {
                        println!("Found parens at {start} {end}");
                        self.section_to_ast(&mut tokens, start, end);
                        break;
                    }
                }
            }
        }
        let end = tokens.len();
        self.section_to_ast(&mut tokens, 0, end);
        unsafe { *self.get_unchecked(self.l_len) }
    }

    /// Takes a mutable reference to a token vec with a start and end and attempts to pop elements from it and place them into a
    fn section_to_ast(&mut self, tokens: &mut heapless::Vec<Token<SaferAst>, N>, start: usize, end: usize) {
        // Exponents evaluate Right to Left
        let mut end = end;
        for index in (start..end).rev() {
            tokens_to_ast!(self, tokens, index, end, {}, Sqrt, Exp)
        }
        // let mut end3 = end2;
        // for index in start..end2 {
        //     tokens_to_ast!(self, tokens, index, end3, Mul, Div, Mod, Fac)
        // }
        let mut index = start;
        while end > start && index < end {
            tokens_to_ast!(self, tokens, index, end, { index += 1 }, Mul, Div, Mod, Fac)
        }
        let mut index = start;
        while end > start && index < end {
            tokens_to_ast!(self, tokens, index, end, { index += 1 }, Add, Sub)
        }
        // for index in start..end3 {
        //     tokens_to_ast!(self, tokens, index, basics_end, Add, Sub)
        // }

        //  NOTE:  Brackets and Sin... are put on last as sections_to_ast will pass
        // sections begining and ending with these values so in reality they are at the first position
        for index in (start..end).rev() {
            sctb_to_ast!(self, tokens, index, Sin, ArcSin, Cos, ArcCos, Tan, ArcTan)
        }
    }
}