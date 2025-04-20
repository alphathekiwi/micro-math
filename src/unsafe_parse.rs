use crate::equation::MathParser;
use crate::{AbstractSnytaxTree, Equation, MicroVal, Op, Token};
use crate::{FLOAT_FLAG, MOVABLE, NESTED_FLAG, VAR_FLAG};

fn leaf_to_contained<'a>(leaf: usize, flag: u8) -> MicroVal<'a, UnsafeAst> {
    if (flag & FLOAT_FLAG) == FLOAT_FLAG {
        MicroVal::Float(f32::from_bits(leaf as u32))
    } else if (flag & VAR_FLAG) == VAR_FLAG {
        MicroVal::Var(leaf as u32)
    } else if (flag & NESTED_FLAG) == NESTED_FLAG && leaf != 0 {
        println!("Leaf: {} Flag: {:x}", leaf, flag);
        let ptr: *const UnsafeAst = leaf as *const UnsafeAst;
        let reference: &UnsafeAst = unsafe { &*ptr };
        MicroVal::Nested(reference)
    } else {
        MicroVal::Unitialized
    }
}

#[derive(Debug, PartialEq, Copy, Clone, Default)]
pub struct UnsafeAst {
    left: usize,
    right: usize,
    left_flags: u8,
    right_flags: u8,
    op: Op,
}
impl UnsafeAst {
    fn with_op(op: Op) -> Self {
        Self {
            op,
            ..Default::default()
        }
    }
}
impl AbstractSnytaxTree for UnsafeAst {
    type A = usize;
    fn solve(&self, vars: &[f32]) -> f32 {
        let left = leaf_to_contained(self.left, self.left_flags).solve(vars);
        let right = leaf_to_contained(self.right, self.right_flags).solve(vars);
        crate::calculation::calculate(left, right, self.op)
    }

    fn set_left(&mut self, left: &Token<usize>) {
        match left {
            Token::Pi => self.set_left_as_float(core::f32::consts::PI),
            Token::Number(n) => self.set_left_as_float(*n),
            Token::Variable(v) => self.set_left_as_var(*v as u8),
            Token::AstPointer(p) => {
                let ptr: *const UnsafeAst = *p as *const UnsafeAst;
                let left: &UnsafeAst = unsafe { &*ptr };
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
    fn set_right(&mut self, right: &Token<usize>) {
        match right {
            Token::Pi => self.set_right_as_float(core::f32::consts::PI),
            Token::Number(n) => self.set_right_as_float(*n),
            Token::Variable(v) => self.set_right_as_var(*v as u8),
            Token::AstPointer(p) => {
                let ptr: *const UnsafeAst = *p as *const UnsafeAst;
                let right: &UnsafeAst = unsafe { &*ptr };
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

    fn get_values(&self) -> (MicroVal<Self>, MicroVal<Self>, Op) {
        let left = leaf_to_contained(self.left, self.left_flags);
        let right = leaf_to_contained(self.right, self.right_flags);
        (left, right, self.op)
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
impl UnsafeAst {
    #[allow(unused)]
    fn new() -> Self {
        UnsafeAst {
            left: 0,
            right: 0,
            op: Op::NotOp,
            left_flags: 0,
            right_flags: 0,
        }
    }

    fn set_left_as_nested(&mut self, left: &UnsafeAst) {
        if left.is_all_movable() {
            self.left_flags = NESTED_FLAG | MOVABLE;
        } else {
            self.left_flags = NESTED_FLAG;
        }
        self.left = left as *const UnsafeAst as usize;
    }
    fn set_left_as_float(&mut self, left: f32) {
        self.left_flags = FLOAT_FLAG;
        self.left = f32::to_bits(left) as usize;
    }
    fn set_left_as_var(&mut self, left: u8) {
        self.left_flags = VAR_FLAG;
        self.left = left as usize;
    }
    fn set_right_as_nested(&mut self, right: &UnsafeAst) {
        if right.is_all_movable() {
            self.right_flags = NESTED_FLAG | MOVABLE;
        } else {
            self.right_flags = NESTED_FLAG;
        }
        self.right = right as *const UnsafeAst as usize;
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
}



macro_rules! tokens_to_ast {
    ($parser:tt, $tokens:tt, $index:tt, $end:tt, $fallthrough:tt, $op:ident) => {
        if matches!($tokens.get($index), Some(Token::Operation(Op::$op))) {
            // println!("Matched a {:?} {:?} {:?}", &$tokens.get($index-1), Op::$op, &$tokens.get($index+1));
            let mut exp = UnsafeAst::with_op(Op::$op);
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
                    let mut exp = UnsafeAst::with_op(Op::$op);
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
                let mut exp = UnsafeAst::with_op(Op::$op);
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

///  NOTE:  The main implementation for the unsafe parser
impl<const N: usize> MathParser<UnsafeAst, N> {
    pub fn all_values_and_pointers(&self) {
        for i in 0..self.len() {
            let ptr: *const UnsafeAst = self.equation[i].as_ptr();
            println!("[{}]: {:?}", ptr as usize, self.get(i))
        }
    }

    /// Note: that `Self::equals_pos` will not be set and may need initializing first
    pub fn parse_expression(&mut self, input: &str) {
        let equals_pos = input.find('=').unwrap_or_default();

        if equals_pos > 0 && equals_pos < input.len() - 1 {
            let (left, right) = input.split_at(equals_pos);
            let left_ex = self.parse_expression_side(left);
            let right_ex = self.parse_expression_side(right);
            let mut root = UnsafeAst::default();
            root.set_left_as_nested(&left_ex);
            root.set_right_as_nested(&right_ex);
            self.left_ptr_push(root);
        } else {
            if let Some(Some(op)) = input.chars().next().map(Op::recurs_on_ans) {
                let mut exp = UnsafeAst::with_op(op);
                exp.set_left_as_var(0);
                self.left_ptr_push(exp);
            }
            self.parse_expression_side(input);
        }
    }

    /// If operating on a balanced equation like
    fn parse_expression_side(&mut self, input: &str) -> UnsafeAst {
        let mut tokens: heapless::Vec<Token<usize>, N> = heapless::Vec::new();
        crate::str_parse::string_to_tokens::<usize, N>(&mut tokens, input);
        let end = tokens.len();
        println!("{:?} {}", tokens, end);
        for start in (0..end).rev() {
            if tokens.get(start).map(Token::is_paren_start).unwrap_or_default() {
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
        UnsafeAst::default()
    }

    /// Takes a mutable reference to a token vec with a start and end and attempts to pop elements from it and place them into a
    fn section_to_ast(&mut self, tokens: &mut heapless::Vec<Token<usize>, N>, start: usize, end: usize) {
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
