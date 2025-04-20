use crate::equation::MathParser;
use crate::equation::ast_render_tree;
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

impl<'a> Equation for &'a mut SaferAst<'a>
where
    'a: 'static,
{
    fn solve(&self, vars: &[f32]) -> f32 {
        let (left, right, op) = self.get_values();
        crate::calculation::calculate(left.base_solve(vars), right.base_solve(vars), op)
    }

    fn render_tree(&self) -> Vec<String> {
        ast_render_tree(self)
    }
}

impl<'a> SaferAst<'a>
where
    'a: 'static,
{
    fn with_op(op: Op) -> Self {
        Self {
            op,
            ..Default::default()
        }
    }
}

impl<'a> AbstractSnytaxTree for &'a mut SaferAst<'a>
where
    'a: 'static,
{
    type A = &'a mut SaferAst<'a>;

    fn solve(&self, vars: &[f32]) -> f32 {
        let (left, right, op) = self.get_values();
        crate::calculation::calculate(left.solve(vars), right.solve(vars), op)
    }

    fn set_left(&mut self, val: &Token<Self::A>) {
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
                let ptr: *const SaferAst = *left as *const SaferAst;
                let left: &'static SaferAst = unsafe { &*ptr };
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

    fn set_right(&mut self, val: &Token<Self::A>) {
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
            let mut exp_ref: &'static SaferAst = to_static!(exp, SaferAst);
            exp_ref.set_right(&$tokens.remove($index+1));
            exp_ref.set_left(&$tokens.remove($index-1));
            // println!("{:?}", exp);
            // for line in exp.render_tree() {
            //     println!("{}", line);
            // }
            let ptr = $parser.left_ptr_push(exp);
            $tokens[$index-1] = Token::AstPointer(&*unsafe { ptr as *const SaferAst });
            $end -= 2;
        } else $fallthrough
    };
    ($parser:tt, $tokens:tt, $index:tt, $end:tt, $fallthrough:tt, $($op:ident),*) => {
        match $tokens.get($index) {
            $(
                Some(Token::Operation(Op::$op)) => {
                    // println!("Matched a {:?} {:?} {:?}", &$tokens.get($index-1), Op::$op, &$tokens.get($index+1));
                    let exp = SaferAst::with_op(Op::$op);
                    let mut exp_ref: &'static SaferAst = to_static!(exp, SaferAst);

                    exp_ref.set_right(&$tokens.remove($index+1));
                    exp_ref.set_left(&$tokens.remove($index-1));
                    // println!("{:?}", exp);
                    // for line in exp.render_tree() {
                    //     println!("{}", line);
                    // }
                    let ptr = $parser.left_ptr_push(exp);
                    $tokens[$index-1] = Token::AstPointer(&*unsafe { ptr as *const SaferAst });
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
                let exp = SaferAst::with_op(Op::$op);
                let mut exp_ref: &'static SaferAst = to_static!(exp, SaferAst);
                let _ = &$tokens.remove($index+2);
                let mid = $tokens.remove($index+1);

                exp_ref.set_right(&mid);
                // println!("{:?} {:?}", exp, &mid);
                // for line in exp.render_tree() {
                //     println!("{}", line);
                // }
                let ptr = $parser.left_ptr_push(exp);
                $tokens[$index] = Token::AstPointer(&*unsafe { ptr as *const SaferAst });
            }),*
            _ => {},
        }
    }
}

macro_rules! to_static {
    ($value:tt, $var_type:tt) => {
        unsafe { &*{ &$value as *const $var_type } }
    };
}
///  NOTE:  The main implementation for the safer parser
impl<'a, const N: usize> MathParser<SaferAst<'a>, N>
where
    'a: 'static,
{
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
            let root = SaferAst::default();
            self.parse_expression_side(left);
            self.parse_expression_side(right);
            // if let Some(left_ex) = self.get(self.l_len - 1) {
            // }
            // if let Some(right_ex) = self.get(self.r_len + 1) {
            // }
            let left_tk: &'static SaferAst =
                to_static!({ *self.get_unchecked(self.l_len - 1) }, SaferAst);
            let right_tk: &'static SaferAst =
                to_static!({ *self.get_unchecked(self.r_len + 1) }, SaferAst);
            let mut root_ref: &'static SaferAst = to_static!(root, SaferAst);
            root_ref.set_left(&Token::AstPointer(left_tk));
            root_ref.set_right(&Token::AstPointer(right_tk));
            self.left_ptr_push(root);
        } else {
            if let Some(Some(op)) = input.chars().next().map(Op::recurs_on_ans) {
                let exp = SaferAst::with_op(op);
                let mut exp_ref: &'static SaferAst = to_static!(exp, SaferAst);
                exp_ref.set_left(&Token::Variable(0));
                self.left_ptr_push(exp);
            }
            self.parse_expression_side(input);
        }
    }

    /// If operating on a balanced equation like
    fn parse_expression_side(&mut self, input: &str) {
        let mut tokens: heapless::Vec<Token<&'a mut SaferAst>, N> = heapless::Vec::new();
        crate::str_parse::string_to_tokens::<&'a mut SaferAst, N>(&mut tokens, input);
        let end = tokens.len();
        println!("{:?} {}", tokens, end);
        for start in (0..end).rev() {
            if tokens.get(start).map(Token::is_paren_start).unwrap_or_default() {
                let tokens_len = tokens.len();
                for end in start..tokens_len {
                    if let Some(Token::CloseParen(_)) = tokens.get(end) {
                        println!("Found parens at {start} {end}");
                        self.section_to_ast(&mut tokens, start, end);
                        break;
                    }
                }
            }
        }
        let end = tokens.len();
        self.section_to_ast(&mut tokens, 0, end);
    }

    /// Takes a mutable reference to a token vec with a start and end and attempts to pop elements from it and place them into a
    fn section_to_ast(
        &mut self,
        tokens: &mut heapless::Vec<Token<&'a mut SaferAst>, N>,
        start: usize,
        end: usize,
    ) {
        // Exponents evaluate Right to Left
        let mut end = end;
        for index in (start..end).rev() {
            unsafe { tokens_to_ast!(self, tokens, index, end, {}, Sqrt, Exp) }
        }
        // let mut end3 = end2;
        // for index in start..end2 {
        //     tokens_to_ast!(self, tokens, index, end3, Mul, Div, Mod, Fac)
        // }
        let mut index = start;
        while end > start && index < end {
            unsafe { tokens_to_ast!(self, tokens, index, end, { index += 1 }, Mul, Div, Mod, Fac) }
        }
        let mut index = start;
        while end > start && index < end {
            unsafe { tokens_to_ast!(self, tokens, index, end, { index += 1 }, Add, Sub) }
        }
        // for index in start..end3 {
        //     tokens_to_ast!(self, tokens, index, basics_end, Add, Sub)
        // }

        //  NOTE:  Brackets and Sin... are put on last as sections_to_ast will pass
        // sections begining and ending with these values so in reality they are at the first position
        for index in (start..end).rev() {
            unsafe { sctb_to_ast!(self, tokens, index, Sin, ArcSin, Cos, ArcCos, Tan, ArcTan) }
        }
    }
}
