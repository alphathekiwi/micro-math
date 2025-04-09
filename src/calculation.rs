use std::cmp::min;
use std::ops::{Add as _, Div as _, Mul as _, Sub as _};

use crate::{MAX_EXPRESSION_LEN, MAX_PARENS};
use crate::parsing::{Calc, MathParser, Token};


impl MathParser {
    /// If expression can't be solved example `2+=` then don't attempt to solve it 
    pub fn has_solve(&self) -> bool {
        match self.expressions.last() {
            Some(Calc::Expr(Token::VarX | Token::VarY | Token::Variable | Token::Pi)) => true,
            Some(Calc::Expr(_)) => false,
            _ => true,
        }
    }

    /// Clones all elements first and only mutates self to save the result of the calculation
    pub fn calculate_result_copy(&self, n: f32) -> heapless::Vec<Calc, MAX_EXPRESSION_LEN> {
        let mut expressions = heapless::Vec::<Calc, MAX_EXPRESSION_LEN>::new();
        let _ = expressions.extend_from_slice(self.expressions.as_slice());
        let _res = preform_calc_on_expressions(&self.parens, &mut expressions, n);
        expressions
    }

    /// Mutates the expressions array during calulation and therefore is unsuitable for logging after the fact
    pub fn calculate_result_inplace(&mut self, n: f32) -> f32 {
        match self.cached_ans {
            Some(ans) => ans,
            None => {
                let res = preform_calc_on_expressions(&self.parens, &mut self.expressions, n);
                if let Some(Calc::Num(n)) = res.first() { 
                    self.cached_ans = Some(*n);
                }
                self.cached_ans.unwrap_or_default()
            },
        }
    }

    /// Takes a buffer and writes the answer to it as UTF-8 then returns a str
    pub fn answer_as_str<'a>(&mut self, n: f32, buffer: &'a mut heapless::Vec<u8, 128>) -> &'a str {
        let ans = self.calculate_result_inplace(n);
        core::fmt::write(buffer, format_args!("{:.2}", ans)).unwrap();
        core::str::from_utf8(buffer).unwrap()
    }
}


fn preform_calc_on_expressions<'a>(parens: &heapless::Vec<(usize, usize), MAX_PARENS>, expressions: &'a mut heapless::Vec<Calc, MAX_EXPRESSION_LEN>, n: f32) -> &'a mut heapless::Vec<Calc, MAX_EXPRESSION_LEN> {
    for (s, e) in parens.iter().rev() {
        let (_, mid, _) = extract_middle_of_parens(expressions, s, e);
        let res = calculate_range(mid, n);
        for r in (*s..*e).rev() {
            let i = r - s;
            match res.get(i) {
                Some(v) => { expressions[r] = *v },
                None => if r < expressions.len() { expressions.remove(r); },
            }
        }
    }
    {
        let res = calculate_range(expressions, n);
        let len = expressions.len();
        for r in (0..len).rev() {
            match res.get(r) {
                Some(v) => { expressions[r] = *v },
                None => if r < expressions.len() { expressions.remove(r); },
            }
        }
    }
    expressions
}

fn extract_middle_of_parens<'a>(expressions: &'a mut heapless::Vec<Calc, 20>, s: &usize, e: &usize) -> (&'a [Calc], &'a [Calc], &'a [Calc]) {
    let (left_of_paren, m) = expressions.split_at(*s);
    let (mid_of_paren, right_of_paren) = m.split_at(min(*e-*s, m.len()));
    (left_of_paren, mid_of_paren, right_of_paren)
}

fn calculate_range(range: &[Calc], n: f32) -> heapless::Vec<Calc, MAX_EXPRESSION_LEN> {
    let mut calcs: heapless::Vec<Calc, MAX_EXPRESSION_LEN> = heapless::Vec::from_slice(range).unwrap();
    let mut index = calcs.len();
    loop {
        match calcs.get(index) { 
            Some(Calc::Expr(Token::Variable)) if index != 0 => calcs[index] = Calc::Num(n),
            Some(Calc::Expr(Token::Sin))    => preform_soh_cah_toh(&mut calcs, index, |b| { b.sin() }, n),
            Some(Calc::Expr(Token::ArcSin)) => preform_soh_cah_toh(&mut calcs, index, |b| { b.asin() }, n),
            Some(Calc::Expr(Token::Cos))    => preform_soh_cah_toh(&mut calcs, index, |b| { b.cos() }, n),
            Some(Calc::Expr(Token::ArcCos)) => preform_soh_cah_toh(&mut calcs, index, |b| { b.acos() }, n),
            Some(Calc::Expr(Token::Tan))    => preform_soh_cah_toh(&mut calcs, index, |b| { b.tan() }, n),
            Some(Calc::Expr(Token::ArcTan)) => preform_soh_cah_toh(&mut calcs, index, |b| { b.atan() }, n),
            Some(Calc::Expr(Token::Sqrt))   => preform_soh_cah_toh(&mut calcs, index, |b| { b.sqrt() }, n),
            _ => {}
        }
        if index == 0 { break; } else { index -= 1; }
    }
    let mut index = calcs.len();
    loop { // Exponents evaluate Right to Left
        if matches!(calcs.get(index), Some(Calc::Expr(Token::Exp))) { 
            preform_maths(&mut calcs, index, |a, b| { a.powf(b) }, n)
        }
        if index == 0 { break; } else { index -= 1; }
    }
    let mut index = 0;
    loop {
        if index == calcs.len() { break; }
        match calcs.get(index) { 
            Some(Calc::Expr(Token::Mul)) => preform_maths(&mut calcs, index, |a, b| { a.mul(b) }, n),
            Some(Calc::Expr(Token::Div)) => preform_maths(&mut calcs, index, |a, b| { a.div(b) }, n),
            Some(Calc::Expr(Token::Mod)) => preform_maths(&mut calcs, index, |a, b| { a % b }, n),
            _ => { index += 1; }
        }
    }
    let mut index = 0;
    loop {
        if index == calcs.len() { break; }
        match calcs.get(index) { 
            Some(Calc::Expr(Token::Add)) => preform_maths(&mut calcs, index, |a, b| { a.add(b) }, n),
            Some(Calc::Expr(Token::Sub)) => preform_maths(&mut calcs, index, |a, b| { a.sub(b) }, n),
            _ => { index += 1; }
        }
    }
    calcs
}

/// Places the result inplace of Operator and removes value of B that was consumed
fn preform_soh_cah_toh<F>(calcs: &mut heapless::Vec<Calc, 20>, index: usize, math: F, n: f32) where F: FnOnce(f32) -> f32 {
    if index+1 >= calcs.len() { return }
    if let Some(Calc::Num(b)) = calcs.get(index+1).map(|v| var_to_num(*v, n)) {
        calcs[index] = Calc::Num(math(b));
        calcs.remove(index + 1);
    }
}

/// Places the result inplace of A and removes Operator and B that were consumed
fn preform_maths<F>(calcs: &mut heapless::Vec<Calc, 20>, index: usize, math: F, n: f32) where F: FnOnce(f32, f32) -> f32 {
    if index == 0 || index+1 >= calcs.len() { return }
    if let (Some(Calc::Num(a)), Some(Calc::Num(b))) = (calcs.get(index-1).map(|v| var_to_num(*v, n)), calcs.get(index+1).map(|v| var_to_num(*v, n))) {
        calcs[index-1] = Calc::Num(math(a, b));
        calcs.remove(index+1);
        calcs.remove(index);
    }
}

fn var_to_num (v: Calc, n: f32) -> Calc {
    if v == Calc::Expr(Token::Variable) {Calc::Num(n)} else {v}
}
