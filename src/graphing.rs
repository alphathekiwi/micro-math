use crate::{parsing::{Calc, MathParser, Token}, MAX_EXPRESSION_LEN};


#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Axis { GraphX, GraphY, NoFocus }
impl Axis {
    pub fn matches_calc(&self, token: &Calc) -> bool {
        matches!((self, token), (Axis::GraphX, Calc::Expr(Token::VarX))|(Axis::GraphY, Calc::Expr(Token::VarY)))
    }
}

impl MathParser {
    ///  NOTE:  Math Parser does not yet implemented equation balancing
    /// currently equations can only be solved if they have a single variable on one side
    pub fn is_balanced_equation(&self) -> bool {
        self.equals_pos == 1 && self.focus_of_eq != Axis::NoFocus && self.has_solve()
    }

    pub fn calculate_points(&self, scale: f32, range: core::ops::RangeInclusive<i32>) -> heapless::Vec<(i32, i32), 128> {
        let mut res: heapless::Vec<(i32, i32), 128> = heapless::Vec::new();
        for i in range.clone() {
            let focus = (i as f32) * scale;
            let ans = self.calculate_result_copy(focus);
            let (x, y) = self.get_x_y(ans, focus);
            if range.contains(&x) && range.contains(&y) {
                let _ = res.push( (64 + x, 96 - y));
            }
        }
        res
    }

    pub fn try_balance_equation(&self) -> bool {
        let mut res: heapless::Vec<Calc, MAX_EXPRESSION_LEN> = heapless::Vec::new();
        let (left, right) = self.expressions.split_at(self.equals_pos);
        if left.len() > right.len() {
            let _ = res.extend_from_slice(right);
            shift_to_other(&self.focus_of_eq, left, &mut res);

        } else {
            let _ = res.extend_from_slice(left);
            shift_to_other(&self.focus_of_eq, right, &mut res);

        }
        false
    }

    fn get_x_y(&self, ans: heapless::Vec<Calc, 20>, focus: f32) -> (i32, i32) {
        if ans.len() == 3 {
            if let Some(Calc::Num(other)) = ans.get(2) {
                match self.focus_of_eq {
                    Axis::GraphX => return (*other as i32, focus as i32),
                    Axis::GraphY => return (focus as i32, *other as i32),
                    Axis::NoFocus => {},
                }
            }
        }
        (0, 0)
    }
}

fn shift_to_other(focus: &Axis, other: &[Calc], main: &mut heapless::Vec<Calc, 20>) {
    let mut remaining: heapless::Vec<Calc, MAX_EXPRESSION_LEN> = heapless::Vec::new();
    let mut skip = 0;
    for (i, o) in other.iter().enumerate() {
        if skip > 0 { continue; }
        if !focus.matches_calc(o) {
            let inv = o.invert();
            if let Some(c) = inv {
                let _ = main.push(c);
            } else {
                let _ = remaining.push(*o);
            }
        } else if let Some(s) = other.get(i+2) {
            if !focus.matches_calc(s) { skip += 2; }
        }
    }
    let _ = main.extend_from_slice(&remaining);
}