use std::ops::{Add as _, Div as _, Mul as _, Sub as _};

use crate::Op;

pub fn calculate(left: f32, right: f32, operation: Op) -> f32 {
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