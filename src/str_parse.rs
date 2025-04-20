use crate::{Op, Token};

pub fn string_to_tokens<T: Copy, const N: usize>(
    expressions: &mut heapless::Vec<Token<T>, N>,
    input: &str,
) {
    let chars = input.chars();
    if let Some(b) = input.chars().next() {
        if Token::<T>::from(b).is_doublesided_op() {
            // If equation begins with an operation push a previous answer variable in front of it
            expressions.push(Token::Variable(0)).ok();
        }
    }
    let mut current = 0;
    for (i, b) in chars.into_iter().enumerate() {
        if current > i {
            continue;
        }
        let token: Token<T> = Token::from(b);
        if token.is_narrow() {
            if matches!(&token, Token::Operation(Op::Sqrt)) {
                previous_is_multiplier::<T, N>(expressions);
            }
            expressions.push(token).ok();
            continue;
        }
        match &token {
            Token::Number(_) => {
                if let Some(remaining) = input.get(i..) {
                    current = i;
                    for c in remaining.chars() {
                        match c {
                            '0'..='9'|'.' => current += 1,
                            _ => break,
                        }
                    }
                }
                if let Ok(n) = input[i..current].parse::<f32>() {
                    push_maybe_negative::<T, N>(expressions, n);
                }
            }
            Token::Operation(Op::Sin | Op::Cos | Op::Tan) => {
                previous_is_multiplier::<T, N>(expressions);
                match (token, input.get(1 + i..i + 4)) {
                    (Token::Operation(Op::Sin), Some("in("))
                    | (Token::Operation(Op::Cos), Some("os("))
                    | (Token::Operation(Op::Tan), Some("an(")) => {
                        expressions.push(token).ok();
                        current = i + 4;
                        continue;
                    }
                    (_, Some(s)) if s.starts_with('(') => {
                        expressions.push(token).ok();
                        current = i + 2;
                        continue;
                    }
                    _ => {
                        expressions.push(Token::Variable(b as u32)).ok();
                    }
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
                    previous_is_multiplier::<T, N>(expressions);
                    expressions.push(t).ok();
                    current = i + 5;
                }
            }
            Token::Pi => {
                previous_is_multiplier::<T, N>(expressions);
                push_maybe_negative::<T, N>(expressions, core::f32::consts::PI);
                if matches!(input.chars().nth(i + 1), Some('0'..='9' | '.')) {
                    expressions.push(Token::Operation(Op::Mul)).ok();
                }
            }
            Token::Variable(_) => {
                previous_is_multiplier::<T, N>(expressions);
                expressions.push(token).ok();
            }
            Token::OpenParen(_) => {
                previous_is_multiplier::<T, N>(expressions);
                expressions.push(token).ok();
            }
            Token::CloseParen(_) => {
                expressions.push(token).ok();
            }
            _ => {}
        }
    }
}

fn previous_is_multiplier<T, const N: usize>(expressions: &mut heapless::Vec<Token<T>, N>) {
    // let recent = ;
    match expressions.last() {
        Some(Token::Number(_) | Token::Pi | Token::Variable(_)) => {
            expressions.push(Token::Operation(Op::Mul)).ok()
        }
        _ => None,
    };
}

fn push_maybe_negative<T, const N: usize>(expressions: &mut heapless::Vec<Token<T>, N>, n: f32) {
    match expressions.last() {
        Some(&Token::Operation(Op::Sub)) => {
            let _ = expressions.pop();
            if let Some(&Token::Number(_)) = expressions.last() {
                let _ = expressions.push(Token::Operation(Op::Add));
            }
            let _ = expressions.push(Token::Number(-n));
        }
        _ => {
            let _ = expressions.push(Token::Number(n));
        }
    }
}
