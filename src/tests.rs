
// use std::cmp::max;

use crate::unsafe_parse::MathParser;
const TEST_EQ_LEN: usize = 128;

// const VARS: &str = "AXY";
// impl std::fmt::Display for crate::Op {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             crate::Op::Add => write!(f, "+"),
//             crate::Op::Sub => write!(f, "-"),
//             crate::Op::Mul => write!(f, "*"),
//             crate::Op::Div => write!(f, "/"),
//             crate::Op::Mod => write!(f, "%"),
//             crate::Op::Exp => write!(f, "^"),
//             crate::Op::Sqrt => write!(f, "√"),
//             crate::Op::Fac => write!(f, "!"),
//             crate::Op::Sin => write!(f, "sin"),
//             crate::Op::ArcSin => write!(f, "asin"),
//             crate::Op::Cos => write!(f, "cos"),
//             crate::Op::ArcCos => write!(f, "acos"),
//             crate::Op::Tan => write!(f, "tan"),
//             crate::Op::ArcTan => write!(f, "atan"),
//             crate::Op::NotOp => write!(f, "?"),
//         }
//     }
// }
// impl MicroEqValue<'_> {
//     pub fn render_tree(&self) -> Vec<String> {
//         let mut display: Vec<String> = Vec::new();
//         match self {
//             MicroEqValue::Float(n) => display.push(format!("{n}")),
//             MicroEqValue::Var(v) => display.push(VARS.chars().nth(*v as usize).map(|c| c.to_string()).unwrap_or_else(||{format!("{}", v)}).to_string()),
//             MicroEqValue::Nested(micro_equation) => {
//                 let lines = micro_equation.render_tree();
//                 for (i, line) in lines.iter().enumerate() {
//                     let prefix: String = if i > 1 { (0..(i / 2)).map(|_|{"  "}).collect() } else { "".into() };
//                     display.push(format!("{prefix}{}", line));
//                 }
//             },
//             MicroEqValue::Unitialized => {},
//         }
//         display
//     }
// }
// impl 
// MicroEquation {
//     #[allow(unused)]
//     pub fn render_tree(&self) -> Vec<String> {
//         let mut display: Vec<String> = Vec::new();
//         let (left, right, op) = self.get_values();
//         let left = left.render_tree();
//         let right = right.render_tree();
//         let height = max(left.len(), right.len());
//         let (ol, or) = (height-left.len(), height-right.len());
//         for i in 0..height {
//             match (i>=ol, i>=or) {
//                 (true, false) => {
//                     let val = format!("{:?}  ", left);
//                     let (pf, sf) = suffix_postfix(val.len()-3);
//                     display.push(val);
//                     display.push(format!("{pf}\\{op} {sf}"));
//                 },
//                 (false, true) => {
//                     let val = format!("  {:?}", right);
//                     let (pf, sf) = suffix_postfix(val.len()-3);
//                     display.push(val);
//                     display.push(format!("{pf} {op}/{sf}"));
//                 },
//                 _ => {
//                     let val = format!("{:?} {:?}", left, right);
//                     let (pf, sf) = suffix_postfix(val.len()-3);
//                     display.push(val);
//                     display.push(format!("{pf}\\{op}/{sf}"));
//                 },
//             }
//             // let (wl, wr) = (left.get(i), right.get(i));
//             display.push(format!("{:?} {:?}", left, right));
//         }
//         display
//     }
// }
// impl<const N: usize> MathParser<N> {
//     pub fn render_tree(&self) -> Vec<String> {
//         self.last().map(|r|{
//             println!("Attempting to render tree {}", self.len());
//             println!("{:?}", self.as_slice());
//             r.render_tree()
//         }).unwrap_or_else(||{
//             println!("No final item found {}", self.len());
//             println!("{:?}", self.as_slice());
//             Vec::new()
//         })
//     }
// }
// fn suffix_postfix(len: usize) -> (String, String) {
//     if len == 0 { 
//         ("".into(), "".into()) 
//     } else {
//         (0..(len / 2)).map(|_|{(" ", " ")}).collect()
//     }
// }

#[allow(unused)]
fn test_graphing(input: &str) {
    let parser: MathParser<TEST_EQ_LEN> = MathParser::new(input);
    for line in parser.render_tree() {
        println!("{}", line);
    }
    // let (eq_pos, focus) = (parser.equals_pos, parser.focus_of_eq);
    // println!("\n{:?}", parser.expressions);
    // println!("{:?} {:?}", parser.focus_of_eq, parser.equals_pos);
    // if parser.is_balanced_equation() || parser.try_balance_equation() {
    //     // let ans = parser.calculate_points(1.0, -63..=64);
    //     // println!("{:?}", [ans]);
    // } else {
    //     assert!(parser.is_balanced_equation(), "Equation can not be balanced {eq_pos}, {:?}", focus);
    // }
    // assert_eq!(ans, Some(expected), "Comparing {input} => {:?} != {expected}\n{:?}", ans, parser.expressions);
}

#[test]
fn valid_equation() {
    let eq_index = "=0+9-10".find('=').filter(|i| { *i < "=0+9-10".len()-1 }).unwrap_or_default();
    assert_eq!(eq_index, 0, "Equals at the start is greater than zero");
    let eq_index = "0+9-10=".find('=').filter(|i| { *i < "0+9-10=".len()-1 }).unwrap_or_default();
    assert_eq!(eq_index, 0, "Equals at the end is greater than zero");
}

#[test]
fn split_equation() {
    let parts: Vec<&str> = "=0+9-10".split_inclusive(|c| "+-=*/^\\%!".contains(c)).collect();
    assert_eq!(parts.len(), 4, "Wrong lenght for {:?}", parts);
}
#[test]
fn balanced_equation() {
    test_graphing("X=y*y");
}

#[test]
fn unbalanced_equation() {
    test_graphing("x*5=y*y");
}

#[allow(unused)]
fn test_calculation(input: &str, expected: f32, n: f32) {
    let parser: MathParser<TEST_EQ_LEN> = MathParser::new(input);
    for line in parser.render_tree() {
        println!("{}", line);
    }
    // println!("{:?}", parser.expressions);
    // let ans = parser.calculate_result_inplace(n);
    // assert_eq!(ans, expected, "Comparing {input} => {ans} != {expected}\n{:?}", parser.expressions);
}

#[test]
fn with_prev_ans() {
    test_calculation("+5", 6.0, 1.0);
    test_calculation("*7", 14.0, 2.0);
}

#[test]
fn advanced_sine() {
    test_calculation("s(3-4)*27.02+cos(0.8)", 18.551777, 0.0);
}
#[test]
fn advanced_order_of_operations() {
    test_calculation("12/(2+3)", 2.4, 0.0);
    test_calculation("((3*(1.5+6.5))/3)^2", 64.0, 0.0);
}

#[test]
fn simple_circle_area() {
    test_calculation("p*3^2", 28.274334, 0.0);
    // Although both of the following look the similar they should give different answers due to order of operations
    test_calculation("p2^2", 12.566371, 0.0); //  p*(2^2)
    test_calculation("2p^2", 19.73921, 0.0);  //  (2*p)^2
}
#[test]
fn simple_addition() {
    test_calculation("3+5+8", 16.0, 0.0);
}
#[test]
fn simple_subtraction() {
    test_calculation("81-7-18", 56.0, 0.0);
}
#[test]
fn simple_multiplication() {
    test_calculation("3*5*3", 45.0, 0.0);
}
#[test]
fn simple_division() {
    test_calculation("96/2/12", 4.0, 0.0);
}
#[test]
fn simple_exponents() {
    test_calculation("2^2^2", 16.0, 0.0);
}
#[test]
fn simple_modulo() {
    test_calculation("83%10", 3.0, 0.0);
}
#[test]
fn simple_square() {
    test_calculation("\\\\81", 3.0, 0.0);
}