use crate::parsing::MathParser;


fn test_graphing(input: &str) {
    let parser = MathParser::new(input);
    let (eq_pos, focus) = (parser.equals_pos, parser.focus_of_eq);
    println!("\n{:?}", parser.expressions);
    println!("{:?} {:?}", parser.focus_of_eq, parser.equals_pos);
    if parser.is_balanced_equation() || parser.try_balance_equation() {
        // let ans = parser.calculate_points(1.0, -63..=64);
        // println!("{:?}", [ans]);
    } else {
        assert!(parser.is_balanced_equation(), "Equation can not be balanced {eq_pos}, {:?}", focus);
    }
    // assert_eq!(ans, Some(expected), "Comparing {input} => {:?} != {expected}\n{:?}", ans, parser.expressions);
}

#[test]
fn balanced_equation() {
    test_graphing("X=y*y");
}

#[test]
fn unbalanced_equation() {
    test_graphing("x*5=y*y");
}


fn test_calculation(input: &str, expected: f32, n: f32) {
    let mut parser = MathParser::new(input);
    // println!("{:?}", parser.expressions);
    let ans = parser.calculate_result_inplace(n);
    assert_eq!(ans, expected, "Comparing {input} => {ans} != {expected}\n{:?}", parser.expressions);
}

#[test]
fn with_prev_ans() {
    test_calculation("+5", 6.0, 1.0);
    test_calculation("*7", 14.0, 2.0);
}

#[test]
fn advanced_sine() {
    test_calculation("s(3+4)*27.02+0.8", 18.551777, 0.0);
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
