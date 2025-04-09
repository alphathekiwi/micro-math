pub mod parsing;
pub mod calculation;
pub mod graphing;

pub const MAX_EXPRESSION_LEN: usize = 20;
pub const MAX_PARENS: usize = MAX_EXPRESSION_LEN / 4;

#[cfg(test)]
pub(crate) mod tests;