use cosp::Term;
use ruff_python_ast::{Expr, Number};
use ruff_python_parser::parse_expression;

fn expr_to_term(expr: &Expr) -> Option<Term> {
    match expr {
        Expr::Compare(ast) => {
            if ast.ops.len() == 1 && ast.comparators.len() == 1 {
                let left_term = expr_to_term(&ast.left)?;
                let right_term = expr_to_term(&ast.comparators[0])?;
                let op_term = Term::Constant(ast.ops[0].to_string());
                Some(Term::Compound(
                    "Compare".into(),
                    vec![op_term, left_term, right_term],
                ))
            } else {
                None
            }
        }
        Expr::NumberLiteral(ast) => match &ast.value {
            Number::Int(value) => Some(Term::Compound(
                "Literal".into(),
                vec![
                    Term::Constant("Int".into()),
                    Term::Constant(value.to_string()),
                ],
            )),
            _ => None,
        },
        _ => None,
    }
}

fn source_expr_to_term(source: &str) -> Option<Term> {
    let parsed = parse_expression(source).ok()?;
    expr_to_term(&parsed.into_expr())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_to_term_1() {
        assert_eq!(
            source_expr_to_term("2 == 3"),
            Some(Term::Compound(
                "Compare".into(),
                vec![
                    Term::Constant("==".into()),
                    Term::Compound(
                        "Literal".into(),
                        vec![Term::Constant("Int".into()), Term::Constant("2".into())]
                    ),
                    Term::Compound(
                        "Literal".into(),
                        vec![Term::Constant("Int".into()), Term::Constant("3".into())]
                    )
                ]
            ))
        )
    }
}
