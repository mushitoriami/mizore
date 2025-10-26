use cosp::Term;
use ruff_python_ast::{Expr, Number, Stmt};
use ruff_python_parser::{parse_expression, parse_module};

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

fn stmt_to_term(stmt: &Stmt) -> Option<Term> {
    match stmt {
        Stmt::Assert(ast) => Some(Term::Compound(
            "Assert".into(),
            vec![expr_to_term(&ast.test)?],
        )),
        _ => None,
    }
}

fn source_expr_to_term(source: &str) -> Option<Term> {
    let parsed = parse_expression(source).ok()?;
    expr_to_term(&parsed.into_expr())
}

fn source_stmt_to_term(source: &str) -> Option<Term> {
    let parsed = parse_module(source).ok()?;
    stmt_to_term(&parsed.into_suite()[0])
}

fn evaluate_term_i64(term: &Term) -> Option<i64> {
    match term {
        Term::Compound(literal, vector) if literal == "Literal" => match vector.as_slice() {
            [Term::Constant(int), Term::Constant(value)] if int == "Int" => {
                Some(value.parse().unwrap())
            }
            _ => None,
        },
        _ => None,
    }
}

fn evaluate_term_bool(term: &Term) -> Option<bool> {
    match term {
        Term::Compound(compare, vector) if compare == "Compare" => match vector.as_slice() {
            [Term::Constant(op), left, right] if op == "==" => {
                let left = evaluate_term_i64(left).unwrap();
                let right = evaluate_term_i64(right).unwrap();
                Some(left == right)
            }
            _ => None,
        },
        _ => None,
    }
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

    #[test]
    fn test_stmt_to_term_1() {
        assert_eq!(
            source_stmt_to_term("assert(2 == 4)\n"),
            Some(Term::Compound(
                "Assert".into(),
                vec![Term::Compound(
                    "Compare".into(),
                    vec![
                        Term::Constant("==".into()),
                        Term::Compound(
                            "Literal".into(),
                            vec![Term::Constant("Int".into()), Term::Constant("2".into())]
                        ),
                        Term::Compound(
                            "Literal".into(),
                            vec![Term::Constant("Int".into()), Term::Constant("4".into())]
                        )
                    ]
                )]
            ))
        )
    }

    #[test]
    fn test_evaluate_term_i64_1() {
        assert_eq!(
            source_expr_to_term("2").map(|x| evaluate_term_i64(&x)),
            Some(Some(2))
        )
    }

    #[test]
    fn test_evaluate_term_bool_1() {
        assert_eq!(
            source_expr_to_term("2 == 2").map(|x| evaluate_term_bool(&x)),
            Some(Some(true))
        )
    }

    #[test]
    fn test_evaluate_term_bool_2() {
        assert_eq!(
            source_expr_to_term("2 == 3").map(|x| evaluate_term_bool(&x)),
            Some(Some(false))
        )
    }
}
