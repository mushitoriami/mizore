use cosp::{Rule, Term};
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

fn assert_to_rule(assert: &Stmt) -> Option<Rule> {
    match assert {
        Stmt::Assert(ast) => Some(Rule::Rule(2, expr_to_term(&ast.test)?, Vec::new())),
        Stmt::If(ast) => match ast.body.as_slice() {
            [Stmt::Assert(ast_assert)] => Some(Rule::Rule(
                2,
                expr_to_term(&ast_assert.test)?,
                vec![expr_to_term(&ast.test)?],
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

fn source_assert_to_rule(source: &str) -> Option<Rule> {
    let parsed = parse_module(source).ok()?;
    assert_to_rule(&parsed.into_suite()[0])
}

fn evaluate_term_i64(term: &Term) -> Option<i64> {
    match term {
        Term::Compound(label, args) if label == "Literal" => match args.as_slice() {
            [Term::Constant(label), Term::Constant(value)] if label == "Int" => {
                Some(value.parse().unwrap())
            }
            _ => None,
        },
        _ => None,
    }
}

fn evaluate_term_bool(term: &Term) -> Option<bool> {
    match term {
        Term::Compound(label, args) if label == "Compare" => match args.as_slice() {
            [Term::Constant(label), left, right] if label == "==" => {
                Some(evaluate_term_i64(left).unwrap() == evaluate_term_i64(right).unwrap())
            }
            _ => None,
        },
        _ => None,
    }
}

fn check_assert(_facts: &[Rule], assert: &Rule) -> bool {
    match assert {
        Rule::Rule(_, head, body) if body.is_empty() => evaluate_term_bool(head).unwrap(),
        _ => false,
    }
}

fn update_facts(facts: &mut Vec<Rule>, assert: Rule) {
    facts.push(assert)
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
    fn test_assert_to_rule_1() {
        assert_eq!(
            source_assert_to_rule("assert(2 == 4)\n"),
            Some(Rule::Rule(
                2,
                Term::Compound(
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
                ),
                Vec::new()
            ))
        )
    }

    #[test]
    fn test_assert_to_rule_2() {
        assert_eq!(
            source_assert_to_rule("if 2 == 3:\n    assert(2 == 4)\n"),
            Some(Rule::Rule(
                2,
                Term::Compound(
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
                ),
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
                            vec![Term::Constant("Int".into()), Term::Constant("3".into())]
                        )
                    ]
                ),]
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

    #[test]
    fn test_check_assert_1() {
        assert_eq!(
            check_assert(
                &[],
                &Rule::Rule(2, source_expr_to_term("2 == 2").unwrap(), Vec::new())
            ),
            true
        )
    }

    #[test]
    fn test_check_assert_2() {
        assert_eq!(
            check_assert(
                &[],
                &Rule::Rule(2, source_expr_to_term("2 == 3").unwrap(), Vec::new())
            ),
            false
        )
    }

    #[test]
    fn test_update_facts_1() {
        let mut facts = Vec::new();
        update_facts(&mut facts, source_assert_to_rule("assert(2 == 3)").unwrap());
        assert_eq!(
            facts,
            vec![source_assert_to_rule("assert(2 == 3)").unwrap()]
        );
        update_facts(&mut facts, source_assert_to_rule("assert(2 == 2)").unwrap());
        assert_eq!(
            facts,
            vec![
                source_assert_to_rule("assert(2 == 3)").unwrap(),
                source_assert_to_rule("assert(2 == 2)").unwrap(),
            ]
        );
    }
}
