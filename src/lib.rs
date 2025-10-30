use cosp::{Rule, Term, infer};
use ruff_python_ast::{Expr, Number, Stmt};
use ruff_python_parser::{parse_expression, parse_module};
use ruff_text_size::{Ranged, TextRange, TextSize};

fn source_to_expr(source: &str) -> Option<Expr> {
    let parsed = parse_expression(source).unwrap();
    Some(parsed.into_expr())
}

fn source_to_stmt(source: &str) -> Option<Stmt> {
    let parsed = parse_module(source).unwrap();
    parsed.into_suite().pop()
}

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
        Expr::BinOp(ast) => {
            let left_term = expr_to_term(&ast.left)?;
            let right_term = expr_to_term(&ast.right)?;
            let op_term = Term::Constant(ast.op.to_string());
            Some(Term::Compound(
                "BinOp".into(),
                vec![op_term, left_term, right_term],
            ))
        }
        Expr::BoolOp(ast) => {
            if ast.values.len() == 2 {
                let left_term = expr_to_term(&ast.values[0])?;
                let right_term = expr_to_term(&ast.values[1])?;
                let op_term = Term::Constant(ast.op.to_string());
                Some(Term::Compound(
                    "BoolOp".into(),
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
        Expr::Name(ast) => Some(Term::Compound(
            "Variable".into(),
            vec![Term::Constant(ast.id.to_string())],
        )),
        _ => None,
    }
}

fn assert_to_term(assert: &Stmt) -> Option<Term> {
    match assert {
        Stmt::Assert(ast) => expr_to_term(&ast.test),
        Stmt::If(ast) => match ast.body.as_slice() {
            [Stmt::Assert(ast_assert)] => Some(Term::Compound(
                "Arrow".into(),
                vec![expr_to_term(&ast.test)?, expr_to_term(&ast_assert.test)?],
            )),
            _ => None,
        },
        Stmt::For(ast) => {
            let Expr::Call(ref ast_call) = *ast.iter else {
                return None;
            };
            let Expr::Name(ref ast_range) = *ast_call.func else {
                return None;
            };
            let [Stmt::Assert(ast_assert)] = ast.body.as_slice() else {
                return None;
            };
            if ast_range.id.to_string() != "range" {
                return None;
            }
            Some(Term::Compound(
                "Arrow".into(),
                vec![
                    Term::Compound(
                        "BoolOp".into(),
                        vec![
                            Term::Constant("and".into()),
                            Term::Compound(
                                "Compare".into(),
                                vec![
                                    Term::Constant("<=".into()),
                                    expr_to_term(&ast_call.arguments.args[0])?,
                                    expr_to_term(&ast.target)?,
                                ],
                            ),
                            Term::Compound(
                                "Compare".into(),
                                vec![
                                    Term::Constant("<".into()),
                                    expr_to_term(&ast.target)?,
                                    expr_to_term(&ast_call.arguments.args[1])?,
                                ],
                            ),
                        ],
                    ),
                    expr_to_term(&ast_assert.test)?,
                ],
            ))
        }
        _ => None,
    }
}

fn evaluate_term_i64(term: &Term) -> Option<i64> {
    match term {
        Term::Compound(label, args) if label == "Literal" => match args.as_slice() {
            [Term::Constant(label), Term::Constant(value)] if label == "Int" => {
                Some(value.parse().unwrap())
            }
            _ => None,
        },
        Term::Compound(label, args) if label == "BinOp" => match args.as_slice() {
            [Term::Constant(label), left, right] => match label.as_str() {
                "+" => Some(evaluate_term_i64(left)? + evaluate_term_i64(right)?),
                "-" => Some(evaluate_term_i64(left)? - evaluate_term_i64(right)?),
                "*" => Some(evaluate_term_i64(left)? * evaluate_term_i64(right)?),
                "/" => Some(evaluate_term_i64(left)? / evaluate_term_i64(right)?),
                "%" => Some(evaluate_term_i64(left)? % evaluate_term_i64(right)?),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn evaluate_term_bool(term: &Term) -> Option<bool> {
    match term {
        Term::Compound(label, args) if label == "Compare" => match args.as_slice() {
            [Term::Constant(label), left, right] => match label.as_str() {
                "==" => Some(evaluate_term_i64(left)? == evaluate_term_i64(right)?),
                ">" => Some(evaluate_term_i64(left)? > evaluate_term_i64(right)?),
                "<" => Some(evaluate_term_i64(left)? < evaluate_term_i64(right)?),
                ">=" => Some(evaluate_term_i64(left)? >= evaluate_term_i64(right)?),
                "<=" => Some(evaluate_term_i64(left)? <= evaluate_term_i64(right)?),
                _ => None,
            },
            _ => None,
        },
        Term::Compound(label, args) if label == "BoolOp" => match args.as_slice() {
            [Term::Constant(label), left, right] => match label.as_str() {
                "and" => Some(evaluate_term_bool(left)? && evaluate_term_bool(right)?),
                "or" => Some(evaluate_term_bool(left)? || evaluate_term_bool(right)?),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn infer_term(term: Term, facts: &[Rule], depth: u64) -> bool {
    infer(&[term], facts)
        .filter(|&(c, _)| c < depth * 2 + 1)
        .is_some()
}

fn verify_assert(facts: &[Rule], stmt: &Stmt, depth: u64) -> bool {
    match assert_to_term(stmt) {
        Some(head) => evaluate_term_bool(&head).unwrap_or_else(|| infer_term(head, facts, depth)),
        _ => true,
    }
}

fn update_facts(facts: &mut Vec<Rule>, stmt: &Stmt) {
    if let Some(term) = assert_to_term(stmt) {
        facts.push(Rule::Rule(2, term, Vec::new()))
    } else if let Stmt::Assign(ast) = stmt {
        facts.push(Rule::Rule(
            2,
            Term::Compound(
                "Compare".into(),
                vec![
                    Term::Constant("==".into()),
                    expr_to_term(&ast.targets[0]).unwrap(),
                    expr_to_term(&ast.value).unwrap(),
                ],
            ),
            Vec::new(),
        ))
    }
}

fn verify_function(function: &Stmt, depth: u64) -> Vec<TextRange> {
    let Stmt::FunctionDef(ast) = function else {
        panic!()
    };
    let mut errs: Vec<TextRange> = Vec::new();
    let mut facts = vec![
        Rule::Rule(
            2,
            Term::Variable("y".into()),
            vec![
                Term::Compound(
                    "Arrow".into(),
                    vec![Term::Variable("x".into()), Term::Variable("y".into())],
                ),
                Term::Variable("x".into()),
            ],
        ),
        Rule::Rule(11, Term::Variable("x".into()), vec![]),
    ];
    for stmt in &ast.body {
        if !verify_assert(&facts, &stmt, depth) {
            errs.push(stmt.range());
        }
        update_facts(&mut facts, &stmt);
    }
    errs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_to_term_1() {
        assert_eq!(
            expr_to_term(&source_to_expr("2 == 3").unwrap()),
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
    fn test_expr_to_term_2() {
        assert_eq!(
            expr_to_term(&source_to_expr("x == 3").unwrap()),
            Some(Term::Compound(
                "Compare".into(),
                vec![
                    Term::Constant("==".into()),
                    Term::Compound("Variable".into(), vec![Term::Constant("x".into())]),
                    Term::Compound(
                        "Literal".into(),
                        vec![Term::Constant("Int".into()), Term::Constant("3".into())]
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_expr_to_term_3() {
        assert_eq!(
            expr_to_term(&source_to_expr("x <= 3").unwrap()),
            Some(Term::Compound(
                "Compare".into(),
                vec![
                    Term::Constant("<=".into()),
                    Term::Compound("Variable".into(), vec![Term::Constant("x".into())]),
                    Term::Compound(
                        "Literal".into(),
                        vec![Term::Constant("Int".into()), Term::Constant("3".into())]
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_expr_to_term_4() {
        assert_eq!(
            expr_to_term(&source_to_expr("x > 3").unwrap()),
            Some(Term::Compound(
                "Compare".into(),
                vec![
                    Term::Constant(">".into()),
                    Term::Compound("Variable".into(), vec![Term::Constant("x".into())]),
                    Term::Compound(
                        "Literal".into(),
                        vec![Term::Constant("Int".into()), Term::Constant("3".into())]
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_expr_to_term_5() {
        assert_eq!(
            expr_to_term(&source_to_expr("x + 3").unwrap()),
            Some(Term::Compound(
                "BinOp".into(),
                vec![
                    Term::Constant("+".into()),
                    Term::Compound("Variable".into(), vec![Term::Constant("x".into())]),
                    Term::Compound(
                        "Literal".into(),
                        vec![Term::Constant("Int".into()), Term::Constant("3".into())]
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_expr_to_term_6() {
        assert_eq!(
            expr_to_term(&source_to_expr("x % 3 < 5").unwrap()),
            Some(Term::Compound(
                "Compare".into(),
                vec![
                    Term::Constant("<".into()),
                    Term::Compound(
                        "BinOp".into(),
                        vec![
                            Term::Constant("%".into()),
                            Term::Compound("Variable".into(), vec![Term::Constant("x".into())]),
                            Term::Compound(
                                "Literal".into(),
                                vec![Term::Constant("Int".into()), Term::Constant("3".into())]
                            )
                        ]
                    ),
                    Term::Compound(
                        "Literal".into(),
                        vec![Term::Constant("Int".into()), Term::Constant("5".into())]
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_expr_to_term_7() {
        assert_eq!(
            expr_to_term(&source_to_expr("x and y").unwrap()),
            Some(Term::Compound(
                "BoolOp".into(),
                vec![
                    Term::Constant("and".into()),
                    Term::Compound("Variable".into(), vec![Term::Constant("x".into())]),
                    Term::Compound("Variable".into(), vec![Term::Constant("y".into())]),
                ]
            ))
        )
    }

    #[test]
    fn test_assert_to_term_1() {
        assert_eq!(
            assert_to_term(&source_to_stmt("assert(2 == 4)\n").unwrap()),
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
                        vec![Term::Constant("Int".into()), Term::Constant("4".into())]
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_assert_to_term_2() {
        assert_eq!(
            assert_to_term(&source_to_stmt("if 2 == 3:\n    assert(2 == 4)\n").unwrap()),
            Some(Term::Compound(
                "Arrow".into(),
                vec![
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
                                vec![Term::Constant("Int".into()), Term::Constant("3".into())]
                            )
                        ]
                    ),
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
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_assert_to_term_3() {
        assert_eq!(
            assert_to_term(&source_to_stmt("for i in range(5, 8):\n    assert(i > 6)\n").unwrap()),
            Some(Term::Compound(
                "Arrow".into(),
                vec![
                    Term::Compound(
                        "BoolOp".into(),
                        vec![
                            Term::Constant("and".into()),
                            Term::Compound(
                                "Compare".into(),
                                vec![
                                    Term::Constant("<=".into()),
                                    Term::Compound(
                                        "Literal".into(),
                                        vec![
                                            Term::Constant("Int".into()),
                                            Term::Constant("5".into())
                                        ]
                                    ),
                                    Term::Compound(
                                        "Variable".into(),
                                        vec![Term::Constant("i".into())]
                                    )
                                ]
                            ),
                            Term::Compound(
                                "Compare".into(),
                                vec![
                                    Term::Constant("<".into()),
                                    Term::Compound(
                                        "Variable".into(),
                                        vec![Term::Constant("i".into())]
                                    ),
                                    Term::Compound(
                                        "Literal".into(),
                                        vec![
                                            Term::Constant("Int".into()),
                                            Term::Constant("8".into())
                                        ]
                                    )
                                ]
                            )
                        ]
                    ),
                    Term::Compound(
                        "Compare".into(),
                        vec![
                            Term::Constant(">".into()),
                            Term::Compound("Variable".into(), vec![Term::Constant("i".into())]),
                            Term::Compound(
                                "Literal".into(),
                                vec![Term::Constant("Int".into()), Term::Constant("6".into())]
                            )
                        ]
                    )
                ]
            ))
        )
    }

    #[test]
    fn test_evaluate_term_i64_1() {
        assert_eq!(
            expr_to_term(&source_to_expr("2").unwrap()).map(|x| evaluate_term_i64(&x)),
            Some(Some(2))
        )
    }

    #[test]
    fn test_evaluate_term_i64_2() {
        assert_eq!(
            expr_to_term(&source_to_expr("x").unwrap()).map(|x| evaluate_term_i64(&x)),
            Some(None)
        )
    }

    #[test]
    fn test_evaluate_term_i64_3() {
        assert_eq!(
            expr_to_term(&source_to_expr("3 + 5").unwrap()).map(|x| evaluate_term_i64(&x)),
            Some(Some(8))
        )
    }

    #[test]
    fn test_evaluate_term_bool_1() {
        assert_eq!(
            expr_to_term(&source_to_expr("2 == 2").unwrap()).map(|x| evaluate_term_bool(&x)),
            Some(Some(true))
        )
    }

    #[test]
    fn test_evaluate_term_bool_2() {
        assert_eq!(
            expr_to_term(&source_to_expr("2 == 3").unwrap()).map(|x| evaluate_term_bool(&x)),
            Some(Some(false))
        )
    }

    #[test]
    fn test_evaluate_term_bool_3() {
        assert_eq!(
            expr_to_term(&source_to_expr("x == 3").unwrap()).map(|x| evaluate_term_bool(&x)),
            Some(None)
        )
    }

    #[test]
    fn test_evaluate_term_bool_4() {
        assert_eq!(
            expr_to_term(&source_to_expr("8 == 3 + 5").unwrap()).map(|x| evaluate_term_bool(&x)),
            Some(Some(true))
        )
    }

    #[test]
    fn test_evaluate_term_bool_5() {
        assert_eq!(
            expr_to_term(&source_to_expr("20 % 3 > 5").unwrap()).map(|x| evaluate_term_bool(&x)),
            Some(Some(false))
        )
    }

    #[test]
    fn test_evaluate_term_bool_6() {
        assert_eq!(
            expr_to_term(&source_to_expr("1 > 5 and 3 == 3").unwrap())
                .map(|x| evaluate_term_bool(&x)),
            Some(Some(false))
        )
    }

    #[test]
    fn test_evaluate_term_bool_7() {
        assert_eq!(
            expr_to_term(&source_to_expr("1 > 5 or 3 == 3").unwrap())
                .map(|x| evaluate_term_bool(&x)),
            Some(Some(true))
        )
    }

    #[test]
    fn test_verify_assert_1() {
        let stmt = source_to_stmt("assert(2 == 2)").unwrap();
        assert_eq!(verify_assert(&[], &stmt, 5), true)
    }

    #[test]
    fn test_verify_assert_2() {
        let stmt = source_to_stmt("assert(2 == 3)").unwrap();
        assert_eq!(verify_assert(&[], &stmt, 5), false)
    }

    #[test]
    fn test_verify_assert_3() {
        let stmt = source_to_stmt("x = 3").unwrap();
        assert_eq!(verify_assert(&[], &stmt, 5), true)
    }

    #[test]
    fn test_verify_assert_4() {
        let stmt = source_to_stmt("assert(x == 3)").unwrap();
        assert_eq!(verify_assert(&[], &stmt, 5), false)
    }

    #[test]
    fn test_verify_assert_5() {
        let stmt = source_to_stmt("assert(x == 3)").unwrap();
        assert_eq!(
            verify_assert(
                &[Rule::Rule(2, assert_to_term(&stmt).unwrap(), Vec::new())],
                &stmt,
                5
            ),
            true
        )
    }

    #[test]
    fn test_verify_assert_6() {
        let stmt = source_to_stmt("assert(x == 3)").unwrap();
        let stmt_2 = source_to_stmt("if x == 3:\n    assert(y == 3)").unwrap();
        let stmt_3 = source_to_stmt("assert(y == 3)").unwrap();
        let facts = vec![
            Rule::Rule(2, assert_to_term(&stmt).unwrap(), Vec::new()),
            Rule::Rule(2, assert_to_term(&stmt_2).unwrap(), Vec::new()),
            Rule::Rule(
                2,
                Term::Variable("y".into()),
                vec![
                    Term::Compound(
                        "Arrow".into(),
                        vec![Term::Variable("x".into()), Term::Variable("y".into())],
                    ),
                    Term::Variable("x".into()),
                ],
            ),
            Rule::Rule(11, Term::Variable("x".into()), vec![]),
        ];
        assert_eq!(verify_assert(&facts, &stmt_3, 5), true)
    }

    #[test]
    fn test_verify_assert_7() {
        let stmt_2 = source_to_stmt("if x == 3:\n    assert(y == 3)").unwrap();
        let stmt_3 = source_to_stmt("assert(y == 3)").unwrap();
        let facts = vec![
            Rule::Rule(2, assert_to_term(&stmt_2).unwrap(), Vec::new()),
            Rule::Rule(
                2,
                Term::Variable("y".into()),
                vec![
                    Term::Compound(
                        "Arrow".into(),
                        vec![Term::Variable("x".into()), Term::Variable("y".into())],
                    ),
                    Term::Variable("x".into()),
                ],
            ),
            Rule::Rule(11, Term::Variable("x".into()), vec![]),
        ];
        assert_eq!(verify_assert(&facts, &stmt_3, 5), false)
    }

    #[test]
    fn test_verify_assert_8() {
        let stmt = source_to_stmt("assert(p == q)").unwrap();
        let stmt_2 = source_to_stmt("assert(q == p)").unwrap();
        let facts = vec![
            Rule::Rule(2, assert_to_term(&stmt).unwrap(), Vec::new()),
            Rule::Rule(
                2,
                Term::Compound(
                    "Compare".into(),
                    vec![
                        Term::Constant("==".into()),
                        Term::Variable("x".into()),
                        Term::Variable("y".into()),
                    ],
                ),
                vec![Term::Compound(
                    "Compare".into(),
                    vec![
                        Term::Constant("==".into()),
                        Term::Variable("y".into()),
                        Term::Variable("x".into()),
                    ],
                )],
            ),
            Rule::Rule(
                2,
                Term::Variable("y".into()),
                vec![
                    Term::Compound(
                        "Arrow".into(),
                        vec![Term::Variable("x".into()), Term::Variable("y".into())],
                    ),
                    Term::Variable("x".into()),
                ],
            ),
            Rule::Rule(11, Term::Variable("x".into()), vec![]),
        ];
        assert_eq!(verify_assert(&facts, &stmt_2, 5), true)
    }

    #[test]
    fn test_verify_assert_9() {
        let stmt = source_to_stmt("assert(p == q)").unwrap();
        let stmt_2 = source_to_stmt("assert(q == p)").unwrap();
        let facts = vec![
            Rule::Rule(2, assert_to_term(&stmt).unwrap(), Vec::new()),
            Rule::Rule(11, Term::Variable("x".into()), vec![]),
        ];
        assert_eq!(verify_assert(&facts, &stmt_2, 5), false)
    }

    #[test]
    fn test_update_facts_1() {
        let stmt = source_to_stmt("assert(2 == 3)").unwrap();
        let stmt_2 = source_to_stmt("assert(2 == 2)").unwrap();
        let mut facts = Vec::new();
        update_facts(&mut facts, &stmt);
        assert_eq!(
            facts,
            vec![Rule::Rule(2, assert_to_term(&stmt).unwrap(), Vec::new())]
        );
        update_facts(&mut facts, &stmt_2);
        assert_eq!(
            facts,
            vec![
                Rule::Rule(2, assert_to_term(&stmt).unwrap(), Vec::new()),
                Rule::Rule(2, assert_to_term(&stmt_2).unwrap(), Vec::new())
            ]
        );
    }

    #[test]
    fn test_update_facts_2() {
        let stmt = source_to_stmt("x = 3").unwrap();
        let stmt_2 = source_to_stmt("assert(x == 3)").unwrap();
        let mut facts = Vec::new();
        update_facts(&mut facts, &stmt);
        assert_eq!(
            facts,
            vec![Rule::Rule(2, assert_to_term(&stmt_2).unwrap(), Vec::new())]
        );
    }

    #[test]
    fn test_verify_function_1() {
        let source = r#"
def test_function():
    assert(2 == 3)
    assert(2 == 2)
"#;
        assert_eq!(
            verify_function(&source_to_stmt(source).unwrap(), 5),
            vec![TextRange::new(TextSize::new(26), TextSize::new(40))]
        );
    }

    #[test]
    fn test_verify_function_2() {
        let source = r#"
def test_function():
    x = 3
    assert(x == 3)
"#;
        assert_eq!(verify_function(&source_to_stmt(source).unwrap(), 5), vec![]);
    }

    #[test]
    fn test_verify_function_3() {
        let source = r#"
def test_function():
    x = 3
    if x == 3:
        assert(y == 1)
    if x == 4:
        assert(z == 2)
    assert(y == 1)
    assert(z == 2)
"#;
        assert_eq!(
            verify_function(&source_to_stmt(source).unwrap(), 5),
            vec![
                TextRange::new(TextSize::new(36), TextSize::new(69)),
                TextRange::new(TextSize::new(74), TextSize::new(107)),
                TextRange::new(TextSize::new(131), TextSize::new(145))
            ]
        );
    }
}
