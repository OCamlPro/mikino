//! Tests over expressions.

crate::prelude!();

#[test]
fn typing_implies() {
    let lft = build_expr!((a: bool));
    let rgt = build_expr!((> (n: int) 7));

    let typ = expr::Op::Implies.type_check(&[lft, rgt]).unwrap();

    assert_eq!(typ, expr::Typ::Bool);
}

#[test]
fn typing_ite() {
    let cnd = build_expr!((a: bool));
    let thn = build_expr!((+ (n_1: int) 2));
    let els = build_expr!((- (n_2: int) 10));

    let typ = expr::Op::Ite.type_check(&[cnd, thn, els]).unwrap();

    assert_eq!(typ, expr::Typ::Int);

    let cnd = build_expr!((a: bool));
    let thn = build_expr!((and (b: bool) true));
    let els = build_expr!((or (c: bool) (d: bool)));

    let typ = expr::Op::Ite.type_check(&[cnd, thn, els]).unwrap();

    assert_eq!(typ, expr::Typ::Bool);
}

#[test]
fn typing_ite_fail() {
    let cnd = build_expr!((a: int));
    let thn = build_expr!((+ (n_1: int) 2));
    let els = build_expr!((- (n_2: int) 10));

    let err = expr::Op::Ite.type_check(&[cnd, thn, els]).unwrap_err();

    assert_eq!(
        err.to_string(),
        "expected first argument of type `bool`, got `int`",
    );

    let cnd = build_expr!((a: bool));
    let thn = build_expr!((and (b: bool) true));
    let els = build_expr!((n: int));

    let err = expr::Op::Ite.type_check(&[cnd, thn, els]).unwrap_err();

    assert_eq!(
        err.to_string(),
        "`ite`'s second and third arguments should have the same type, got `bool` and `int`",
    );
}

#[test]
fn typing_cmp() {
    let a_1 = build_expr!((+ (a: int) 2));
    let a_2 = build_expr!((-(b: int)(c: int)));
    let a_3 = build_expr!((* (n: int) 7));

    let typ = expr::Op::Ge.type_check(&[a_1, a_2, a_3]).unwrap();
    assert_eq!(typ, expr::Typ::Bool);
}

macro_rules! parse_build_check {
    {
        input: $input:expr,
        decls: ($($decls:tt)*),
        $then:tt: $expect:expr $(,)?
    } => {{
        let input = $input;
        println!("input:");
        for line in input.lines() {
            println!("    {}", line);
        }
        let decls = build_decls!($($decls)*).unwrap();
        let ast = parse::rules::hsmt_expr(input).unwrap();
        let res = ast
            .inner_to_expr(|var, prime_opt| {
                let span = var.span;
                let var = if prime_opt.is_some() {
                    decls.get_next_var(*var)
                } else {
                    decls.get_curr_var(*var)
                }
                .ok_or_else(|| PError::new(format!("undeclared variable {:?}", var), span))?;
                Ok(parse::Spn::new(expr::PExpr::new_var(var), span))
            });
        parse_build_check!(@then $then, res, $expect)
    }};

    { @then expect, $res:expr, $expect:expr $(,)? } => {{
        let expr = $res.unwrap();
        println!("> {}", expr);
        assert_eq!(expr.to_string(), $expect);
    }};
    { @then fail, $res:expr, $expect:expr $(,)? } => {{
        let expr = $res.unwrap_err().to_string();
        println!("> {}", expr);
        assert_eq!(expr, $expect);
    }};
}

#[test]
fn collapse() {
    parse_build_check! {
        input: "a - b - 'c - d",
        decls: (a, b, c, d: int),
        expect: "(- a@0 b@0 c@1 d@0)",
    }
    parse_build_check! {
        input: "a + 'b + c + 'd",
        decls: (a, b, c, d: int),
        expect: "(+ a@0 b@1 c@0 d@1)",
    }
    parse_build_check! {
        input: "a > 'b > c > 'd",
        decls: (a, b, c, d: int),
        expect: "(> a@0 b@1 c@0 d@1)",
    }
    parse_build_check! {
        input: "a = 'b = c = 'd",
        decls: (a, b, c, d: int),
        expect: "(= a@0 b@1 c@0 d@1)",
    }
}

#[test]
fn precedence() {
    parse_build_check! {
        input: "a + b * 'c",
        decls: (a, b, c: int),
        expect: "(+ a@0 (* b@0 c@1))",
    }
    parse_build_check! {
        input: "a < if 'a + 2 > b { 7 } else if 'a > c { c + 2 } else { 10 }",
        decls: (a, b, c: int),
        expect: "(< a@0 (ite (> (+ a@1 2) b@0) 7 (ite (> a@1 c@0) (+ c@0 2) 10)))",
    }
    parse_build_check! {
        input: "boo_1 && a < if 'a + 2 > b { 7 } else if 'a > c { c + 2 } else { 10 } && boo_2",
        decls: (
            a, b, c: int
            boo_1, boo_2: bool
        ),
        expect: "(and \
            boo_1@0 \
            (< a@0 (ite (> (+ a@1 2) b@0) 7 (ite (> a@1 c@0) (+ c@0 2) 10))) \
            boo_2@0\
        )",
    }
}

#[test]
fn type_check_fail() {
    parse_build_check! {
        input: "a && b && c",
        decls: (
            a, b: bool
            c: int
        ),
        fail: "[2, 4] `and`'s arguments must all be boolean expressions",
    }
}
