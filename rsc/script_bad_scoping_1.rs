/// Some regular (SMT-level) variables.
vars {
	cnt : int,
}

/// This expression is legal because `cnt` has been declared, mikino accepts it.
assert {
	cnt ≥ 0,
}

let cnt_pos_is_sat = check_sat!();

/// Branching.
if cnt_pos_is_sat {
	echo!("`cnt ≥ 0` is sat")
	/// Declaring more SMT-level variables.
	vars {
		next_cnt : int,
		reset counting : bool,
	}
} else {
	panic!("this should be sat")
}

/// At this point `next_cnt`, `reset` and `counting` are all visible because
/// - they were declared in the `then` branch,
/// - the `else` branch panics (exits) so it does not matter that they were not exist there,
/// - the implicit `otherwise` branch panics by default, so same as the `else` branch.
assert {
	next_cnt =
		if reset { 0 } else if counting { cnt + 1 } else { cnt },
}



let next_is_sat = check_sat!();

if next_is_sat {
	echo!("next is also sat")
	vars {
		next_next_var : int
	}
} else {
	echo!("next is unsat")
}

// At this point referring to `next_next_var` will cause an error because it *might* not be
// declared. Indeed, if `next_is_sat` is `unsat` we go through the `else` branch which does not
// exit and does not declare `next_next_var`.
// Does not compile:

assert { next_next_var = next_var }



