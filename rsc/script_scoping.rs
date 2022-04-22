//! # Scoping
//!
//! Remember that hsmt scripts have two notions of variables. SMT-level **variables** are declared
//! with `vars { ... }`, which are then declared as-is at SMT-level. **Meta-variables** store check
//! sat results.
//!
//! Now, during parsing mikino checks the well-definedness of expressions and meta-variable uses.
//! These checks are conservative, in the sense that whenever the script branches, only variables
//! and meta-variables declared/defined in all branches *that do not exit* are usable after the
//! branching.
//! 
//! Branches do *exit* whenever they necessarily go through an `exit!(...)` or a `panic!(...)`.
//!
//! Let's illustrate this.

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
//
// assert { next_next_var = next_var }


/// Obviously, `reset!()` makes all SMT-level variables disappear.
echo!()
echo!("resetting")
echo!()
reset!()

// So the following does not compile:
// 
// assert { cnt ≥ 0 }


/// **Meta**-variables however are still visible, no reason to discard them.
if cnt_pos_is_sat {
	if next_is_sat {
		echo!("both `cnt ≥ 0` and the definition of `next_cnt` were sat")
	} else {
		echo!("only `cnt ≥ 0` was sat")
	}
} else {
	echo!("`cnt ≥ 0` was unsat")
}

echo!()
echo!("all done")

exit!()

