# v0.9.1

- added a function generating `rsmt2::SmtConf` from a string Z3 CLI invokation with arguments
- fixed parser for `and` and `or` operators

# v0.9.0

- added a notion of script
	- very similar to SMT-LIB 2 but with Rust-flavored syntax
	- adds branching (if-then-else) over check-sat-s compared to SMT-LIB
	- adds `panic`, `exit`, `println`... commands
	- allows binding check-sat results to (meta-)variables
- various QoL improvements
- minor bugfixes
