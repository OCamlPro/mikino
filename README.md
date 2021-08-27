Mikino is a (relatively) simple induction and BMC engine.

You can run in demo mode with `mikino demo demo.mkn`. This will write a heavily commented example
system in `demo.mkn`. Mikino files are designed to work well with Rust syntax highlighting.

# License

Mikino is distributed under the terms of both the MIT license and the Apache License (Version 2.0).

See [LICENSE-APACHE](./LICENSE-APACHE) and [LICENSE-MIT](./LICENSE-MIT) for details.

# Transition Systems

A (transition) system is composed of some variable declarations, of type `bool`, `int` or `rat`
(rational). A valuation of these variables is usually called a *state*. (An `int` is a
*mathematical* integer here: it cannot over/underflow. A `rat` is a fraction of `int`s.)

> Let's use a simple counter system as an example. Say this system has two variables, `cnt` of type
> `int` and `inc` of type bool.

The definition of a system features an *initial predicate*. It is a boolean expression over the variables of the system that evaluate to true on the initial states of the system.

> Assume now that we want to allow our counter's `cnt` variable's initial value to be anything as
> long as it is positive. Our initial predicate will be `(≥ cnt 0)`. Note that variable `inc` is
> irrelevant in this predicate.

Next, the *transition relation* of the system is an expression over two versions of the variables:
the *current* variables, and the *next* variables. The transition relation is a relation between the
current state and the next state that evaluates to true if the next state is a legal successor of
the current one. A the *next* version of a variable `v` is simply written `v`, and its *current*
version is written `(pre v)`.

> Our counter should increase by `1` whenever variable `inc` is true, and maintain its value
> otherwise. There is several ways to write this, for instance
>
> ```
> (or (and inc (= cnt (+ (pre cnt) 1))) (and (not inc) (= cnt (pre cnt))))
> ```
>
> or
>
> ```
> (ite     inc (= cnt (+ (pre cnt) 1))                 (= cnt (pre cnt)) )
> ```

Last, the transition system has a list of named Proof Obligations (POs) which are boolean
expressions over the variables. The system is **safe** if and only if it is not possible to reach a
falsification of any of those POs from the initial states by applying the transition relation
repeatedly.

> A reasonable PO for the counter system is `(≥ cnt 0)`. The system is safe for this PO as no
> reachable state of the counter can falsify it.
>
> The PO `(not (= cnt 7))` does not hold in all reachable states, in fact the initial state `{ cnt:
> 7, inc: _ }` falsifies it. But assume we change the initial predicate to be `(= cnt 0)`. Then the
> PO is still falsifiable by applying the transition relation seven times to the (only) initial
> state `{ cnt: 0, inc: _ }`. In all seven transitions, we need `inc` to be true so that `cnt` is
> actually incremented.

A falsification of a PO is a *concrete trace*: a sequence of states *i)* that starts from an initial
state, *ii)* where successors are valid by the transition relation and *iii)* such that the last
state of the sequence falsifies the PO.

> A falsification of `(not (= cnt 7))` for the last system above with the modified initial predicate
> is
>
> ```
> Step 0
> | cnt: 0
> Step 1
> | cnt: 1
> | inc: true
> Step 2
> | cnt: 2
> | inc: true
> Step 3
> | cnt: 3
> | inc: true
> Step 4
> | cnt: 4
> | inc: true
> Step 5
> | cnt: 5
> | inc: true
> Step 6
> | cnt: 6
> | inc: true
> Step 7
> | cnt: 7
> | inc: true
> ```
