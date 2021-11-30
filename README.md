# Verified SAT

An almost certainly correct (and very slow) DPLL sat solver.

The proofs are parametric over a function for picking the next variable to branch on.

The bulk of the work is in proving various lemmas about assignment in `src/assign.lean`.

Some trivial sat problems are solved in `src/problems.lean`
