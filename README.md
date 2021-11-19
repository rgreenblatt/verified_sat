# Verified SAT

An almost certainly correct (and very slow) DPLL sat solver

The meat of the work is in proving various lemma about assignment in `assign.lean`.

The proofs are parametric over a function for picking the next variable to branch on.
