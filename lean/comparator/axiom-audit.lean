import ClassicalSolution

/-
Axiom audit for the ClassicalSchur comparator package. Prints the `#print axioms`
closure of each theorem that `config.json` lists. Each closure must be a subset
of {propext, Classical.choice, Quot.sound}. The comparator enforces
`permitted_axioms` itself; this file shows the closures to a reviewer and to
`check-conformance.sh`.

Run from the `lean/` directory: lake env lean comparator/classical/axiom-audit.lean
-/

#print axioms ClassicalSchurClaims.erL_four
#print axioms ClassicalSchurClaims.erL_five_bounds
#print axioms ClassicalSchurClaims.le_erL_of_groupPartition
#print axioms ClassicalSchurClaims.lift_lemma
#print axioms ClassicalSchurClaims.le_sdeg_blockSums
#print axioms ClassicalSchurClaims.erL_le
