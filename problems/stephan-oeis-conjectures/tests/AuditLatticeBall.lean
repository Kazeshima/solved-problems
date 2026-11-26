import LatticeBall

/-! Axiom audit: every result should depend only on `propext`, `Classical.choice`
and `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`). -/
#print axioms LatticeBall.mem_ballPoints
#print axioms LatticeBall.card_ballPoints_add
#print axioms LatticeBall.inv_two
#print axioms LatticeBall.inv_double
#print axioms LatticeBall.inv_two_pow
#print axioms LatticeBall.A055414_mod_sixteen
#print axioms LatticeBall.A055410_mod_eight

open LatticeBall in
example (n : ℕ) : (ballPoints 8 ((n : ℤ) ^ 2)).card % 16 = 1 := A055414_mod_sixteen n
