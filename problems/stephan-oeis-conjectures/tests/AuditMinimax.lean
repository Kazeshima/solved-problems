import MinimaxTrees

open MinimaxTrees

-- The statement and the definitions it depends on.
#check @a_zero
#check @a_succ
#check @b_zero
#check @b_succ
#check @a_values
#check @b_values
#check @a_even

#print axioms a_succ
#print axioms b_succ
#print axioms a_values
#print axioms b_values
#print axioms derivative_A
#print axioms two_mul_B
#print axioms a_even

example : a 2 = 2 ^ 1 * b 2 ∧ a 4 = 2 ^ 2 * b 4 ∧ a 6 = 2 ^ 3 * b 6 :=
  ⟨a_even 1, a_even 2, a_even 3⟩
