import Quadric.Five.CensusEval

namespace Quadric.Five.Census
theorem checkRows_append (S : System) (T : List Table) (h : ℕ) (xs ys : List (List ℕ)) :
    checkRows S T h (xs++ys)=(checkRows S T h xs && checkRows S T (h+xs.length) ys) := by
  induction xs generalizing h with
  | nil => simp [checkRows]
  | cons x xs ih =>
    simp only [List.cons_append,checkRows,List.length_cons,ih,Bool.and_assoc]
    congr 3 <;> omega
end Quadric.Five.Census
