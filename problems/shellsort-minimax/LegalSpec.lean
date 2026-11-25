import Certificates

namespace ShellMinimax.Certificate

/-- The finite checker accepts exactly the positive decreasing lists below n
whose final entry is 1, including the one-pass table [1]. -/
theorem legal_last {n : Nat} (H : List Nat) : Legal n H ↔
    H.Pairwise (· > ·) ∧ H.getLast? = some 1 ∧ ∀ g ∈ H, 0 < g ∧ g < n := by
  constructor
  · intro h
    refine ⟨h.1, ?_, h.2.2⟩
    induction H with
    | nil => simp [Legal] at h
    | cons a as ih =>
      cases as with
      | nil =>
        have e : 1 = a := by simpa using h.2.1
        simp [← e]
      | cons b bs =>
        have ab := (List.pairwise_cons.mp h.1).1 b (by simp)
        have bp := (h.2.2 b (by simp)).1
        have ne : 1 ≠ a := by omega
        have hm : 1 ∈ b :: bs := (List.mem_cons.mp h.2.1).resolve_left ne
        exact ih ⟨h.1.of_cons,hm,fun g hg => h.2.2 g (List.mem_cons_of_mem a hg)⟩
  · rintro ⟨order,last,bounds⟩
    refine ⟨order,?_,bounds⟩
    exact List.mem_of_getLast? last

end ShellMinimax.Certificate
