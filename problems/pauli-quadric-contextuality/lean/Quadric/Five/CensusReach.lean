import Quadric.Five.Paths

namespace Quadric.Five.Moves
def Reach (table : List Move) (s t : ℕ→Bool) : Prop := ∃w : List ℕ,action table w s=t

theorem action_append (table : List Move) (u v : List ℕ) (s : ℕ→Bool) :
    action table (u++v) s=action table v (action table u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append,action,ih]

theorem Reach.trans {table : List Move} {s t v : ℕ→Bool} (h : Reach table s t) (k : Reach table t v) :
    Reach table s v := by
  obtain ⟨a,rfl⟩:=h
  obtain ⟨b,rfl⟩:=k
  exact ⟨a++b,action_append ..⟩
end Quadric.Five.Moves
