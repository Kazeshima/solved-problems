import Quadric.Five.Forms

namespace Quadric.Five.Small
def inHyperplane (u : ℕ) (l : Line) := sym 3 u l.a == 0 && sym 3 u l.b == 0 && sym 3 u l.c == 0
def hyperplanes := labels 3
def hyperErrors (s : ℕ→Bool) (u : ℕ) := errors (full3.filter (inHyperplane u)) s

private theorem as_total {α : Type*} (xs : List α) (f : α→Bool) :
    total xs (fun i=>((f i).toNat:ℤ))=(xs.countP f:ℕ) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [ih,h,List.countP_cons,add_comm]

def multiplicity (l : Line) := hyperplanes.countP (fun u=>inHyperplane u l)

theorem sum_hyperplanes (s : ℕ→Bool) (m : ∀l∈full3,multiplicity l=15) :
    total hyperplanes (fun u=>(hyperErrors s u : ℤ))=15*(errors full3 s : ℤ) := by
  have h (u : ℕ) : (hyperErrors s u:ℤ)=total full3 (fun l=>
      (((inHyperplane u l).toNat:ℤ)*(Small.failure s l).toNat)) := by
    unfold hyperErrors errors; rw [List.countP_filter,←as_total]
    apply total_congr; intro l _; cases inHyperplane u l <;> cases Small.failure s l <;> decide
  unfold errors
  rw [total_congr _ (fun u _=>h u),total_comm,←as_total,←total_mul]
  apply total_congr; intro l hl
  have e:=m l hl
  have ht:= as_total hyperplanes (fun u=>inHyperplane u l)
  rw [show hyperplanes.countP (fun u=>inHyperplane u l)=15 from e] at ht
  cases hh : Small.failure s l <;> simp [hh,total_zero,ht]

theorem cheap_hyperplane (s : ℕ→Bool) (low : errors full3 s ≤ 92)
    (m : ∀l∈full3,multiplicity l=15) : ∃u∈hyperplanes,hyperErrors s u≤21 := by
  by_contra! bad
  have lb:= total_le hyperplanes (f:=fun _=>(22:ℤ)) (g:=fun u=>(hyperErrors s u:ℤ))
    (fun u hu=>by change (22:ℤ)≤(hyperErrors s u:ℤ); have := bad u hu; omega)
  have size : total hyperplanes (fun _=>(22:ℤ))=1386 := by decide +kernel
  rw [size,sum_hyperplanes s m] at lb
  omega

end Quadric.Five.Small
