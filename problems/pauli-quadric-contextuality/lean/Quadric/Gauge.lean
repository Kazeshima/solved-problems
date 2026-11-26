import Quadric.Counts

namespace Quadric
open Finset

/-- A ratio of two sign assignments with the same line products has zero parity on every line. -/
def Gauge {n} (h : Label n → Bit) : Prop :=
  h 0=0 ∧ ∀ p r, (p,r) ∈ pairs n → h (p+r) = h p + h r

private theorem line_add {n} {h : Label n → Bit} (hg : Gauge h) {p r : Label n}
    (hp : q p=0) (hr : q r=0) (ht : q (p+r)=0) :
    h (p+r) = h p + h r := by
  by_cases hz : p=0
  · subst p; simp [hg.1]
  by_cases hw : r=0
  · subst r; simp [hg.1]
  by_cases hs : p+r=0
  · have he := (add_eq_zero_iff_same _ _).mp hs
    subst r; simp [hg.1,CharTwo.add_self_eq_zero]
  exact hg.2 p r (mem_pairs.mpr
    ⟨mem_points.mpr ⟨hz,hp⟩,mem_points.mpr ⟨hw,hr⟩,
     mem_points.mpr ⟨hs,ht⟩⟩)

theorem gauge_extends {n} {h : Label n → Bit} (hg : Gauge h) :
    ∃ f : Label n →+ Bit, ∀ p ∈ points n, f p = h p := by
  let f : Label n → Bit := fun p => h (p.1,0) + h (0,p.2)
  have hx (a c : Word n) : h (a+c,0) = h (a,0)+h (c,0) := by
    simpa using line_add hg (p:=(a,0)) (r:=(c,0))
      (by simp [q]) (by simp [q]) (by simp [q])
  have hz (b d : Word n) : h (0,b+d) = h (0,b)+h (0,d) := by
    simpa using line_add hg (p:=(0,b)) (r:=(0,d))
      (by simp [q]) (by simp [q]) (by simp [q])
  refine ⟨{toFun:=f, map_zero':=?_, map_add':=?_},?_⟩
  · change h 0 + h 0=0; simp [hg.1]
  · intro p r
    change h (p.1+r.1,0)+h (0,p.2+r.2) = _
    rw [hx,hz]; dsimp [f]; abel
  · rintro ⟨a,b⟩ hp
    change h (a,0)+h (0,b) = h (a,b)
    have he := line_add hg (p:=(a,0)) (r:=(0,b)) (by simp [q]) (by simp [q])
      (by simpa [q] using (mem_points.mp hp).2)
    simpa using he.symm

theorem hom_is_gauge {n} (h : Label n →+ Bit) : Gauge h :=
  ⟨h.map_zero,fun p r _ => h.map_add p r⟩

end Quadric
