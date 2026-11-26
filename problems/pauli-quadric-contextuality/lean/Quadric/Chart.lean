import Quadric.Four
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Notation

namespace Quadric.Four
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
attribute [local irreducible] bad points pairs lines
open Finset Matrix
open scoped BigOperators

abbrev W3 := Word 3
abbrev Sym3 := Matrix (Fin 3) (Fin 3) Bit

/-- Symmetric matrix for the Lagrangian graph [I|M]. -/
def chartMatrix (d e : W3) : Sym3 :=
  !![d 0, d 0*d 1+e 2, d 0*d 2+e 1;
     d 0*d 1+e 2, d 1, d 1*d 2+e 0;
     d 0*d 2+e 1, d 1*d 2+e 0, d 2]

def chart (d e : W3) : Label 4 :=
  (Fin.cons 1 e, Fin.cons (dot d e) d)

def wedge (d u : W3) : W3 :=
  ![d 1*u 2+d 2*u 1, d 0*u 2+d 2*u 0, d 0*u 1+d 1*u 0]

def negativeBit (p : Label 4) : Bit := if p.1≠0 ∧ p.2≠0 then 1 else 0

theorem mixed_value (p : Label 4) : value (mixed p) = chi (negativeBit p) := by
  by_cases h : p.1≠0 ∧ p.2≠0 <;> norm_num [negativeBit,chi,value,mixed,h]

private theorem bad_by_score {n} (s : Assignment n) (p r : Label n)
    (hp : (p,r) ∈ pairs n) (hs : score s (p,r) = -1) : triple (p,r) ∈ bad s := by
  unfold bad
  have hl : triple (p,r) ∈ lines n := by unfold lines; exact mem_image_of_mem triple hp
  exact mem_filter.mpr ⟨hl,(score_rep s hp).trans hs⟩

theorem bad_of_bits {p r : Label 4} (h : (p,r) ∈ pairs 4)
    (hb : negativeBit p + negativeBit r + negativeBit (p+r) + cross p r = 1) :
    triple (p,r) ∈ bad mixed := by
  have hs : score mixed (p,r) = -1 := by
    rw [score_eval mixed h,mixed_value,mixed_value,mixed_value,
      ← chi_add,← chi_add,← chi_add,hb]
    norm_num [chi]
  exact @bad_by_score 4 mixed p r h hs

theorem chart_matrix_update (d e u : W3) :
    chartMatrix (d+u) (e+wedge d u) = chartMatrix d e + Matrix.vecMulVec u u := by
  exact (by decide : ∀ d e u : W3, chartMatrix (d+u) (e+wedge d u) =
    chartMatrix d e + Matrix.vecMulVec u u) d e u

/-- Finite-field data for one principal-minor chart. The calculation uses kernel reduction. -/
private theorem chart_bits : ∀ d e u : W3, u ≠ 0 →
    let p := chart d e
    let r := chart (d+u) (e+wedge d u)
    (p ≠ 0 ∧ q p = 0) ∧ (r ≠ 0 ∧ q r = 0) ∧
    (p+r ≠ 0 ∧ q (p+r) = 0) ∧
    negativeBit p + negativeBit r + negativeBit (p+r) + cross p r = 1 := by
  decide

theorem chart_pencil_violated (d e u : W3) (hu : u ≠ 0) :
    triple (chart d e,chart (d+u) (e+wedge d u)) ∈ bad mixed := by
  obtain ⟨hp,hr,ht,hb⟩ := chart_bits d e u hu
  let p := chart d e
  let r := chart (d+u) (e+wedge d u)
  exact @bad_of_bits p r ((@mem_pairs 4 p r).mpr
    ⟨(@mem_points 4 p).mpr hp,(@mem_points 4 r).mpr hr,(@mem_points 4 (p+r)).mpr ht⟩) hb

end Quadric.Four
