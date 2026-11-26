import Quadric.States
import Quadric.Clifford

namespace Quadric.Four
open Finset Matrix
open scoped BigOperators
attribute [local irreducible] points pairs lines bad

def push (C : Clifford 4) (s : Signing) : Signing :=
  fun p => spin s (C.perm.symm p.val) + C.phase (C.perm.symm p.val)

theorem spin_push (C : Clifford 4) (s : Signing) {p : Lab} (hp : p ∈ points 4) :
    spin (push C s) (C.perm p) = spin s p + C.phase p := by
  have h := (C.map_point p).mpr hp
  simp only [spin,dif_pos h,dif_pos hp,push,Equiv.symm_apply_apply]

def canonical : Signing := fun p => if mixed p then 1 else 0
theorem canonical_value {p : Lab} (hp : p ∈ points 4) :
    value (assign canonical p)=value (mixed p) := by
  rw [sign_value]; simp only [spin,dif_pos hp,canonical]
  cases mixed p <;> norm_num [chi,value]

theorem operator_eq_of_signs {s t : Assignment 4}
    (h : ∀ p ∈ points 4, value (s p) = value (t p)) : operator s = operator t := by
  unfold operator; exact sum_congr rfl fun p hp => by simp only [term,h p hp]

theorem matrix_canonical : matrixOf canonical = candidate :=
  (operator_eq_of_signs (fun _ hp => canonical_value hp)).trans witness_operator

theorem bad_triple_iff {n} (s : Assignment n) {p r : Label n}
    (h : (p,r) ∈ pairs n) : triple (p,r) ∈ bad s ↔ score s (p,r) = -1 := by
  have hl : triple (p,r) ∈ lines n := by unfold lines; exact mem_image_of_mem triple h
  unfold bad; rw [mem_filter,and_iff_right hl,score_rep s h]

theorem violations_canonical : violations canonical = bad mixed := by
  ext l
  by_cases hl : l ∈ lines 4
  · obtain ⟨⟨p,r⟩,h,rfl⟩ := (by simpa only [lines,mem_image] using hl :
      ∃ z ∈ pairs 4, triple z=l)
    rw [violations,bad_triple_iff _ h,bad_triple_iff _ h,score_eval _ h,score_eval _ h]
    obtain ⟨hp,hr,ht⟩ := mem_pairs.mp h
    rw [canonical_value hp,canonical_value hr,canonical_value ht]
  · simp [violations,bad,hl]
def canonicalOpt : Opt := ⟨canonical,by rw [violations_canonical,witness_count,degree_four]⟩

theorem matrix_push (C : Clifford 4) (s : Signing) :
    matrixOf (push C s)=C.conj (matrixOf s) := by
  classical
  unfold matrixOf operator
  simp only [Clifford.conj,mul_sum,sum_mul]
  symm
  apply sum_bij (fun p _ => C.perm p) (fun p hp => (C.map_point p).mpr hp)
    (fun _ _ _ _ h => C.perm.injective h)
  · intro p hp
    refine ⟨C.perm.symm p,?_,C.perm.apply_symm_apply _⟩
    apply (C.map_point _).mp
    simpa only [Equiv.apply_symm_apply] using hp
  · intro p hp
    simp only [term,Matrix.mul_smul,Matrix.smul_mul,C.normal,smul_smul,
      sign_value,spin_push C s hp,chi_add]

def lineMap (C : Clifford 4) (l : Finset Lab) : Finset Lab := l.image C.perm

theorem map_triple (C : Clifford 4) (p r : Lab) :
    lineMap C (triple (p,r)) = triple (C.perm p,C.perm r) := by
  simp [lineMap,triple]

theorem map_pair (C : Clifford 4) {p r : Lab} (h : (p,r) ∈ pairs 4) :
    (C.perm p,C.perm r) ∈ pairs 4 := by
  simpa only [mem_pairs,← C.map_add,C.map_point] using h

theorem score_push (C : Clifford 4) (s : Signing) {p r : Lab} (hh : (p,r) ∈ pairs 4) :
    score (assign (push C s)) (C.perm p,C.perm r) = score (assign s) (p,r) := by
  obtain ⟨hp,hr,ht⟩ := mem_pairs.mp hh
  rw [score_eval _ (map_pair C hh),score_eval _ hh]
  simp only [sign_value,← C.map_add,spin_push C s hp,spin_push C s hr,spin_push C s ht,
    ← chi_add]
  congr 1
  have h := (C.cocycle p r).2
  calc
    _ = (spin s p + spin s r + spin s (p+r)) + C.phase (p+r) +
      (C.phase p+C.phase r+cross (C.perm p) (C.perm r)) := by abel
    _ = _ := by rw [←h]; abel_nf; simp [CharTwo.two_eq_zero]

theorem push_inv (C : Clifford 4) (s : Signing) : push C.inv (push C s) = s := by
  funext p
  change spin (push C s) (C.perm p.1) + C.phase (C.perm.symm (C.perm p.1)) = _
  rw [spin_push C s p.2,Equiv.symm_apply_apply,add_assoc,CharTwo.add_self_eq_zero,add_zero,spin_point]

theorem map_bad_subset (C : Clifford 4) (s : Signing) :
    (violations s).image (lineMap C) ⊆ violations (push C s) := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hl
  have hline : k ∈ lines 4 := by
    unfold violations bad at hk; exact (mem_filter.mp hk).1
  unfold lines at hline
  obtain ⟨⟨p,r⟩,h,rfl⟩ := mem_image.mp hline
  rw [map_triple]
  unfold violations at hk ⊢
  exact (bad_triple_iff _ (map_pair C h)).mpr
    ((score_push C s h).trans ((bad_triple_iff _ h).mp hk))

theorem map_bad (C : Clifford 4) (s : Signing) :
    (violations s).image (lineMap C) = violations (push C s) := by
  apply Subset.antisymm (map_bad_subset C s)
  intro l hl
  have h := map_bad_subset C.inv (push C s) (mem_image_of_mem _ hl)
  rw [push_inv] at h
  exact mem_image.mpr ⟨_,h,by simp [lineMap,Clifford.inv,image_image,Function.comp_def]⟩

theorem lineMap_injective (C : Clifford 4) : Function.Injective (lineMap C) := by
  intro a b h
  have := congrArg (lineMap C.inv) h
  simpa [lineMap,Clifford.inv,image_image,Function.comp_def] using this

def optMove (C : Clifford 4) (s : Opt) : Opt := ⟨push C s.val,by
  rw [←map_bad,card_image_of_injective _ (lineMap_injective C)]; exact s.property⟩

theorem move_ray (C : Clifford 4) (u : W → ℝ) :
    C.conj (ray u)=ray (C.U *ᵥ u) := by
  ext i j
  simp only [Clifford.conj,Matrix.mul_apply,Matrix.transpose_apply,ray,Matrix.mulVec,dotProduct]
  simp only [sum_mul,mul_sum]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _; ring

theorem move_ray_formula (C : Clifford 4) {s : Signing} {u : W → ℝ}
    (h : matrixOf s = (48:ℝ) • ray u - (3:ℝ) • (1:Mat 4)) :
    matrixOf (push C s) = (48:ℝ) • ray (C.U *ᵥ u) - (3:ℝ) • (1:Mat 4) := by
  rw [matrix_push,h]
  change C.U * (_-_) * C.Uᵀ = _
  rw [mul_sub,sub_mul,Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.smul_mul,mul_one,C.rightInv]
  rw [show C.U * ray u * C.Uᵀ = _ from move_ray C u]

end Quadric.Four
