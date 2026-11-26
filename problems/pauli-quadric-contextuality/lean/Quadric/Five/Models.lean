import Quadric.Five.Covers
import Quadric.Five.Witness
import Quadric.Action

namespace Quadric.Five
open Finset Matrix
open scoped BigOperators
abbrev Signing (n : ℕ) := Label n → Bit

def allPoints (n : ℕ) : Finset (Label n) := univ.erase 0
def quadric {n} (c : Label n) := (allPoints n).filter fun p => form c p=0

/-- Hermitian representative i^(a·b mod 2) X^a Z^b. On a commuting line the extra phase
is the product of the two quadratic bits. -/
def herm {n} (p r : Label n) := cross p r + q p*q r

def contexts {n} (S : Finset (Label n)) :=
  (S ×ˢ S).filter fun z => z.1+z.2∈S ∧ polar z.1 z.2=0
def bitScore {n} (s : Signing n) (p r : Label n) :=
  s p + s r + s (p+r) + herm p r
def faults {n} (S : Finset (Label n)) (s : Signing n) :=
  (contexts S).filter fun z => bitScore s z.1 z.2 ≠ 0

def AtLeast {n} (S : Finset (Label n)) (k : ℕ) : Prop := ∀ s, 6*k≤(faults S s).card

theorem mem_contexts {n} {S : Finset (Label n)} {p r : Label n} :
    (p,r)∈contexts S ↔ p∈S ∧ r∈S ∧ p+r∈S ∧ polar p r=0 := by
  simp only [contexts,mem_filter,mem_product]; tauto

theorem mem_faults {n} {S : Finset (Label n)} {s : Signing n} {p r : Label n} :
    (p,r)∈faults S s ↔ (p,r)∈contexts S ∧ bitScore s p r≠0 := by simp [faults]

theorem zero_quadric (n : ℕ) : quadric (0:Label n)=points n := by
  ext p; simp [quadric,allPoints,form,polar,cross]

theorem plus_contexts (n : ℕ) : contexts (points n)=pairs n := by
  ext ⟨p,r⟩; rw [mem_contexts,mem_pairs]
  have aux (h : p∈points n ∧ r∈points n ∧ p+r∈points n) : polar p r=0 := by
    obtain ⟨hp,hr,ht⟩ := h
    have hq := (mem_points.mp ht).2
    simpa only [q_add,(mem_points.mp hp).2,(mem_points.mp hr).2,zero_add] using hq
  tauto

def asBits {n} (s : Assignment n) : Signing n := fun p => if s p then 1 else 0
theorem plus_score {n} (s : Assignment n) {p r : Label n} (h : (p,r)∈pairs n) :
    score s (p,r)=chi (bitScore (asBits s) p r) := by
  obtain ⟨hp,hr,_⟩ := mem_pairs.mp h
  have hs (p : Label n) : value (s p)=chi (asBits s p) := by cases h : s p <;> norm_num [value,asBits,h,chi]
  rw [score_eval s h]; simp only [bitScore,herm,(mem_points.mp hp).2,zero_mul,add_zero,chi_add,hs]

theorem plus_faults {n} (s : Assignment n) :
    (faults (points n) (asBits s)).card=6*(bad s).card := by
  classical
  have hterm (z : Label n × Label n) (hz : z∈pairs n) :
      score s z = 1-2*(if bitScore (asBits s) z.1 z.2≠0 then (1:ℝ) else 0) := by
    rcases z with ⟨p,r⟩
    rw [plus_score s hz]; unfold chi; split_ifs <;> norm_num <;> contradiction
  have h := pair_score_sum s
  rw [sum_congr rfl hterm,sum_sub_distrib,←mul_sum,sum_boole] at h
  simp only [sum_const,nsmul_eq_mul,mul_one,six_to_one,Nat.cast_mul,Nat.cast_ofNat] at h
  unfold faults; rw [plus_contexts]
  exact_mod_cast (by linarith : (((pairs n).filter (fun z => bitScore (asBits s) z.1 z.2≠0)).card : ℝ)
    = 6*(bad s).card)

def slice {n} (S : Finset (Label n)) (c t : Label n) :=
  S.filter (coversPoint c t)

theorem slice_faults {n} (S : Finset (Label n)) (c t : Label n) (s : Signing n) :
    faults (slice S c t) s = (faults S s).filter fun z => coversPoint c t z.1 ∧ coversPoint c t z.2 := by
  ext ⟨p,r⟩
  have plus (h : polar p r=0) (hp : coversPoint c t p) (hr : coversPoint c t r) :
      coversPoint c t (p+r) := by
    unfold coversPoint at *; rw [polar_add_left,form_add,h,hp,hr,add_zero]
  simp only [mem_faults,mem_contexts,slice,mem_filter]
  tauto

theorem slice_bound {n} (S : Finset (Label n)) (c : Label n) (h0 : 0∉S)
    (s : Signing n) (k m : ℕ) (hm : 8*(m:ℝ)=dim n^2-4*chi (q c)*dim n)
    (hs : ∀ t∈centres c,k≤(faults (slice S c t) s).card) :
    (centres c).card*k≤(faults S s).card*m := by
  apply cover_bound (centres c) (faults S s) (fun t z => coversPoint c t z.1 ∧ coversPoint c t z.2)
  · rintro ⟨p,r⟩ hz
    obtain ⟨hp,hr,ht,hpr⟩ := mem_contexts.mp (mem_faults.mp hz).1
    have nz (p : Label n) (hp : p∈S) : p≠0 := fun hh => h0 (hh ▸ hp)
    have hn := cover_card c p r (nz p hp) (nz r hr) (nz _ ht) hpr
    exact_mod_cast (by linarith :
      ((((centres c).filter fun t => coversPoint c t p ∧ coversPoint c t r).card : ℕ):ℝ) = m)
  · intro t ht; simpa only [←slice_faults] using hs t ht

theorem canonical_centres5 : (centres (0:Label 5)).card=496 := by
  have h := centres_card (0:Label 5); norm_num [dim,q,chi] at h
  exact_mod_cast (by linarith : ((centres (0:Label 5)).card : ℝ)=496)

theorem canonical_centres4 : (centres (0:Label 4)).card=120 := by
  have h := centres_card (0:Label 4); norm_num [dim,q,chi] at h
  exact_mod_cast (by linarith : ((centres (0:Label 4)).card : ℝ)=120)

theorem five_from_sections (h : ∀ t∈centres (0:Label 5),AtLeast (slice (points 5) 0 t) 1575) :
    6975≤degree 5 := by
  obtain ⟨s,hs⟩ := degree_attained 5
  have hi := slice_bound (points 5) 0 (by simp) (asBits s) (6*1575) 112
    (by norm_num [dim,q,chi]) (fun t ht => h t ht _)
  rw [canonical_centres5,plus_faults] at hi
  omega

theorem slice_zero_full {n} (a : Label n) : slice (allPoints n) 0 a=quadric a := by
  ext p; simp only [slice,quadric,mem_filter,coversPoint,form]
  have hz : polar (0:Label n) p=0 := by simp [polar,cross]
  rw [hz,add_zero,polar_comm p a]
  have eq (b c : Bit) : b=c ↔ c+b=0 := by
    constructor
    · rintro rfl; exact CharTwo.add_self_eq_zero _
    · intro h; have := congrArg (fun z : Bit => c+z) h
      simpa [←add_assoc,CharTwo.add_self_eq_zero] using this
  exact and_congr_right fun _ => eq _ _

theorem four_from_elliptics (h : ∀ a∈centres (0:Label 4), AtLeast (quadric a) 315) :
    AtLeast (allPoints 4) 1575 := by
  intro s
  have hi := slice_bound (allPoints 4) 0 (by simp [allPoints]) s (6*315) 24
    (by norm_num [dim,q,chi]) (fun a ha => by rw [slice_zero_full]; exact h a ha s)
  rw [canonical_centres4] at hi; omega

/-- If all base elliptic quadrics have the certified minimum, every five-qubit assignment
inherits the lower bound as soon as its parabolic section embeddings are supplied. -/
theorem exact_from_sections (h : ∀ t∈centres (0:Label 5),AtLeast (slice (points 5) 0 t) 1575) :
    degree 5 = 6975 := le_antisymm witness_upper (five_from_sections h)

end Quadric.Five
