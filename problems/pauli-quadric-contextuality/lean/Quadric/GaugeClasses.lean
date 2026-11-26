import Quadric.Action
import Quadric.Phase
import Quadric.Gauge

namespace Quadric.Four
open Finset Matrix
open scoped BigOperators
attribute [local irreducible] points lines pairs bad

def lineBit (s : Signing) (p r : Lab) : Bit :=
  spin s p + spin s r + spin s (p+r) + cross p r

theorem score_bits (s : Signing) {p r : Lab} (hp : (p,r) ∈ pairs 4) :
    score (assign s) (p,r) = chi (lineBit s p r) := by
  rw [score_eval _ hp]; simp only [sign_value,lineBit,chi_add]

theorem violations_eq_iff (s t : Signing) :
    violations s = violations t ↔
    ∀ p r : Lab, (p,r) ∈ pairs 4 → lineBit s p r=lineBit t p r := by
  constructor
  · intro he p r hh
    have hl : (triple (p,r) ∈ violations s) ↔ triple (p,r) ∈ violations t := by rw [he]
    change triple (p,r) ∈ bad (assign s) ↔ triple (p,r) ∈ bad (assign t) at hl
    rw [bad_triple_iff _ hh,bad_triple_iff _ hh,score_bits s hh,score_bits t hh] at hl
    have uniq (b c : Bit) : (chi b = -1 ↔ chi c = -1) → b=c := by
      fin_cases b <;> fin_cases c <;> norm_num [chi]
    exact uniq _ _ hl
  · intro h
    ext l
    by_cases hl : l ∈ lines 4
    · unfold lines at hl
      obtain ⟨⟨p,r⟩,hh,rfl⟩ := mem_image.mp hl
      change _ ∈ bad (assign s) ↔ _ ∈ bad (assign t)
      rw [bad_triple_iff _ hh,bad_triple_iff _ hh,score_bits s hh,score_bits t hh,h _ _ hh]
    · simp [violations,bad,hl]

theorem word_dual (g : W →+ Bit) : ∀ x, g x = dot (fun i => g (axis i)) x := by
  apply axis_induction
  · simp
  · intro x i hx; rw [map_add,dot_add,hx,dot_axis]

theorem label_dual (g : Lab →+ Bit) : ∃ c : Lab, ∀ p, g p = polar c p := by
  let xhom : W →+ Bit := {
    toFun := fun x => g (x,0)
    map_zero' := g.map_zero
    map_add' := fun x y => by simpa using g.map_add (x,0) (y,0)}
  let zhom : W →+ Bit := {
    toFun := fun x => g (0,x)
    map_zero' := g.map_zero
    map_add' := fun x y => by simpa using g.map_add (0,x) (0,y)}
  refine ⟨(fun i => zhom (axis i),fun i => xhom (axis i)),?_⟩
  rintro ⟨a,b⟩
  calc
    g (a,b) = xhom a + zhom b := by
      simpa [xhom,zhom] using g.map_add (a,0) (0,b)
    _ = _ := by rw [word_dual xhom,word_dual zhom]; simp only [polar,cross]; rw [dot_comm b]

def gaugeSign (c : Lab) (s : Signing) : Signing := fun p => s p + polar c p.val

theorem spin_gauge (c : Lab) (s : Signing) {p : Lab} (hp : p∈points 4) :
    spin (gaugeSign c s) p = spin s p + polar c p := by simp [spin,gaugeSign,hp]

theorem gauge_preserves (c : Lab) (s : Signing) : violations (gaugeSign c s)=violations s := by
  apply (violations_eq_iff _ _).mpr
  intro p r hh
  obtain ⟨hp,hr,ht⟩ := mem_pairs.mp hh
  simp only [lineBit,spin_gauge c s hp,spin_gauge c s hr,spin_gauge c s ht,
    polar,cross_add,add_cross]
  ring_nf <;> simp [CharTwo.two_eq_zero]

theorem gauge_exhausts {s t : Signing} (he : violations s=violations t) :
    ∃ c, gaugeSign c s=t := by
  let h (p : Lab) := spin s p + spin t p
  have hg : Gauge h := by
    constructor
    · simp [h,spin,mem_points]
    · intro p r hh
      have eq := (violations_eq_iff _ _).mp he _ _ hh
      exact (by decide : ∀ a b c d e f z : Bit,
        a+b+c+z=d+e+f+z → c+f=a+d+(b+e)) _ _ _ _ _ _ _ eq
  obtain ⟨g, hg⟩ := gauge_extends hg
  obtain ⟨c,hc⟩ := label_dual g
  refine ⟨c,?_⟩
  funext p
  have hx := (hc p.val).symm.trans (hg _ p.property)
  change s p + polar c p.val=t p
  rw [hx]; simp [h,←add_assoc,CharTwo.add_self_eq_zero]

theorem axis_ne (i : Fin 4) : axis i ≠ 0 := by
  intro hh; have := congrFun hh i; simpa [axis] using this

theorem gauge_inj (s : Signing) : Function.Injective (fun c => gaugeSign c s) := by
  intro c d he
  have h (p : Lab) (hp : p ∈ points 4) : polar c p=polar d p :=
    add_left_cancel (congrFun he ⟨p,hp⟩)
  apply Prod.ext
  · funext i
    have hp : ((0,axis i) : Lab) ∈ points 4 := mem_points.mpr ⟨by simp [Prod.ext_iff,axis_ne],by simp [q]⟩
    simpa [polar,cross,dot_comm (axis i),dot_axis] using h _ hp
  · funext i
    have hp : ((axis i,0) : Lab) ∈ points 4 := mem_points.mpr ⟨by simp [Prod.ext_iff,axis_ne],by simp [q]⟩
    simpa [polar,cross,dot_axis] using h _ hp

noncomputable def configurations := (univ : Finset Opt).image fun o => violations o.val

theorem gauge_fiber_card (s : Opt) :
    (univ.filter (fun t : Opt => violations t.val = violations s.val)).card=256 := by
  classical
  let fibre := univ.filter (fun t : Opt => violations t.val=violations s.val)
  let f (c : Lab) : fibre := ⟨⟨gaugeSign c s.val,(congrArg Finset.card (gauge_preserves c s.val)).trans s.property⟩,
    by simp [fibre,gauge_preserves]⟩
  have inj : Function.Injective f := by
    intro c d he; exact gauge_inj s.val (congrArg (fun z : fibre => z.val.val) he)
  have surj : Function.Surjective f := by
    · intro t
      have ht : violations t.val.val=violations s.val := (mem_filter.mp t.property).2
      obtain ⟨c,hc⟩ := gauge_exhausts ht.symm
      exact ⟨c,Subtype.ext (Subtype.ext hc)⟩
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨inj,surj⟩)
  calc
    _ = Fintype.card fibre := (Fintype.card_coe _).symm
    _ = Fintype.card Lab := h.symm
    _ = 256 := by norm_num [Fintype.card_pi]

theorem gauge_counting : Fintype.card Opt = configurations.card*256 := by
  classical
  have h := card_eq_sum_card_image (fun s : Opt => violations s.val) (univ : Finset Opt)
  rw [card_univ] at h
  rw [h]
  apply sum_const_nat
  intro l hl
  obtain ⟨s,_,rfl⟩ := mem_image.mp hl
  exact gauge_fiber_card s

end Quadric.Four
