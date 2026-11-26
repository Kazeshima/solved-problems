import Quadric.Five.BasePoints

namespace Quadric.Five
open Finset

private theorem bit_one {b : Bit} (h : b≠0) : b=1 := (by decide : ∀ z:Bit,z≠0 → z=1) b h
@[simp] theorem form_zero {n} (c : Label n) : form c 0=0 := by simp [form,q,polar,cross]
@[simp] theorem zero_form {n} (p : Label n) : form 0 p=q p := by simp [form,polar,cross]

private theorem single_hop {n} (c p r : Label n) (hp : form c p=1) (hr : form c r=1)
    (h : polar p r=1) :
    ∃ A : Morph n n, A.f p=r ∧ ∀x,form c (A.f x)=form c x := by
  have ha : form c (p+r)=1 := by rw [form_add,hp,hr,h]; decide
  refine ⟨transvection (p+r),swap_value h,fun x=>?_⟩
  change form c (toggle (p+r) x)=_
  rw [form_toggle,ha,show (1:Bit)+1=0 by decide,mul_zero,add_zero]

theorem centre_transitive {n} (hn : 4<dim n) (c p r : Label n) (hp : form c p=1)
    (hr : form c r=1) : ∃ A : Morph n n, A.f p=r ∧ ∀x,form c (A.f x)=form c x := by
  classical
  by_cases he : p=r
  · subst r; exact ⟨Morph.id _,rfl,fun _=>rfl⟩
  by_cases hpr : polar p r=0
  · have nz (z:Label n) (h:form c z=1) : z≠0 := by rintro rfl; simp at h
    have cc:=cover_card c p r (nz p hp) (nz r hr) (mt (add_eq_zero_iff_same _ _).mp he) hpr
    have hpos : 0<((centres c).filter fun z => coversPoint c z p ∧ coversPoint c z r).card := by
      apply Nat.pos_of_ne_zero; intro hh
      rw [hh] at cc
      by_cases hc : q c=0 <;> simp [chi,hc] at cc <;>
        nlinarith [mul_pos (sub_pos.mpr hn) (show 0<dim n by linarith)]
    obtain ⟨z,hz⟩ := card_pos.mp hpos
    obtain ⟨hc,ha,hb⟩ := mem_filter.mp hz
    have hz1 : form c z=1 := bit_one (mem_filter.mp hc).2
    obtain ⟨A,hA,pa⟩ := single_hop c p z hp hz1 (ha.trans hp)
    obtain ⟨B,hB,pb⟩ := single_hop c z r hz1 hr ((polar_comm z r).trans (hb.trans hr))
    exact ⟨A.thenMap B,by change B.f (A.f p)=r; rw [hA,hB],fun x=> (pb _).trans (pa x)⟩
  · exact single_hop c p r hp hr (bit_one hpr)

theorem map_quad {n} {c : Label n} (A : Morph n n)
    (h : ∀x,form c (A.f x)=form c x) {x : Label n} (hx : x∈quadric c) : A.f x∈quadric c := by
  simp only [quadric,allPoints,mem_filter,mem_erase,mem_univ,and_true] at hx ⊢
  exact ⟨A.nonzero hx.1,(h _).trans hx.2⟩

theorem map_slice {n} {c p r : Label n} (A : Morph n n)
    (h : ∀x,form c (A.f x)=form c x) (hp : A.f p=r)
    {x : Label n} (hx : x∈slice (quadric c) c p) : A.f x∈slice (quadric c) c r := by
  obtain ⟨hq,hm⟩ := mem_filter.mp hx
  apply mem_filter.mpr
  refine ⟨map_quad A h hq,?_⟩
  change polar (A.f x) r=form c (A.f x)
  rw [←hp,A.sympl,h]; exact hm

theorem base_section {n} {k : ℕ} (h : AtLeast (allPoints n) k) :
    AtLeast (slice (quadric (0:Label (n+1))) 0 (pole n)) k := by
  apply (sectionMap n).transports _ h
  intro x hx
  have hx0 : x≠0 := (mem_erase.mp hx).1
  apply mem_filter.mpr
  change extend x ∈ quadric 0 ∧ coversPoint 0 (pole n) (extend x)
  rw [zero_quadric,mem_points]
  exact ⟨⟨(sectionMap n).nonzero hx0,extend_q x⟩,
    by simp [coversPoint,polar_comm (extend x),extend_q]⟩

attribute [local irreducible] degree faults
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

section FiveTransport
attribute [local irreducible] points quadric slice allPoints centres

theorem five_from_full_four (h : AtLeast (allPoints 4) 1575) : 6975≤degree 5 := by
  apply five_from_sections
  intro t ht
  have ht1 : form 0 t=1 := by unfold centres at ht; exact bit_one (mem_filter.mp ht).2
  obtain ⟨A,ha,hi⟩ := centre_transitive (by norm_num [dim] : 4<dim 5) 0 (pole 4) t
    (by rw [zero_form,pole_q]) ht1
  have H0 : AtLeast (slice (quadric (0:Label 5)) 0 (pole 4)) 1575 := by
    exact @base_section 4 1575 h
  have tr := A.transports (S:=slice (quadric 0) 0 (pole 4)) (T:=slice (quadric 0) 0 t)
    (fun x hx=>@map_slice 5 0 (pole 4) t A hi ha x hx) H0
  simpa only [zero_quadric] using tr
end FiveTransport

theorem one_elliptic_suffices (h : AtLeast (quadric ellipticBase) 315) :
    AtLeast (allPoints 4) 1575 := by
  apply four_from_elliptics
  intro a ha
  have hqa : q a=1 := by simpa using bit_one (mem_filter.mp ha).2
  let t := ellipticBase+a
  have ht : form a t=0 := by
    simp only [t,form,q_add,polar_add_right,elliptic_type,hqa]
    rw [polar_comm a ellipticBase,show polar a a=0 from CharTwo.add_self_eq_zero _]
    abel_nf; simp [CharTwo.two_eq_zero,CharTwo.two_nsmul]
  apply (transvection t).transports _ h
  intro x hx
  obtain ⟨hx0,hf⟩ := mem_filter.mp hx
  refine mem_filter.mpr ⟨mem_erase.mpr ⟨(transvection t).nonzero (mem_erase.mp hx0).1,mem_univ _⟩,?_⟩
  change form a (toggle t x)=0
  rw [form_toggle,ht,zero_add,mul_one]
  unfold t form at *; rw [polar_add_left]
  linear_combination (norm:=ring_nf <;> simp [CharTwo.two_eq_zero]) hf

theorem elliptic_reduction
    (H : ∀ s : Signing 4, (faults (slice (quadric ellipticBase) ellipticBase sectionBase) s).card<558 →
      1890≤(faults (quadric ellipticBase) s).card) : AtLeast (quadric ellipticBase) 315 := by
  classical
  intro s
  change 1890 ≤ (faults (quadric ellipticBase) s).card
  by_contra! bad
  obtain ⟨t,ht,hcheap⟩ : ∃ t∈centres ellipticBase,
      (faults (slice (quadric ellipticBase) ellipticBase t) s).card<558 := by
    by_contra! hh
    have bound:=slice_bound (quadric ellipticBase) ellipticBase (by simp [quadric,allPoints]) s 558 40
      (by norm_num [dim,elliptic_type,chi_one]) hh
    have hc:=centres_card ellipticBase
    norm_num [dim,elliptic_type,chi_one] at hc
    have hc' : (centres ellipticBase).card=136 := by exact_mod_cast (by linarith : ((centres ellipticBase).card:ℝ)=136)
    rw [hc'] at bound; omega
  obtain ⟨A,hp,hq⟩ := centre_transitive (by norm_num [dim] : 4<dim 4) ellipticBase
    sectionBase t sectionBase_off (bit_one (mem_filter.mp ht).2)
  have low := A.comparison (S:=slice (quadric ellipticBase) ellipticBase sectionBase)
    (T:=slice (quadric ellipticBase) ellipticBase t) (fun _ hx=>map_slice A hq hp hx) s
  have all := A.comparison (S:=quadric ellipticBase) (T:=quadric ellipticBase)
    (fun _ hx=>map_quad A hq hx) s
  have hien := H (A.pull s) (lt_of_le_of_lt low hcheap)
  omega

theorem exact_of_elliptic_base
    (h : AtLeast (quadric ellipticBase) 315) : degree 5=6975 :=
  le_antisymm witness_upper (five_from_full_four (one_elliptic_suffices h))

end Quadric.Five
