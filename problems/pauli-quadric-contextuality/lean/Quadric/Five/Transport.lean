import Quadric.Five.Models
import Quadric.Gates

namespace Quadric.Five
open Finset
open scoped BigOperators
attribute [local irreducible] points pairs lines bad

structure Morph (n m : ℕ) where
  f : Label n → Label m
  inj : Function.Injective f
  zero : f 0=0
  sympl (x y) : polar (f x) (f y)=polar x y
  add (x y) (h : polar x y=0) : f (x+y)=f x+f y
  phase : Label n→Bit
  law (x y) (h : polar x y=0) :
    herm x y+phase (x+y)=phase x+phase y+herm (f x) (f y)

namespace Morph
variable {n m k : ℕ}
def id (n : ℕ) : Morph n n where
  f:=fun x=>x
  inj:=fun _ _ h=>h
  zero:=rfl
  sympl _ _:=rfl
  add _ _ _:=rfl
  phase _:=0
  law _ _ _:=by simp

def thenMap (A : Morph n m) (B : Morph m k) : Morph n k where
  f:=fun x=>B.f (A.f x)
  inj:=B.inj.comp A.inj
  zero:=by rw [A.zero,B.zero]
  sympl _ _:=by rw [B.sympl,A.sympl]
  add x y h:=by rw [A.add _ _ h,B.add _ _ ((A.sympl _ _).trans h)]
  phase x:=A.phase x+B.phase (A.f x)
  law x y h:=by
    rw [A.add _ _ h]
    have a:=A.law _ _ h
    have b:=B.law _ _ ((A.sympl _ _).trans h)
    linear_combination a+b

def pull (A : Morph n m) (s : Signing m) : Signing n :=
  fun x => s (A.f x)+A.phase x

theorem pull_bit (A : Morph n m) (s : Signing m) {p r : Label n} (h : polar p r=0) :
    bitScore (A.pull s) p r=bitScore s (A.f p) (A.f r) := by
  simp only [pull,bitScore,A.add _ _ h]
  have he:=A.law _ _ h
  linear_combination (norm := ring_nf <;> simp [CharTwo.two_eq_zero]) he

theorem comparison (A : Morph n m) {S : Finset (Label n)} {T : Finset (Label m)}
    (ha : ∀ x∈S,A.f x∈T) (s : Signing m) :
    (faults S (A.pull s)).card≤(faults T s).card := by
  apply card_le_card_of_injOn (fun z => (A.f z.1,A.f z.2))
  · rintro ⟨p,r⟩ hz
    obtain ⟨hh,hv⟩ := mem_faults.mp hz
    obtain ⟨hp,hr,ht,hpr⟩ := mem_contexts.mp hh
    apply mem_faults.mpr
    refine ⟨mem_contexts.mpr ⟨ha _ hp,ha _ hr,?_,(A.sympl _ _).trans hpr⟩,?_⟩
    · rw [←A.add _ _ hpr]; exact ha _ ht
    · rwa [←A.pull_bit s hpr]
  · rintro ⟨p,r⟩ _ ⟨t,u⟩ _ he
    exact Prod.ext (A.inj (Prod.mk.inj he).1) (A.inj (Prod.mk.inj he).2)

theorem transports (A : Morph n m) {S : Finset (Label n)} {T : Finset (Label m)}
    (ha : ∀ x∈S,A.f x∈T) {d : ℕ} (h : AtLeast S d) : AtLeast T d :=
  fun s => (h (A.pull s)).trans (A.comparison ha s)

theorem nonzero (A : Morph n m) {x : Label n} (hx : x≠0) : A.f x≠0 := by
  intro h; exact hx (A.inj (h.trans A.zero.symm))
end Morph

theorem dot_cons {n} (a b : Bit) (x y : Word n) :
    dot (Fin.cons a x) (Fin.cons b y)=a*b+dot x y := by simp [dot,Fin.sum_univ_succ]

def extend {n} (p : Label n) : Label (n+1) :=
  (Fin.cons (q p) p.1, Fin.cons (q p) p.2)
def pole (n : ℕ) : Label (n+1) := (Fin.cons 1 0, Fin.cons 1 0)

theorem extend_inj (n : ℕ) : Function.Injective (@extend n) := by
  intro p r h
  have a:=congrArg Prod.fst h
  have b:=congrArg Prod.snd h
  exact Prod.ext (funext (fun i => by simpa [extend] using congrFun a i.succ))
    (funext (fun i => by simpa [extend] using congrFun b i.succ))

theorem extend_zero (n : ℕ) : extend (0:Label n)=0 := by
  apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [extend,q]

theorem extend_q {n} (x : Label n) : q (extend x)=0 := by
  change dot (Fin.cons (q x) x.1) (Fin.cons (q x) x.2)=0
  rw [dot_cons]; exact (by decide : ∀ b : Bit, b*b+b=0) _
theorem pole_q (n : ℕ) : q (pole n)=1 := by simp [q,pole,dot_cons]

theorem extend_cross {n} (p r : Label n) : cross (extend p) (extend r) = herm p r := by
  simp [cross,extend,herm,dot_cons,add_comm]

theorem extend_polar {n} (p r : Label n) : polar (extend p) (extend r)=polar p r := by
  simp only [polar,extend_cross,herm]; ring_nf <;> simp [CharTwo.two_eq_zero]
@[simp] theorem pole_perp {n} (p : Label n) : polar (pole n) (extend p)=0 := by
  simp [polar,pole,extend,cross,dot_cons,CharTwo.add_self_eq_zero]

theorem extend_add {n} (p r : Label n) (h : polar p r=0) : extend (p+r)=extend p+extend r := by
  apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j=>?_) i <;>
    simp [extend,q_add,h]

def sectionMap (n : ℕ) : Morph n (n+1) where
  f:=extend
  inj:=extend_inj _
  zero:=extend_zero _
  sympl:=extend_polar
  add:=extend_add
  phase _:=0
  law p r _:=by simp [herm,extend_q,extend_cross]

def toggle {n} (a p : Label n) := Clifford.turnLabel a p
theorem trans_q {n} (a : Label n) : q (extend a+pole n)=1 := by
  simp [q_add,extend_q,pole_q,polar_comm (extend a)]

noncomputable def carrierRotation {n} (a : Label n) :=
  Clifford.rotation (extend a+pole n) (trans_q a)

theorem rotation_extend {n} (a p : Label n) :
    (carrierRotation a).perm (extend p)=extend (toggle a p) := by
  change Clifford.turnLabel (extend a+pole n) (extend p)=_
  unfold toggle Clifford.turnLabel
  simp only [polar_add_left,extend_polar,pole_perp,add_zero]
  split_ifs with h
  · rfl
  · have h1 : polar a p=1 := (by decide : ∀ b : Bit,b≠0 → b=1) _ h
    apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j=>?_) i <;>
      simp [extend,pole,q_add,h1,add_assoc,add_comm,add_left_comm]

theorem cliff_polar {n} (C : Clifford n) (x y : Label n) :
    polar (C.perm x) (C.perm y)=polar x y := by
  have h:=C.map_q (x+y)
  simp only [C.map_add,q_add,C.map_q] at h
  exact add_left_cancel h

noncomputable def transvection {n} (a : Label n) : Morph n n where
  f:=toggle a
  inj:=(Clifford.turn_involution a).injective
  zero:=by simp [toggle,Clifford.turnLabel,polar,cross]
  sympl x y:=by rw [←extend_polar,←rotation_extend,←rotation_extend,cliff_polar,extend_polar]
  add x y h:=by
    apply extend_inj n
    have hs : polar (toggle a x) (toggle a y)=0 := by
      rw [←extend_polar,←rotation_extend,←rotation_extend,cliff_polar,extend_polar,h]
    rw [←rotation_extend,extend_add _ _ h,Clifford.map_add,extend_add _ _ hs,
      rotation_extend,rotation_extend]
  phase x:=(carrierRotation a).phase (extend x)
  law x y h:=by
    have he:=((carrierRotation a).cocycle (extend x) (extend y)).2
    simpa only [extend_cross,←extend_add x y h,rotation_extend] using he

theorem form_toggle {n} (c a p : Label n) :
    form c (toggle a p)=form c p+polar a p*(form c a+1) := by
  unfold toggle Clifford.turnLabel
  by_cases he : polar a p=0
  · simp [he]
  · have h1 : polar a p=1 := (by decide : ∀ b : Bit,b≠0 → b=1) _ he
    simp [he,h1,form_add,add_comm,add_assoc,add_left_comm]

theorem swap_value {n} {p r : Label n} (hp : polar p r=1) : toggle (p+r) p=r := by
  have h0 : polar p p=0 := CharTwo.add_self_eq_zero _
  have hs : polar (p+r) p=1 := by rw [polar_add_left,polar_comm r p,hp,h0,zero_add]
  simp [toggle,Clifford.turnLabel,hs,add_comm,add_left_comm,add_assoc] <;> abel_nf <;> simp

end Quadric.Five
