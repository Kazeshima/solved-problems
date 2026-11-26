import Quadric.Five.Forms
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range

namespace Quadric.Five.Certificates
open Small

structure Triangle where
  a : ℕ
  b : ℕ
  c : ℕ
  u : ℤ
  deriving DecidableEq, Repr

structure Cert where
  sigma : ℕ
  count : ℕ
  den : ℕ
  y : List ℤ
  tri : List Triangle
  boundNum : ℤ
  boundDen : ℕ
  floor : ℕ
  deriving Repr

def sign (b : Bool) : ℤ := if b then -1 else 1
@[simp] theorem sign_square (b : Bool) : sign b^2=1 := by cases b <;> norm_num [sign]

def edgeSpin (sig : ℕ) (s : ℕ→Bool) (e : ℕ×ℕ) :=
  graph sig e.1 e.2 * sign (s e.1) * sign (s e.2)

def score (sig : ℕ) (s : ℕ→Bool) := total edges (edgeSpin sig s)
def outsideErrors (sig : ℕ) (s : ℕ→Bool) :=
  edges.countP (fun e => edgeSpin sig s e == -1)

private theorem total_indicator {α : Type*} (xs : List α) (f : α→Bool) :
    total xs (fun i => ((f i).toNat : ℤ)) = xs.countP f := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h,ih,List.countP_cons,add_comm]

theorem score_eq (sig : ℕ) (s : ℕ→Bool) :
    score sig s=756-2*(outsideErrors sig s : ℤ) := by
  have term' (e : ℕ×ℕ) : edgeSpin sig s e =
      ((isEdge e.1 e.2).toNat:ℤ) - 2*((edgeSpin sig s e == -1).toNat : ℤ) := by
    unfold edgeSpin
    rw [graph_eq]
    generalize isEdge e.1 e.2=i
    generalize (negative 4 (outside[e.1]?.getD 0) (outside[e.2]?.getD 0) ^^
      sig.testBit (drop ((outside[e.1]?.getD 0) ^^^ (outside[e.2]?.getD 0))))=b
    cases i <;> cases b <;> cases s e.1 <;> cases s e.2 <;> decide
  rw [score,total_congr edges (fun e _ => term' e),total_sub,total_mul,
    total_indicator,total_indicator,edge_count]; rfl

def credit (t : Triangle) (e : ℕ×ℕ) : ℤ :=
  (if e=(t.a,t.b) then t.u else 0) + (if e=(t.a,t.c) then t.u else 0) +
    (if e=(t.b,t.c) then t.u else 0)

def validTri (sig : ℕ) (t : Triangle) : Prop :=
  0≤t.u ∧ t.a<t.b ∧ t.b<t.c ∧ t.c<56 ∧
  graph sig t.a t.b*graph sig t.a t.c*graph sig t.b t.c = -1 ∧
  ∀ a b c : Bool, graph sig t.a t.b*sign a*sign b+
    graph sig t.a t.c*sign a*sign c+graph sig t.b t.c*sign b*sign c ≤ 1
instance (sig : ℕ) (t : Triangle) : Decidable (validTri sig t) := by unfold validTri; infer_instance

private theorem first_mem {a b : ℕ} {xs : List ℕ} (h : (a,b) ∈ pairs xs) : a∈xs := by
  induction xs with
  | nil => simp [pairs] at h
  | cons k ks ih =>
    simp only [pairs,List.mem_append,List.mem_map] at h
    rcases h with ⟨v,_,hv⟩|ht
    · exact List.mem_cons.mpr (Or.inl (Prod.mk.inj hv).1.symm)
    · exact List.mem_cons.mpr (Or.inr (ih ht))

private theorem row_count (a b c : ℕ) (xs : List ℕ) :
    (xs.map fun x => (a,x)).count (b,c) = if a=b then xs.count c else 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases ha : a=b <;> by_cases hx : x=c <;> simp_all [List.count_cons]

private theorem pairs_once {a b : ℕ} (lt : a<b) (xs : List ℕ)
    (ord : xs.Pairwise (·<·)) (ha : a∈xs) (hb : b∈xs) : (pairs xs).count (a,b)=1 := by
  induction xs with
  | nil => simp at ha
  | cons k ks ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp ord
    rw [pairs,List.count_append,row_count]
    by_cases hk : k=a
    · subst k
      have hnot : a∉ks := fun h => (lt_irrefl a) (head _ h)
      have hn : (a,b)∉pairs ks := fun h => hnot (first_mem h)
      have hbk := (List.mem_cons.mp hb).resolve_left (Nat.ne_of_gt lt)
      simp [List.count_eq_zero.mpr hn,List.count_eq_one_of_mem (tail.imp (fun h => Nat.ne_of_lt h)) hbk]
    · have hak := (List.mem_cons.mp ha).resolve_left (Ne.symm hk)
      have hbk := (List.mem_cons.mp hb).resolve_left (Nat.ne_of_gt (Nat.lt_trans (head _ hak) lt))
      simp [hk,ih tail hak hbk]

private theorem count_edge {a b : ℕ} (hab : a<b) (hb : b<56) : edges.count (a,b)=1 :=
  pairs_once hab vertices List.pairwise_lt_range (List.mem_range.mpr (lt_trans hab hb)) (List.mem_range.mpr hb)

def diagonal (C : Cert) (i : ℕ) := 2*C.y[i]?.getD 0
def off (C : Cert) (i j : ℕ) :=
  (total C.tri (fun t => credit t (i,j))-2*(C.den:ℤ))*graph C.sigma i j
def matrix (C : Cert) := upper (diagonal C) (off C) vertices
def numerator (C : Cert) := total vertices (fun i => C.y[i]?.getD 0) + total C.tri (·.u)

private theorem marked (k : ℕ×ℕ) (u : ℤ) (f : ℕ×ℕ→ℤ) :
    total edges (fun e => (if e=k then u else 0)*f e) = edges.count k*u*f k := by
  calc
    _ = total edges (fun e => if e=k then u*f e else 0) :=
      total_congr _ fun e _ => by split_ifs <;> simp_all
    _ = _ := by rw [total_mark]; ac_rfl

theorem tri_bound (C : Cert) (s : ℕ→Bool) (t : Triangle) (ht : validTri C.sigma t) :
    total edges (fun e => credit t e*edgeSpin C.sigma s e) ≤ t.u := by
  obtain ⟨hu,hab,hbc,hc,_,h⟩ := ht
  simp only [credit,add_mul,total_add,marked,count_edge hab (lt_trans hbc hc),
    count_edge (lt_trans hab hbc) hc,count_edge hbc hc]
  simp only [Nat.cast_one,one_mul]
  have hh := mul_le_mul_of_nonneg_left (h (s t.a) (s t.b) (s t.c)) hu
  dsimp only [edgeSpin]
  linarith only [hh]

/-- A successful positive-pivot check and admissible triangle multipliers bound every signing
of the outside points. All matrix and certificate arithmetic is integral. -/
theorem completion_inequality (C : Cert) (s : ℕ→Bool)
    (hp : 0≤Schur.quad (matrix C) (vertices.map (fun i=>sign (s i))))
    (ht : ∀ t∈C.tri, validTri C.sigma t) :
    4*(C.den:ℤ)*(378-(outsideErrors C.sigma s : ℤ)) ≤ numerator C := by
  let X (i : ℕ) := sign (s i)
  have hn := hp
  change 0≤Schur.quad (matrix C) (vertices.map X) at hn
  rw [matrix,quad_upper] at hn
  have hd : total vertices (fun i => diagonal C i*(X i)^2) =
      2*total vertices (fun i => C.y[i]?.getD 0) := by simp [X,diagonal,total_mul]
  have terms (e : ℕ×ℕ) : off C e.1 e.2 * X e.1 * X e.2 =
      total C.tri (fun t => credit t e*edgeSpin C.sigma s e) -
        (2*C.den:ℤ)*edgeSpin C.sigma s e := by
    simp only [off,edgeSpin,X]
    rw [show total C.tri (fun t => credit t e*(graph C.sigma e.1 e.2*sign (s e.1)*sign (s e.2))) =
        (graph C.sigma e.1 e.2*sign (s e.1)*sign (s e.2))*total C.tri (fun t => credit t e) by
          rw [←total_mul]; exact total_congr _ fun _ _ => by ring]
    ring
  change 0≤total vertices (fun i => diagonal C i*(X i)^2)+
    2*total edges (fun e => off C e.1 e.2*X e.1*X e.2) at hn
  rw [hd,total_congr _ (fun e _ => terms e),total_sub,total_mul,total_comm] at hn
  have hb := total_le C.tri (fun t h => tri_bound C s t (ht t h))
  change total C.tri (fun t => total edges (fun e => credit t e*edgeSpin C.sigma s e)) ≤ _ at hb
  change 0≤2*total vertices (fun i => C.y[i]?.getD 0) +
    2*(total C.tri _-(2*C.den:ℤ)*score C.sigma s) at hn
  rw [score_eq] at hn
  unfold numerator
  nlinarith only [hn,hb]

def arithmeticOK (C : Cert) : Prop :=
  0<C.den ∧ C.y.length=56 ∧ 0<C.boundDen ∧
  numerator C*C.boundDen=C.boundNum*C.den ∧
  4*(C.den:ℤ)*(378-(C.floor:ℤ)) ≤ numerator C ∧
  numerator C < 4*(C.den:ℤ)*(379-(C.floor:ℤ)) ∧
  315≤C.count+C.floor ∧ C.count=errors full3 C.sigma.testBit ∧
  ∀ t∈C.tri,validTri C.sigma t

-- Finite list predicates use a structural Boolean fold, so no unbounded universal instance is needed.
def checkNumbers (C : Cert) : Bool :=
  decide (0<C.den ∧ C.y.length=56 ∧ 0<C.boundDen ∧
    numerator C*C.boundDen=C.boundNum*C.den ∧
    4*(C.den:ℤ)*(378-(C.floor:ℤ)) ≤ numerator C ∧
    numerator C < 4*(C.den:ℤ)*(379-(C.floor:ℤ)) ∧
    315≤C.count+C.floor ∧ C.count=errors full3 C.sigma.testBit) &&
    C.tri.all (fun t => decide (validTri C.sigma t))

theorem numbers_sound {C : Cert} (h : checkNumbers C=true) : arithmeticOK C := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨ha,hb,hc,hd,he,hf,hg,hh⟩ := of_decide_eq_true a
  exact ⟨ha,hb,hc,hd,he,hf,hg,hh,fun t ht => of_decide_eq_true (List.all_eq_true.mp b t ht)⟩

theorem certificate_bound (C : Cert) (hn : checkNumbers C=true)
    (s : ℕ→Bool) (hp : 0≤Schur.quad (matrix C) (vertices.map (fun i=>sign (s i)))) :
    315 ≤ errors full3 C.sigma.testBit + outsideErrors C.sigma s := by
  obtain ⟨hd,_,_,_,_,hceil,h315,hcount,htri⟩ := numbers_sound hn
  have h := completion_inequality C s hp htri
  have hfloor : C.floor≤outsideErrors C.sigma s := by
    by_contra! hx
    have hh : (outsideErrors C.sigma s : ℤ)+1≤C.floor := by exact_mod_cast hx
    have hd' : 0<(C.den:ℤ) := by exact_mod_cast hd
    nlinarith only [h,hceil,mul_nonneg (show (0:ℤ)≤C.den by omega) (sub_nonneg.mpr hh)]
  omega

theorem certificate_sound (C : Cert) (hn : checkNumbers C=true)
    (hp : Schur.check 56 1 (matrix C)=true) (s : ℕ→Bool) :
    315 ≤ errors full3 C.sigma.testBit + outsideErrors C.sigma s :=
  certificate_bound C hn s (Schur.sound 56 1 (matrix C) (by decide) hp _)

end Quadric.Five.Certificates
