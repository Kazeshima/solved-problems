import Quadric.Five.Certificates

namespace Quadric.Five.Certificates
open Small

/-- An integer Gram decomposition of a positive multiple of the submitted certificate matrix,
up to a small symmetric residual. -/
structure Factor where
  scale : ℕ
  rows : List (List ℤ)
  residue : List (List ℤ)
  deriving Repr

def atRow (m : List (List ℤ)) (i : ℕ) := m[i]?.getD []
def entry (m : List (List ℤ)) (i j : ℕ) := (atRow m i)[j]?.getD 0
def dotRow (F : Factor) (i j : ℕ) := Schur.dot (atRow F.rows i) (atRow F.rows j)
def gram (F : Factor) (i j : ℕ) :=
  total vertices (fun k => entry F.rows i k * entry F.rows j k)
def errWeight (F : Factor) :=
  2*total edges (fun e => |entry F.residue e.1 e.2|)

def Q (d : ℕ→ℤ) (g : ℕ→ℕ→ℤ) (x : ℕ→ℤ) :=
  total vertices (fun i => d i*x i^2)+2*total edges (fun e => g e.1 e.2*x e.1*x e.2)

theorem pair_members {α : Type*} {xs : List α} {e : α×α} (h : e∈pairs xs) :
    e.1∈xs ∧ e.2∈xs := by
  induction xs with
  | nil => simp [pairs] at h
  | cons i is ih =>
    rcases List.mem_append.mp h with h|h
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h; simp [hj]
    · obtain ⟨ha,hb⟩ := ih h; simp [ha,hb]

theorem ordered_edge {a b : ℕ} (h : (a,b)∈edges) : a<b := by
  have aux (xs : List ℕ) (hs : xs.Pairwise (·<·)) (h : (a,b)∈pairs xs) : a<b := by
    induction xs with
    | nil => simp [pairs] at h
    | cons i is ih =>
      rcases List.mem_append.mp h with h|h
      · obtain ⟨j,hj,hp⟩ := List.mem_map.mp h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
        exact (List.pairwise_cons.mp hs).1 _ hj
      · exact ih (List.pairwise_cons.mp hs).2 h
  exact aux vertices List.pairwise_lt_range h

theorem total_nonneg {α : Type*} (xs : List α) (f : α→ℤ) (h : ∀ i∈xs,0≤f i) :
    0≤total xs f := by
  rw [←total_zero xs]; exact total_le _ h

theorem le_total {α : Type*} (xs : List α) (f : α→ℤ) (hp : ∀ i,0≤f i)
    {i : α} (hi : i∈xs) : f i≤total xs f := by
  induction xs with
  | nil => simp at hi
  | cons a as ih =>
    rw [total_cons]
    rcases List.mem_cons.mp hi with rfl|hi
    · linarith only [total_nonneg as f (fun j _=>hp j)]
    · linarith only [ih hi,hp a]

theorem square_total {α : Type*} (xs : List α) (f : α→ℤ) :
    (total xs f)^2 = total xs (fun i => (f i)^2) +
      2*total (pairs xs) (fun e => f e.1*f e.2) := by
  induction xs with
  | nil => simp [pairs]
  | cons a as ih =>
    simp only [total_cons,pairs,total_append,total_map,total_mul]
    linear_combination ih

theorem gram_identity (F : Factor) (x : ℕ→ℤ) : Q (fun i=>gram F i i) (gram F) x =
    total vertices (fun k => (total vertices (fun i => entry F.rows i k*x i))^2) := by
  simp_rw [square_total]
  rw [total_add,total_mul]
  unfold Q gram
  congr 1
  · rw [total_comm vertices vertices (fun k i => (entry F.rows i k*x i)^2)]
    apply total_congr; intro i _
    rw [mul_comm,←total_mul]
    exact total_congr _ (fun k _=>by ring)
  · congr 1
    rw [total_comm vertices (pairs vertices) (fun k e =>
      entry F.rows e.1 k*x e.1 * (entry F.rows e.2 k*x e.2))]
    apply total_congr; intro e _
    rw [mul_assoc,mul_comm,←total_mul]
    exact total_congr _ (fun k _=>by ring)

private theorem row_eta (r : List ℤ) (h : r.length=56) :
    vertices.map (fun i=>r[i]?.getD 0) = r := by
  apply List.ext_getElem
  · simp [vertices,h]
  · intro i hi hj
    simp [vertices,List.getElem?_eq_getElem hj]

theorem dotRow_eq (F : Factor) {i j : ℕ}
    (hi : (atRow F.rows i).length=56) (hj : (atRow F.rows j).length=56) :
    dotRow F i j=gram F i j := by
  unfold dotRow gram entry
  conv_lhs => rw [←row_eta _ hi,←row_eta _ hj]
  rw [dot_map]

def cellOK (C : Cert) (F : Factor) (i j : ℕ) : Bool :=
  (F.scale:ℤ)*(if i=j then diagonal C i else off C i j) ==
      dotRow F i j+entry F.residue i j

def rowValid (C : Cert) (F : Factor) (i : ℕ) : Bool :=
  (atRow F.rows i).length==56 && errWeight F < entry F.residue i i &&
  vertices.all fun j => i>j || cellOK C F i j

theorem gram_positive (C : Cert) (F : Factor) (hscale : 0<F.scale)
    (hc : ∀i∈vertices,rowValid C F i=true) (x : ℕ→ℤ) :
    0 ≤ Schur.quad (matrix C) (vertices.map x) := by
  have shape (i) (hi : i∈vertices) : (atRow F.rows i).length=56 :=
    eq_of_beq (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hc i hi)).1).1
  have diag (i) (hi : i∈vertices) : (F.scale:ℤ)*diagonal C i =
      gram F i i + entry F.residue i i := by
    have he := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (hc i hi)).2 i hi
    simpa [cellOK,dotRow_eq F (shape _ hi) (shape _ hi)] using he
  have offeq (e : ℕ×ℕ) (he : e∈edges) : (F.scale:ℤ)*off C e.1 e.2 =
      gram F e.1 e.2+entry F.residue e.1 e.2 := by
    obtain ⟨hi,hj⟩ := pair_members he
    have hlt := ordered_edge he
    have hh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (hc e.1 hi)).2 e.2 hj
    simpa [cellOK,not_lt_of_ge hlt.le,hlt.ne,dotRow_eq F (shape _ hi) (shape _ hj)] using hh
  let E := total vertices (fun i=>x i^2)
  have en : 0≤E := total_nonneg _ _ fun _ _ => sq_nonneg _
  have hd : errWeight F*E ≤ total vertices (fun i=>entry F.residue i i*x i^2) := by
    rw [show errWeight F*E = total vertices (fun i=>errWeight F*x i^2) from (total_mul ..).symm]
    apply total_le; intro i hi
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hc i hi)).1).2).le
  have ho : -(errWeight F*E) ≤ 2*total edges (fun e=>entry F.residue e.1 e.2*x e.1*x e.2) := by
    have hh := total_le edges (f:=fun e => (-2*E)*|entry F.residue e.1 e.2|)
      (g:=fun e => 2*(entry F.residue e.1 e.2*x e.1*x e.2)) (fun e he => by
        obtain ⟨hi,hj⟩ := pair_members he
        have h1 : x e.1^2 ≤ E := le_total vertices _ (fun _=>sq_nonneg _) hi
        have h2 : x e.2^2 ≤ E := le_total vertices _ (fun _=>sq_nonneg _) hj
        let z := entry F.residue e.1 e.2
        change (-2*E)*|z|≤2*(z*x e.1*x e.2)
        by_cases hz : 0≤z
        · rw [abs_of_nonneg hz]; nlinarith only [mul_nonneg hz (sq_nonneg (x e.1+x e.2)),
            mul_nonneg hz (sub_nonneg.mpr h1),mul_nonneg hz (sub_nonneg.mpr h2)]
        · rw [abs_of_neg (lt_of_not_ge hz)]
          have hn := neg_nonneg.mpr (le_of_not_ge hz)
          nlinarith only [mul_nonneg hn (sq_nonneg (x e.1-x e.2)),
            mul_nonneg hn (sub_nonneg.mpr h1),mul_nonneg hn (sub_nonneg.mpr h2)])
    rw [total_mul,total_mul] at hh; unfold errWeight; linarith only [hh]
  have hG : 0≤Q (fun i=>gram F i i) (gram F) x := by
    rw [gram_identity]; exact total_nonneg _ _ fun _ _=>sq_nonneg _
  have hd' := total_congr vertices (f:=fun i=>(F.scale:ℤ)*(diagonal C i*x i^2))
    (g:=fun i=>gram F i i*x i^2 + entry F.residue i i*x i^2)
    (fun i hi => by dsimp only; linear_combination (x i)^2 * diag i hi)
  have ht' := total_congr edges (f:=fun e=>(F.scale:ℤ)*(off C e.1 e.2*x e.1*x e.2))
    (g:=fun e=>gram F e.1 e.2*x e.1*x e.2+entry F.residue e.1 e.2*x e.1*x e.2)
    (fun e he=> by dsimp only; linear_combination (x e.1*x e.2) * offeq e he)
  rw [total_mul,total_add] at hd' ht'
  rw [matrix,quad_upper]
  change 0≤total vertices (fun i=>diagonal C i*x i^2)+2*total edges (fun e=>off C e.1 e.2*x e.1*x e.2)
  apply nonneg_of_mul_nonneg_right (a:=(F.scale:ℤ)) _ (by exact_mod_cast hscale)
  unfold Q at hG
  linarith only [hG,hd,ho,hd',ht']

def RowSpan (C : Cert) (F : Factor) : ℕ → ℕ → Prop
  | _,0 => True
  | i,n+1 => rowValid C F i=true ∧ RowSpan C F (i+1) n

theorem at_span (C : Cert) (F : Factor) (i n j : ℕ) (h : RowSpan C F i n) (hj : j<n) :
    rowValid C F (i+j)=true := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simpa using h.1
    | succ j => simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (i+1) j h.2 (by omega)

theorem rows_valid (C : Cert) (F : Factor) (h : RowSpan C F 0 56) :
    ∀ i∈vertices,rowValid C F i=true := by
  intro i hi; simpa using at_span C F 0 56 i h (List.mem_range.mp hi)

end Quadric.Five.Certificates
