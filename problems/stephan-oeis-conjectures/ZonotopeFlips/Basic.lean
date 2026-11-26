import Mathlib

/-!
# Consistent graphs: the combinatorial model of the higher Bruhat order `B(n, n-3)`

A graph on a finite set `S ⊂ ℕ` is stored as a set of ordered pairs `(x, y)` with `x < y`.
It is *consistent* when the neighbourhood of every vertex `p` is an initial or a final
segment of `S \ {p}`.  (This is Ziegler's consistency condition for subsets of
`C([n], n-2)`, written for the complementary 2-subsets.)

This file contains the model, vertex deletion / insertion, and the generic bijection
`card_del_eq` used for every counting step.
-/

open Finset

namespace ZonoFlips

open Classical

noncomputable section

abbrev Graph := Finset (ℕ × ℕ)

/-- Ordered pairs `x < y` of elements of `S`. -/
def pairs (S : Finset ℕ) : Finset (ℕ × ℕ) := (S ×ˢ S).filter fun p => p.1 < p.2

theorem mem_pairs {S : Finset ℕ} {x y : ℕ} : (x, y) ∈ pairs S ↔ x ∈ S ∧ y ∈ S ∧ x < y := by
  simp [pairs, and_assoc]

/-- All graphs on the vertex set `S`. -/
def graphs (S : Finset ℕ) : Finset Graph := (pairs S).powerset

theorem mem_graphs {S : Finset ℕ} {G : Graph} : G ∈ graphs S ↔ G ⊆ pairs S := by
  unfold graphs; exact mem_powerset

/-- Adjacency in a graph stored as ordered pairs. -/
def adj (G : Graph) (x y : ℕ) : Prop := (x, y) ∈ G ∨ (y, x) ∈ G

theorem adj_comm {G : Graph} {x y : ℕ} : adj G x y ↔ adj G y x := by
  unfold adj; exact or_comm

theorem adj_mem {S : Finset ℕ} {G : Graph} (hG : G ∈ graphs S) {x y : ℕ} (h : adj G x y) :
    x ∈ S ∧ y ∈ S ∧ x ≠ y := by
  rw [mem_graphs] at hG
  rcases h with h | h
  · have := mem_pairs.mp (hG h); exact ⟨this.1, this.2.1, by omega⟩
  · have := mem_pairs.mp (hG h); exact ⟨this.2.1, this.1, by omega⟩

theorem mem_iff_adj {S : Finset ℕ} {G : Graph} (hG : G ∈ graphs S) {x y : ℕ} (hxy : x < y) :
    (x, y) ∈ G ↔ adj G x y := by
  constructor
  · exact fun h => Or.inl h
  · rintro (h | h)
    · exact h
    · rw [mem_graphs] at hG
      have := mem_pairs.mp (hG h); omega

theorem graph_ext {S : Finset ℕ} {G G' : Graph} (hG : G ∈ graphs S) (hG' : G' ∈ graphs S)
    (h : ∀ x ∈ S, ∀ y ∈ S, x < y → (adj G x y ↔ adj G' x y)) : G = G' := by
  ext ⟨x, y⟩
  constructor
  · intro hm
    have hp := mem_pairs.mp ((mem_graphs.mp hG) hm)
    exact (mem_iff_adj hG' hp.2.2).mpr ((h x hp.1 y hp.2.1 hp.2.2).mp (Or.inl hm))
  · intro hm
    have hp := mem_pairs.mp ((mem_graphs.mp hG') hm)
    exact (mem_iff_adj hG hp.2.2).mpr ((h x hp.1 y hp.2.1 hp.2.2).mpr (Or.inl hm))

/-! ### Deleting and inserting a vertex -/

/-- Delete the vertex `w`. -/
def del (G : Graph) (w : ℕ) : Graph := G.filter fun p => p.1 ≠ w ∧ p.2 ≠ w

theorem adj_del {G : Graph} {w x y : ℕ} : adj (del G w) x y ↔ adj G x y ∧ x ≠ w ∧ y ≠ w := by
  unfold adj del
  simp only [mem_filter]
  tauto

theorem del_mem_graphs {S : Finset ℕ} {G : Graph} (hG : G ∈ graphs S) (w : ℕ) :
    del G w ∈ graphs (S.erase w) := by
  rw [mem_graphs] at hG ⊢
  rintro ⟨x, y⟩ h
  simp only [del, mem_filter] at h
  have := mem_pairs.mp (hG h.1)
  exact mem_pairs.mpr ⟨mem_erase.mpr ⟨h.2.1, this.1⟩, mem_erase.mpr ⟨h.2.2, this.2.1⟩, this.2.2⟩

/-- Insert the vertex `w`, joined to the vertices `q ∈ S \ {w}` with `ψ q`. -/
def ins (H : Graph) (S : Finset ℕ) (w : ℕ) (ψ : ℕ → Prop) : Graph :=
  H ∪ ((S.erase w).filter ψ).image fun q => if q < w then (q, w) else (w, q)

theorem mem_ins {H : Graph} {S : Finset ℕ} {w : ℕ} {ψ : ℕ → Prop} {x y : ℕ} :
    (x, y) ∈ ins H S w ψ ↔
      (x, y) ∈ H ∨ (y = w ∧ x ∈ S ∧ x < w ∧ ψ x) ∨ (x = w ∧ y ∈ S ∧ w < y ∧ ψ y) := by
  unfold ins
  simp only [mem_union, mem_image, mem_filter, mem_erase]
  constructor
  · rintro (h | ⟨q, ⟨⟨hqw, hqS⟩, hψ⟩, hq⟩)
    · exact Or.inl h
    · by_cases hlt : q < w
      · rw [if_pos hlt, Prod.mk.injEq] at hq
        rw [← hq.1, ← hq.2]
        exact Or.inr (Or.inl ⟨rfl, hqS, hlt, hψ⟩)
      · rw [if_neg hlt, Prod.mk.injEq] at hq
        rw [← hq.1, ← hq.2]
        exact Or.inr (Or.inr ⟨rfl, hqS, by omega, hψ⟩)
  · rintro (h | ⟨hy, hxS, hlt, hψ⟩ | ⟨hx, hyS, hlt, hψ⟩)
    · exact Or.inl h
    · refine Or.inr ⟨x, ⟨⟨by omega, hxS⟩, hψ⟩, ?_⟩
      rw [if_pos hlt, hy]
    · refine Or.inr ⟨y, ⟨⟨by omega, hyS⟩, hψ⟩, ?_⟩
      rw [if_neg (by omega), hx]

theorem adj_ins {H : Graph} {S : Finset ℕ} {w : ℕ} {ψ : ℕ → Prop} {x y : ℕ} :
    adj (ins H S w ψ) x y ↔
      adj H x y ∨ (x = w ∧ y ∈ S ∧ y ≠ w ∧ ψ y) ∨ (y = w ∧ x ∈ S ∧ x ≠ w ∧ ψ x) := by
  unfold adj
  rw [mem_ins, mem_ins]
  constructor
  · rintro ((h | ⟨hy, hxS, hlt, hψ⟩ | ⟨hx, hyS, hlt, hψ⟩) | (h | ⟨hy, hxS, hlt, hψ⟩ | ⟨hx, hyS, hlt, hψ⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr ⟨hy, hxS, by omega, hψ⟩)
    · exact Or.inr (Or.inl ⟨hx, hyS, by omega, hψ⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl ⟨hy, hxS, by omega, hψ⟩)
    · exact Or.inr (Or.inr ⟨hx, hyS, by omega, hψ⟩)
  · rintro ((h | h) | ⟨hx, hyS, hyw, hψ⟩ | ⟨hy, hxS, hxw, hψ⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · by_cases hlt : y < w
      · exact Or.inr (Or.inr (Or.inl ⟨hx, hyS, hlt, hψ⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨hx, hyS, by omega, hψ⟩))
    · by_cases hlt : x < w
      · exact Or.inl (Or.inr (Or.inl ⟨hy, hxS, hlt, hψ⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hy, hxS, by omega, hψ⟩))

theorem ins_mem_graphs {S : Finset ℕ} {H : Graph} {w : ℕ} (hw : w ∈ S)
    (hH : H ∈ graphs (S.erase w)) (ψ : ℕ → Prop) : ins H S w ψ ∈ graphs S := by
  rw [mem_graphs] at hH ⊢
  rintro ⟨x, y⟩ h
  rcases mem_ins.mp h with h | ⟨hy, hxS, hlt, _⟩ | ⟨hx, hyS, hlt, _⟩
  · have := mem_pairs.mp (hH h)
    exact mem_pairs.mpr ⟨(mem_erase.mp this.1).2, (mem_erase.mp this.2.1).2, this.2.2⟩
  · exact mem_pairs.mpr ⟨hxS, hy ▸ hw, by omega⟩
  · exact mem_pairs.mpr ⟨hx ▸ hw, hyS, by omega⟩

/-- The graphs on `S` with property `P` (one fixed decidability instance, so that families
defined in different places are syntactically comparable). -/
def sel (S : Finset ℕ) (P : Graph → Prop) : Finset Graph :=
  @Finset.filter _ P (fun _ => Classical.propDecidable _) (graphs S)

theorem mem_sel {S : Finset ℕ} {P : Graph → Prop} {G : Graph} :
    G ∈ sel S P ↔ G ∈ graphs S ∧ P G := by
  unfold sel; exact mem_filter

theorem sel_congr {S : Finset ℕ} {P Q : Graph → Prop} (h : ∀ G ∈ graphs S, (P G ↔ Q G)) :
    sel S P = sel S Q := by
  ext G
  rw [mem_sel, mem_sel]
  exact ⟨fun ⟨hG, hP⟩ => ⟨hG, (h G hG).mp hP⟩, fun ⟨hG, hQ⟩ => ⟨hG, (h G hG).mpr hQ⟩⟩

/-- Splitting a family along a condition and its negation. -/
theorem card_split {S : Finset ℕ} (P c1 c2 : Graph → Prop)
    (h : ∀ G ∈ graphs S, P G → (c2 G ↔ ¬ c1 G)) :
    (sel S P).card = (sel S fun G => P G ∧ c1 G).card + (sel S fun G => P G ∧ c2 G).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext G
    simp only [mem_union, mem_sel]
    constructor
    · rintro ⟨hG, hP⟩
      by_cases hc : c1 G
      · exact Or.inl ⟨hG, hP, hc⟩
      · exact Or.inr ⟨hG, hP, (h G hG hP).mpr hc⟩
    · rintro (⟨hG, hP, _⟩ | ⟨hG, hP, _⟩) <;> exact ⟨hG, hP⟩
  · rw [disjoint_left]
    intro G h1 h2
    have h1' := mem_sel.mp h1
    have h2' := mem_sel.mp h2
    exact (h G h1'.1 h1'.2.1).mp h2'.2.2 h1'.2.2

/-- The generic counting step: if in every graph with property `P` the neighbourhood of `w`
is forced to be `ψ`, deleting `w` lands in `Q`, and inserting `w` with neighbourhood `ψ`
into any graph with property `Q` gives a graph with property `P`, then the two families
are equinumerous. -/
theorem card_del_eq {S : Finset ℕ} {w : ℕ} (hw : w ∈ S) (P Q : Graph → Prop) (ψ : ℕ → Prop)
    (h1 : ∀ G ∈ graphs S, P G → Q (del G w) ∧ ∀ q ∈ S, q ≠ w → (adj G w q ↔ ψ q))
    (h2 : ∀ H ∈ graphs (S.erase w), Q H → P (ins H S w ψ)) :
    (sel S P).card = (sel (S.erase w) Q).card := by
  apply Finset.card_nbij' (fun G => del G w) (fun H => ins H S w ψ)
  · intro G hG
    have hG' := mem_sel.mp hG
    exact mem_sel.mpr ⟨del_mem_graphs hG'.1 w, (h1 G hG'.1 hG'.2).1⟩
  · intro H hH
    have hH' := mem_sel.mp hH
    exact mem_sel.mpr ⟨ins_mem_graphs hw hH'.1 ψ, h2 H hH'.1 hH'.2⟩
  · intro G hG
    have hG' := mem_sel.mp hG
    have hforced := (h1 G hG'.1 hG'.2).2
    apply graph_ext (ins_mem_graphs hw (del_mem_graphs hG'.1 w) ψ) hG'.1
    intro x hx y hy hxy
    rw [adj_ins, adj_del]
    constructor
    · rintro (⟨h, _, _⟩ | ⟨hxw, _, hyw, hψ⟩ | ⟨hyw, _, hxw, hψ⟩)
      · exact h
      · rw [hxw]; exact (hforced y hy hyw).mpr hψ
      · rw [hyw]; exact adj_comm.mp ((hforced x hx hxw).mpr hψ)
    · intro h
      by_cases hxw : x = w
      · have hyw : y ≠ w := by omega
        exact Or.inr (Or.inl ⟨hxw, hy, hyw, (hforced y hy hyw).mp (hxw ▸ h)⟩)
      · by_cases hyw : y = w
        · exact Or.inr (Or.inr ⟨hyw, hx, hxw, (hforced x hx hxw).mp (adj_comm.mp (hyw ▸ h))⟩)
        · exact Or.inl ⟨h, hxw, hyw⟩
  · intro H hH
    have hH' := mem_sel.mp hH
    apply graph_ext (del_mem_graphs (ins_mem_graphs hw hH'.1 ψ) w) hH'.1
    intro x hx y hy _
    rw [adj_del, adj_ins]
    have hxw := (mem_erase.mp hx).1
    have hyw := (mem_erase.mp hy).1
    constructor
    · rintro ⟨h | ⟨h, _⟩ | ⟨h, _⟩, _, _⟩
      · exact h
      · exact absurd h hxw
      · exact absurd h hyw
    · intro h
      exact ⟨Or.inl h, hxw, hyw⟩

/-! ### Rows: initial / final segments -/

/-- `a` is closed downwards on `S \ {p}`. -/
def DownP (S : Finset ℕ) (p : ℕ) (a : ℕ → Prop) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ p → y ≠ p → x < y → a y → a x

/-- `a` is closed upwards on `S \ {p}`. -/
def UpP (S : Finset ℕ) (p : ℕ) (a : ℕ → Prop) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ p → y ≠ p → x < y → a x → a y

/-- `a` cuts out an initial or a final segment of `S \ {p}`. -/
def MonoP (S : Finset ℕ) (p : ℕ) (a : ℕ → Prop) : Prop := DownP S p a ∨ UpP S p a

/-- Every neighbourhood is an initial or a final segment of the remaining vertices. -/
def Consistent (S : Finset ℕ) (G : Graph) : Prop := ∀ p ∈ S, MonoP S p (adj G p)

theorem MonoP.of_subset_congr {S S' : Finset ℕ} {p : ℕ} {a b : ℕ → Prop} (hsub : S' ⊆ S)
    (hc : ∀ q ∈ S', q ≠ p → (b q ↔ a q)) (h : MonoP S p a) : MonoP S' p b := by
  rcases h with h | h
  · left
    intro x hx y hy hxp hyp hxy hby
    exact (hc x hx hxp).mpr (h x (hsub hx) y (hsub hy) hxp hyp hxy ((hc y hy hyp).mp hby))
  · right
    intro x hx y hy hxp hyp hxy hbx
    exact (hc y hy hyp).mpr (h x (hsub hx) y (hsub hy) hxp hyp hxy ((hc x hx hxp).mp hbx))

theorem MonoP.congr {S : Finset ℕ} {p : ℕ} {a b : ℕ → Prop}
    (hc : ∀ q ∈ S, q ≠ p → (b q ↔ a q)) (h : MonoP S p a) : MonoP S p b :=
  h.of_subset_congr (Subset.refl S) hc

/-- No pattern `1 0 1` in a row. -/
theorem MonoP.no101 {S : Finset ℕ} {p : ℕ} {a : ℕ → Prop} (h : MonoP S p a) {x y z : ℕ}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxp : x ≠ p) (hyp : y ≠ p) (hzp : z ≠ p)
    (hxy : x < y) (hyz : y < z) (hax : a x) (haz : a z) : a y := by
  rcases h with h | h
  · exact h y hy z hz hyp hzp hyz haz
  · exact h x hx y hy hxp hyp hxy hax

/-- No pattern `0 1 0` in a row. -/
theorem MonoP.no010 {S : Finset ℕ} {p : ℕ} {a : ℕ → Prop} (h : MonoP S p a) {x y z : ℕ}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxp : x ≠ p) (hyp : y ≠ p) (hzp : z ≠ p)
    (hxy : x < y) (hyz : y < z) (hay : a y) : a x ∨ a z := by
  rcases h with h | h
  · exact Or.inl (h x hx y hy hxp hyp hxy hay)
  · exact Or.inr (h y hy z hz hyp hzp hyz hay)

/-- Inserting a new position `w` next to `t`, carrying the same value as `t`, keeps a row
monotone. -/
theorem monoP_clone {S : Finset ℕ} {p w t : ℕ} {a b : ℕ → Prop}
    (ht : t ∈ S) (htw : t ≠ w) (htp : t ≠ p)
    (hord : ∀ q ∈ S, q ≠ w → q ≠ t → (q < w ↔ q < t))
    (hb : ∀ q ∈ S, q ≠ w → (b q ↔ a q)) (hbw : b w ↔ a t)
    (h : MonoP (S.erase w) p a) : MonoP S p b := by
  have hte : t ∈ S.erase w := mem_erase.mpr ⟨htw, ht⟩
  rcases h with h | h
  · left
    intro x hx y hy hxp hyp hxy hby
    by_cases hxw : x = w
    · have hyw : y ≠ w := by omega
      rw [hxw, hbw]
      have hay : a y := (hb y hy hyw).mp hby
      by_cases hyt : y = t
      · rw [← hyt]; exact hay
      · have h1 := hord y hy hyw hyt
        exact h t hte y (mem_erase.mpr ⟨hyw, hy⟩) htp hyp (by omega) hay
    · rw [hb x hx hxw]
      by_cases hyw : y = w
      · have hat : a t := hbw.mp (hyw ▸ hby)
        by_cases hxt : x = t
        · rw [hxt]; exact hat
        · have h1 := hord x hx hxw hxt
          exact h x (mem_erase.mpr ⟨hxw, hx⟩) t hte hxp htp (by omega) hat
      · exact h x (mem_erase.mpr ⟨hxw, hx⟩) y (mem_erase.mpr ⟨hyw, hy⟩) hxp hyp hxy
          ((hb y hy hyw).mp hby)
  · right
    intro x hx y hy hxp hyp hxy hbx
    by_cases hyw : y = w
    · have hxw : x ≠ w := by omega
      rw [hyw, hbw]
      have hax : a x := (hb x hx hxw).mp hbx
      by_cases hxt : x = t
      · rw [← hxt]; exact hax
      · have h1 := hord x hx hxw hxt
        exact h x (mem_erase.mpr ⟨hxw, hx⟩) t hte hxp htp (by omega) hax
    · rw [hb y hy hyw]
      by_cases hxw : x = w
      · have hat : a t := hbw.mp (hxw ▸ hbx)
        by_cases hyt : y = t
        · rw [hyt]; exact hat
        · have h1 := hord y hy hyw hyt
          exact h t hte y (mem_erase.mpr ⟨hyw, hy⟩) htp hyp (by omega) hat
      · exact h x (mem_erase.mpr ⟨hxw, hx⟩) y (mem_erase.mpr ⟨hyw, hy⟩) hxp hyp hxy
          ((hb x hx hxw).mp hbx)

/-- A monotone row whose top entry is `1` is closed upwards. -/
theorem upP_of_top {S : Finset ℕ} {p m : ℕ} {a : ℕ → Prop} (hm : m ∈ S) (hmp : m ≠ p)
    (hmax : ∀ q ∈ S, q ≤ m) (ham : a m) (h : MonoP S p a) : UpP S p a := by
  rcases h with h | h
  · intro x _ y hy _ hyp _ _
    by_cases hym : y = m
    · rw [hym]; exact ham
    · exact h y hy m hm hyp hmp (by have := hmax y hy; omega) ham
  · exact h

/-- A monotone row whose bottom entry is `0` is closed upwards. -/
theorem upP_of_bot {S : Finset ℕ} {p m : ℕ} {a : ℕ → Prop} (hm : m ∈ S) (hmp : m ≠ p)
    (hmin : ∀ q ∈ S, m ≤ q) (ham : ¬ a m) (h : MonoP S p a) : UpP S p a := by
  rcases h with h | h
  · intro x hx y _ hxp _ _ hax
    exfalso
    by_cases hxm : x = m
    · exact ham (hxm ▸ hax)
    · exact ham (h m hm x hx hmp hxp (by have := hmin x hx; omega) hax)
  · exact h

/-- Putting a `0` in front of an upward closed row. -/
theorem upP_ins_min {S : Finset ℕ} {p w : ℕ} {a b : ℕ → Prop}
    (hmin : ∀ q ∈ S, q ≠ w → w < q) (hb : ∀ q ∈ S, q ≠ w → (b q ↔ a q)) (hbw : ¬ b w)
    (h : UpP (S.erase w) p a) : UpP S p b := by
  intro x hx y hy hxp hyp hxy hbx
  have hxw : x ≠ w := fun e => hbw (e ▸ hbx)
  have hyw : y ≠ w := by have := hmin x hx hxw; omega
  exact (hb y hy hyw).mpr (h x (mem_erase.mpr ⟨hxw, hx⟩) y (mem_erase.mpr ⟨hyw, hy⟩) hxp hyp hxy
    ((hb x hx hxw).mp hbx))

/-- Putting a `1` behind an upward closed row. -/
theorem upP_ins_max {S : Finset ℕ} {p w : ℕ} {a b : ℕ → Prop}
    (hmax : ∀ q ∈ S, q ≠ w → q < w) (hb : ∀ q ∈ S, q ≠ w → (b q ↔ a q)) (hbw : b w)
    (h : UpP (S.erase w) p a) : UpP S p b := by
  intro x hx y hy hxp hyp hxy hbx
  by_cases hyw : y = w
  · rw [hyw]; exact hbw
  · have hxw : x ≠ w := by have := hmax y hy hyw; omega
    exact (hb y hy hyw).mpr (h x (mem_erase.mpr ⟨hxw, hx⟩) y (mem_erase.mpr ⟨hyw, hy⟩) hxp hyp hxy
      ((hb x hx hxw).mp hbx))

end

end ZonoFlips
