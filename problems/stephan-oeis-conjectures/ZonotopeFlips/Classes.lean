import ZonotopeFlips.Basic

/-!
# Classes of consistent graphs with two prescribed rows

`Cls S i j φi φj G` says: `G` is consistent on `S`, the neighbourhood of `i` is cut out by
`φi` and that of `j` by `φj`.  The four kinds of flips at a pair `i < j` are four such classes.
`cls_del_card` is the deletion bijection for these classes.
-/

open Finset

namespace ZonoFlips

open Classical

noncomputable section

structure Cls (S : Finset ℕ) (i j : ℕ) (φi φj : ℕ → Prop) (G : Graph) : Prop where
  cons : Consistent S G
  rowi : ∀ q ∈ S, (adj G i q ↔ φi q)
  rowj : ∀ q ∈ S, (adj G j q ↔ φj q)

/-- The finite set of graphs of a class. -/
def clsSet (S : Finset ℕ) (i j : ℕ) (φi φj : ℕ → Prop) : Finset Graph :=
  sel S (Cls S i j φi φj)

theorem mem_clsSet {S : Finset ℕ} {i j : ℕ} {φi φj : ℕ → Prop} {G : Graph} :
    G ∈ clsSet S i j φi φj ↔ G ∈ graphs S ∧ Cls S i j φi φj G := by
  unfold clsSet; exact mem_sel

theorem Consistent.del {S : Finset ℕ} {G : Graph} (h : Consistent S G) (w : ℕ) :
    Consistent (S.erase w) (del G w) := by
  intro p hp
  have hpw := (mem_erase.mp hp).1
  refine (h p (mem_erase.mp hp).2).of_subset_congr (erase_subset w S) ?_
  intro q hq _
  rw [adj_del]
  have := (mem_erase.mp hq).1
  exact ⟨fun h => h.1, fun h => ⟨h, hpw, this⟩⟩

theorem Cls.del {S : Finset ℕ} {i j : ℕ} {φi φj : ℕ → Prop} {G : Graph}
    (h : Cls S i j φi φj G) {w : ℕ} (hwi : w ≠ i) (hwj : w ≠ j) :
    Cls (S.erase w) i j φi φj (del G w) := by
  refine ⟨h.cons.del w, ?_, ?_⟩
  · intro q hq
    rw [adj_del, ← h.rowi q (mem_erase.mp hq).2]
    have := (mem_erase.mp hq).1
    exact ⟨fun h => h.1, fun h => ⟨h, Ne.symm hwi, this⟩⟩
  · intro q hq
    rw [adj_del, ← h.rowj q (mem_erase.mp hq).2]
    have := (mem_erase.mp hq).1
    exact ⟨fun h => h.1, fun h => ⟨h, Ne.symm hwj, this⟩⟩

/-! ### Adjacency in an inserted graph -/

theorem adj_ins_of_ne {H : Graph} {S : Finset ℕ} {w : ℕ} {ψ : ℕ → Prop} {p q : ℕ}
    (hpw : p ≠ w) (hqw : q ≠ w) : adj (ins H S w ψ) p q ↔ adj H p q := by
  rw [adj_ins]
  constructor
  · rintro (h1 | ⟨h1, _⟩ | ⟨h1, _⟩)
    · exact h1
    · exact absurd h1 hpw
    · exact absurd h1 hqw
  · exact fun h => Or.inl h

theorem adj_ins_new {H : Graph} {S : Finset ℕ} {w : ℕ} {ψ : ℕ → Prop} {p : ℕ}
    (hH : H ∈ graphs (S.erase w)) (hp : p ∈ S) (hpw : p ≠ w) :
    adj (ins H S w ψ) p w ↔ ψ p := by
  rw [adj_ins]
  constructor
  · rintro (h1 | ⟨h1, _⟩ | ⟨_, _, _, h1⟩)
    · exact absurd rfl (mem_erase.mp (adj_mem hH h1).2.1).1
    · exact absurd h1 hpw
    · exact h1
  · exact fun h1 => Or.inr (Or.inr ⟨rfl, hp, hpw, h1⟩)

theorem adj_ins_self {H : Graph} {S : Finset ℕ} {w : ℕ} {ψ : ℕ → Prop} {q : ℕ}
    (hH : H ∈ graphs (S.erase w)) (hq : q ∈ S) (hqw : q ≠ w) :
    adj (ins H S w ψ) w q ↔ ψ q := by
  rw [adj_comm]; exact adj_ins_new hH hq hqw

/-- The row of a marked vertex after insertion. -/
theorem ins_row_marked {S : Finset ℕ} {i w : ℕ} {φ ψ : ℕ → Prop} {H : Graph}
    (hH : H ∈ graphs (S.erase w)) (hrow : ∀ q ∈ S.erase w, (adj H i q ↔ φ q))
    (hi : i ∈ S) (hwi : w ≠ i) (hψi : ψ i ↔ φ w) :
    ∀ q ∈ S, (adj (ins H S w ψ) i q ↔ φ q) := by
  intro q hq
  by_cases hqw : q = w
  · rw [hqw, adj_ins_new hH hi (Ne.symm hwi)]; exact hψi
  · rw [adj_ins_of_ne (Ne.symm hwi) hqw]
    exact hrow q (mem_erase.mpr ⟨hqw, hq⟩)

theorem Cls.ins {S : Finset ℕ} {i j w : ℕ} {φi φj ψ : ℕ → Prop} {H : Graph}
    (hH : H ∈ graphs (S.erase w)) (h : Cls (S.erase w) i j φi φj H)
    (hi : i ∈ S) (hj : j ∈ S) (hwi : w ≠ i) (hwj : w ≠ j)
    (hψi : ψ i ↔ φi w) (hψj : ψ j ↔ φj w)
    (hcons : Consistent S (ins H S w ψ)) : Cls S i j φi φj (ins H S w ψ) :=
  ⟨hcons, ins_row_marked hH h.rowi hi hwi hψi, ins_row_marked hH h.rowj hj hwj hψj⟩

/-- Deletion bijection for classes with two prescribed rows. -/
theorem cls_del_card {S : Finset ℕ} {i j w : ℕ} {φi φj : ℕ → Prop} (ψ : ℕ → Prop)
    (cond : Graph → Prop)
    (hi : i ∈ S) (hj : j ∈ S) (hw : w ∈ S) (hwi : w ≠ i) (hwj : w ≠ j)
    (hψi : ψ i ↔ φi w) (hψj : ψ j ↔ φj w)
    (hforced : ∀ G ∈ graphs S, Cls S i j φi φj G → cond G →
      ∀ q ∈ S, q ≠ w → (adj G w q ↔ ψ q))
    (hins : ∀ H ∈ graphs (S.erase w), Cls (S.erase w) i j φi φj H →
      Consistent S (ins H S w ψ) ∧ cond (ins H S w ψ)) :
    (sel S fun G => Cls S i j φi φj G ∧ cond G).card
      = (clsSet (S.erase w) i j φi φj).card := by
  unfold clsSet
  apply card_del_eq hw _ _ ψ
  · rintro G hG ⟨hc, hcond⟩
    exact ⟨hc.del hwi hwj, hforced G hG hc hcond⟩
  · intro H hH hc
    obtain ⟨h1, h2⟩ := hins H hH hc
    exact ⟨Cls.ins hH hc hi hj hwi hwj hψi hψj h1, h2⟩

/-! ### Rows of an inserted graph -/

theorem mono_ins_self {S : Finset ℕ} {w : ℕ} {ψ : ℕ → Prop} {H : Graph}
    (hH : H ∈ graphs (S.erase w)) (hψ : MonoP S w ψ) :
    MonoP S w (adj (ins H S w ψ) w) :=
  hψ.congr fun _ hq hqw => adj_ins_self hH hq hqw

theorem mono_ins_marked {S : Finset ℕ} {i w : ℕ} {φ ψ : ℕ → Prop} {H : Graph}
    (hH : H ∈ graphs (S.erase w)) (hrow : ∀ q ∈ S.erase w, (adj H i q ↔ φ q))
    (hi : i ∈ S) (hwi : w ≠ i) (hψi : ψ i ↔ φ w) (hφ : MonoP S i φ) :
    MonoP S i (adj (ins H S w ψ) i) :=
  hφ.congr fun q hq _ => ins_row_marked hH hrow hi hwi hψi q hq

theorem mono_ins_clone {S : Finset ℕ} {w p t : ℕ} {ψ : ℕ → Prop} {H : Graph}
    (hH : H ∈ graphs (S.erase w)) (hp : p ∈ S) (hpw : p ≠ w)
    (ht : t ∈ S) (htw : t ≠ w) (htp : t ≠ p)
    (hord : ∀ q ∈ S, q ≠ w → q ≠ t → (q < w ↔ q < t))
    (hbit : ψ p ↔ adj H p t)
    (h : MonoP (S.erase w) p (adj H p)) : MonoP S p (adj (ins H S w ψ) p) := by
  refine monoP_clone ht htw htp hord ?_ ?_ h
  · intro q _ hqw
    exact adj_ins_of_ne hpw hqw
  · rw [adj_ins_new hH hp hpw]; exact hbit

/-- Consistency of an inserted graph when the new vertex is a clone of the marked vertex `i`
(outside the marked rows). -/
theorem cons_ins_clone_i {S : Finset ℕ} {i j w : ℕ} {φi φj ψ : ℕ → Prop} {H : Graph}
    (hH : H ∈ graphs (S.erase w)) (hc : Cls (S.erase w) i j φi φj H)
    (hi : i ∈ S) (hj : j ∈ S) (hwi : w ≠ i) (hwj : w ≠ j)
    (hψi : ψ i ↔ φi w) (hψj : ψ j ↔ φj w)
    (hmi : MonoP S i φi) (hmj : MonoP S j φj) (hmw : MonoP S w ψ)
    (hord : ∀ q ∈ S, q ≠ w → q ≠ i → (q < w ↔ q < i))
    (hbit : ∀ p ∈ S, p ≠ w → p ≠ i → p ≠ j → (ψ p ↔ φi p)) :
    Consistent S (ins H S w ψ) := by
  intro p hp
  by_cases hpw : p = w
  · rw [hpw]; exact mono_ins_self hH hmw
  by_cases hpi : p = i
  · rw [hpi]; exact mono_ins_marked hH hc.rowi hi hwi hψi hmi
  by_cases hpj : p = j
  · rw [hpj]; exact mono_ins_marked hH hc.rowj hj hwj hψj hmj
  have hpe : p ∈ S.erase w := mem_erase.mpr ⟨hpw, hp⟩
  refine mono_ins_clone hH hp hpw hi (Ne.symm hwi) (Ne.symm hpi) hord ?_ (hc.cons p hpe)
  rw [hbit p hp hpw hpi hpj, adj_comm]
  exact (hc.rowi p hpe).symm

/-- The same with a clone of the marked vertex `j`. -/
theorem cons_ins_clone_j {S : Finset ℕ} {i j w : ℕ} {φi φj ψ : ℕ → Prop} {H : Graph}
    (hH : H ∈ graphs (S.erase w)) (hc : Cls (S.erase w) i j φi φj H)
    (hi : i ∈ S) (hj : j ∈ S) (hwi : w ≠ i) (hwj : w ≠ j)
    (hψi : ψ i ↔ φi w) (hψj : ψ j ↔ φj w)
    (hmi : MonoP S i φi) (hmj : MonoP S j φj) (hmw : MonoP S w ψ)
    (hord : ∀ q ∈ S, q ≠ w → q ≠ j → (q < w ↔ q < j))
    (hbit : ∀ p ∈ S, p ≠ w → p ≠ i → p ≠ j → (ψ p ↔ φj p)) :
    Consistent S (ins H S w ψ) := by
  intro p hp
  by_cases hpw : p = w
  · rw [hpw]; exact mono_ins_self hH hmw
  by_cases hpi : p = i
  · rw [hpi]; exact mono_ins_marked hH hc.rowi hi hwi hψi hmi
  by_cases hpj : p = j
  · rw [hpj]; exact mono_ins_marked hH hc.rowj hj hwj hψj hmj
  have hpe : p ∈ S.erase w := mem_erase.mpr ⟨hpw, hp⟩
  refine mono_ins_clone hH hp hpw hj (Ne.symm hwj) (Ne.symm hpj) hord ?_ (hc.cons p hpe)
  rw [hbit p hp hpw hpi hpj, adj_comm]
  exact (hc.rowj p hpe).symm

/-! ### Reading patterns off a class -/

/-- No `1 0 1` in the row of `p`. -/
theorem Cls.no101 {S : Finset ℕ} {i j : ℕ} {φi φj : ℕ → Prop} {G : Graph}
    (h : Cls S i j φi φj G) {p x y z : ℕ} (hp : p ∈ S)
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxp : x ≠ p) (hyp : y ≠ p) (hzp : z ≠ p)
    (hxy : x < y) (hyz : y < z) (hax : adj G p x) (haz : adj G p z) : adj G p y :=
  (h.cons p hp).no101 hx hy hz hxp hyp hzp hxy hyz hax haz

/-- No `0 1 0` in the row of `p`. -/
theorem Cls.no010 {S : Finset ℕ} {i j : ℕ} {φi φj : ℕ → Prop} {G : Graph}
    (h : Cls S i j φi φj G) {p x y z : ℕ} (hp : p ∈ S)
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxp : x ≠ p) (hyp : y ≠ p) (hzp : z ≠ p)
    (hxy : x < y) (hyz : y < z) (hay : adj G p y) : adj G p x ∨ adj G p z :=
  (h.cons p hp).no010 hx hy hz hxp hyp hzp hxy hyz hay

/-- Adjacency to the marked vertex `i`, read from the other side. -/
theorem Cls.adj_i {S : Finset ℕ} {i j : ℕ} {φi φj : ℕ → Prop} {G : Graph}
    (h : Cls S i j φi φj G) {p : ℕ} (hp : p ∈ S) : adj G p i ↔ φi p := by
  rw [adj_comm]; exact h.rowi p hp

theorem Cls.adj_j {S : Finset ℕ} {i j : ℕ} {φi φj : ℕ → Prop} {G : Graph}
    (h : Cls S i j φi φj G) {p : ℕ} (hp : p ∈ S) : adj G p j ↔ φj p := by
  rw [adj_comm]; exact h.rowj p hp

/-- A condition that always holds in a class does not change its cardinality. -/
theorem card_of_forall {S : Finset ℕ} (P : Graph → Prop) (c : Graph → Prop)
    (h : ∀ G ∈ graphs S, P G → c G) :
    (sel S P).card = (sel S fun G => P G ∧ c G).card := by
  congr 1
  apply sel_congr
  intro G hG
  exact ⟨fun hP => ⟨hP, h G hG hP⟩, fun hP => hP.1⟩

end

end ZonoFlips
